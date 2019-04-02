(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


From Coq Require Import
     ZArith List String Omega
     FSets.FMapAVL
     Structures.OrderedTypeEx
     ZMicromega.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.


From Vellvm Require Import 
     LLVMAst
     Util
     StepSemantics 
     MemoryAddress
     LLVMIO
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
  Definition t := addr.
  Lemma addr_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (a1 ~=? b1); 
      destruct (a2 ~=? b2); unfold eqv in *; unfold AstLib.eqv_int in *; subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.      
  Qed.
End A.


Module Make(LLVMIO: LLVM_INTERACTIONS(A)).
  Import LLVMIO.
  Import DV.
  
Definition addr := A.addr.

Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Definition IntMap := IM.t.

Definition add {a} k (v:a) := IM.add k v.
Definition delete {a} k (m:IntMap a) := IM.remove k m.
Definition member {a} k (m:IntMap a) := IM.mem k m.
Definition lookup {a} k (m:IntMap a) := IM.find k m.
Definition empty {a} := @IM.empty a.

Fixpoint add_all {a} ks (m:IntMap a) :=
  match ks with
  | [] => m
  | (k,v) :: tl => add k v (add_all tl m)
  end.

Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
  match vs with
  | [] => m
  | v :: tl => add i v (add_all_index tl (i+1) m)
  end.

(* Give back a list of values from i to (i + sz) - 1 in m. *)
(* Uses def as the default value if a lookup failed. *)
Definition lookup_all_index {a} (i:Z) (sz:Z) (m:IntMap a) (def:a) : list a :=
  List.map (fun x =>
         let x' := lookup (Z.of_nat x) m in
         match x' with
         | None => def
         | Some val => val
         end) (seq (Z.to_nat i) (Z.to_nat sz)).

Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with | Some x => Some x | None => my end) m1 m2.

Definition size {a} (m : IM.t a) : Z := Z.of_nat (IM.cardinal m).

Inductive SByte :=
| Byte : byte -> SByte
| Ptr : addr -> SByte
| PtrFrag : SByte
| SUndef : SByte.

(* TODO SAZ: 
    mem_block should keep track of its allocation size so that operations
    can fail if they are out of range
*)
Definition mem_block := IntMap SByte.
Definition memory := IntMap mem_block.
Definition undef := DVALUE_Undef. (* TODO: should this be an empty block? *)

Fixpoint max_default (l:list Z) (x:Z) :=
  match l with
  | [] => x
  | h :: tl =>
    max_default tl (if h >? x then h else x)
  end.

Definition oracle (m:memory) : Z :=
  let keys := List.map fst (IM.elements m) in
  let max := max_default keys 0 in
  let offset := 1 in (* TODO: This should be "random" *)
  max + offset.


(* Computes the byte size of this type. *)
Fixpoint sizeof_dtyp (ty:dtyp) : Z :=
  match ty with
  | DTYPE_I sz => 8 (* All integers are padded to 8 bytes. *)
  | DTYPE_Pointer => 8
  | DTYPE_Struct l => fold_left (fun x acc => x + sizeof_dtyp acc) l 0
  | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
  | DTYPE_Float => 4
  | DTYPE_Double => 8
  | _ => 0 (* TODO: add support for more types as necessary *)
  end.

(* Convert integer to its byte representation. *)
Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition Z_to_sbyte_list (count:nat) (z:Z) : list SByte :=
  List.map Byte (bytes_of_int count z).

Definition Sbyte_to_byte_list (sb:SByte) : list byte :=
  match sb with
  | Byte b => [b]
  | Ptr _ | PtrFrag | SUndef => []
  end.

Definition sbyte_list_to_byte_list (bytes:list SByte) : list byte :=
  List.flat_map Sbyte_to_byte_list bytes.

Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
  int_of_bytes (sbyte_list_to_byte_list bytes).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, List.length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
Opaque Byte.wordsize.
  rewrite Nat2Z.inj_succ. simpl.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega.
  rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
  rewrite Byte.Z_mod_modulus_eq. reflexivity.
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.



(* Serializes a dvalue into its SByte-sensitive form. *)
Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
  match dval with
  | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
  | DVALUE_I1 i => Z_to_sbyte_list 8 (unsigned i)
  | DVALUE_I8 i => Z_to_sbyte_list 8 (unsigned i)
  | DVALUE_I32 i => Z_to_sbyte_list 8 (unsigned i)
  | DVALUE_I64 i => Z_to_sbyte_list 8 (unsigned i)
  | DVALUE_Float f => Z_to_sbyte_list 4 (unsigned (Float32.to_bits f))
  | DVALUE_Double d => Z_to_sbyte_list 8 (unsigned (Float.to_bits d))
  | DVALUE_Struct fields | DVALUE_Array fields =>
      (* note the _right_ fold is necessary for byte ordering. *)
      fold_right (fun 'dv acc => ((serialize_dvalue dv) ++ acc) % list) [] fields
  | _ => [] (* TODO add more dvalues as necessary *)
  end.

(* Deserialize a list of SBytes into a dvalue. *)
Fixpoint deserialize_sbytes (bytes:list SByte) (t:dtyp) : dvalue :=
  match t with
  | DTYPE_I sz =>
    let des_int := sbyte_list_to_Z bytes in
    match sz with
    | 1 => DVALUE_I1 (repr des_int)
    | 8 => DVALUE_I8 (repr des_int)
    | 32 => DVALUE_I32 (repr des_int)
    | 64 => DVALUE_I64 (repr des_int)
    | _ => DVALUE_None (* invalid size. *)
    end
  | DTYPE_Float => DVALUE_Float (Float32.of_bits (repr (sbyte_list_to_Z bytes)))
  | DTYPE_Double => DVALUE_Double (Float.of_bits (repr (sbyte_list_to_Z bytes)))
      
  | DTYPE_Pointer =>
    match bytes with
    | Ptr addr :: tl => DVALUE_Addr addr
    | _ => DVALUE_None (* invalid pointer. *)
    end
  | DTYPE_Array sz t' =>
    let fix array_parse count byte_sz bytes :=
        match count with
        | O => []
        | S n => (deserialize_sbytes (firstn byte_sz bytes) t')
                   :: array_parse n byte_sz (skipn byte_sz bytes)
        end in
    DVALUE_Array (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_dtyp t')) bytes)
  | DTYPE_Struct fields =>
    let fix struct_parse typ_list bytes :=
        match typ_list with
        | [] => []
        | t :: tl =>
          let size_ty := Z.to_nat (sizeof_dtyp t) in
          (deserialize_sbytes (firstn size_ty bytes) t)
            :: struct_parse tl (skipn size_ty bytes)
        end in
    DVALUE_Struct (struct_parse fields bytes)
  | _ => DVALUE_None (* TODO add more as serialization support increases *)
  end.

(* Todo - complete proofs, and think about moving to MemoryProp module. *)
(* The relation defining serializable dvalues. *)
Inductive serialize_defined : dvalue -> Prop :=
  | d_addr: forall addr,
      serialize_defined (DVALUE_Addr addr)
  | d_i1: forall i1,
      serialize_defined (DVALUE_I1 i1)
  | d_i8: forall i1,
      serialize_defined (DVALUE_I8 i1)
  | d_i32: forall i32,
      serialize_defined (DVALUE_I32 i32)
  | d_i64: forall i64,
      serialize_defined (DVALUE_I64 i64)
  | d_struct_empty:
      serialize_defined (DVALUE_Struct [])
  | d_struct_nonempty: forall dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Struct fields_list) ->
      serialize_defined (DVALUE_Struct (dval :: fields_list))
  | d_array_empty:
      serialize_defined (DVALUE_Array [])
  | d_array_nonempty: forall dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Array fields_list) ->
      serialize_defined (DVALUE_Array (dval :: fields_list)).

(* Lemma assumes all integers encoded with 8 bytes. *)

Inductive sbyte_list_wf : list SByte -> Prop :=
| wf_nil : sbyte_list_wf []
| wf_cons : forall b l, sbyte_list_wf l -> sbyte_list_wf (Byte b :: l)
.                                                   

(*
Lemma sbyte_list_to_Z_inverse:
  forall i1 : int1, (sbyte_list_to_Z (Z_to_sbyte_list 8 (Int1.unsigned i1))) = 
               (Int1.unsigned i1).
Proof.
  intros i1.
  destruct i1. simpl.
Admitted. *)


(*
Lemma serialize_inverses : forall dval,
    serialize_defined dval -> exists typ, deserialize_sbytes (serialize_dvalue dval) typ = dval.
Proof.
  intros. destruct H.
  (* DVALUE_Addr. Type of pointer is not important. *)
  - exists (TYPE_Pointer TYPE_Void). reflexivity.
  (* DVALUE_I1. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 1).
    simpl. 
      

    admit.
  (* DVALUE_I32. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 32). admit.
  (* DVALUE_I64. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 64). admit.
  (* DVALUE_Struct [] *)
  - exists (TYPE_Struct []). reflexivity.
  (* DVALUE_Struct fields *)
  - admit.
  (* DVALUE_Array [] *)
  - exists (TYPE_Array 0 TYPE_Void). reflexivity.
  (* DVALUE_Array fields *)
  - admit.
Admitted.
*)

(* Construct block indexed from 0 to n. *)
Fixpoint init_block_h (n:nat) (m:mem_block) : mem_block :=
  match n with
  | O => add 0 SUndef m
  | S n' => add (Z.of_nat n) SUndef (init_block_h n' m)
  end.

(* Initializes a block of n 0-bytes. *)
Definition init_block (n:Z) : mem_block :=
  match n with
  | 0 => empty
  | Z.pos n' => init_block_h (BinPosDef.Pos.to_nat (n' - 1)) empty
  | Z.neg _ => empty (* invalid argument *)
  end.

(* Makes a block appropriately sized for the given type. *)
Definition make_empty_block (ty:dtyp) : mem_block :=
  init_block (sizeof_dtyp ty).

Fixpoint handle_gep_h (t:dtyp) (b:Z) (off:Z) (vs:list dvalue) (m:memory) : err (memory * dvalue):=
  match vs with
  | v :: vs' =>
    match v with
    | DVALUE_I32 i =>
      let k := unsigned i in
      let n := BinIntDef.Z.to_nat k in
      match t with
      | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                           handle_gep_h ta b (off + k * (sizeof_dtyp ta)) vs' m
      | DTYPE_Struct ts | DTYPE_Packed_struct ts => (* Handle these differently in future *)
        let offset := fold_left (fun acc t => acc + sizeof_dtyp t)
                                (firstn n ts) 0 in
        match nth_error ts n with
        | None => raise "overflow"
        | Some t' =>
          handle_gep_h t' b (off + offset) vs' m
        end
      | _ => raise ("non-i32-indexable type")
      end
    | DVALUE_I8 i =>
      let k := unsigned i in
      let n := BinIntDef.Z.to_nat k in
      match t with
      | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                           handle_gep_h ta b (off + k * (sizeof_dtyp ta)) vs' m
      | _ => raise ("non-i8-indexable type")
      end
    | DVALUE_I64 i =>
      let k := unsigned i in
      let n := BinIntDef.Z.to_nat k in
      match t with
      | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                           handle_gep_h ta b (off + k * (sizeof_dtyp ta)) vs' m
      | _ => raise ("non-i64-indexable type")
      end
    | _ => raise "non-I32 index"
    end
  | [] => ret (m, DVALUE_Addr (b, off))
  end.


Definition concretize_block (b:Z) (m:memory) : Z * memory :=
  match lookup b m with
  | None => (b, m)
  | Some block =>
    let i := oracle m in
    let fix loop es k block : mem_block :=
        match es with
        | [] => block
        | (i, e) :: tl => loop tl (k+1) (add (k + i) e block)
        end in
    (* TODO change source block SBYTES to associate abstract pointers with concrete memory. *)
    (i, add b (loop (IM.elements block) i block) m)
  end.

Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) (m:memory) : err (memory * dvalue):=
  match vs with
  | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 indices *)
    match dv with
    | DVALUE_Addr (b, o) =>
      handle_gep_h t b (o + (sizeof_dtyp t) * (unsigned i)) vs' m
    | _ => raise "non-address" 
    end
  | _ => raise "non-I32 index"
  end.

(* LLVM 5.0 memcpy 
   According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
   this operation can never fail?  It doesn't return any status code... 
 *)

Definition handle_memcpy (args : List.list dvalue) (m:memory) : err memory :=
  match args with
  | DVALUE_Addr (dst_b, dst_o) ::
                DVALUE_Addr (src_b, src_o) ::
                DVALUE_I32 len ::
                DVALUE_I32 align :: (* alignment ignored *)
                DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
    src_block <- trywith "memcpy src block not found" (lookup src_b m) ;;
    dst_block <- trywith "memcpy dst block not found" (lookup dst_b m) ;;
    let sdata := lookup_all_index src_o (unsigned len) src_block SUndef in
    let dst_block' := add_all_index sdata dst_o dst_block in
    let m' := add dst_b dst_block' m in
    (ret m' : err memory)
              
  | _ => raise "memcpy got incorrect arguments"
  end.


(* TODO:
   - we can use the handler combinators to make these more modular

   - these operations are too defined: load and store should fail if the 
     address isn't in range
*)


Definition handle_mem {X} : (IO X) -> memory -> (LLVM (failureE +' debugE)) (memory * X)%type :=
  fun e m =>
    match e with
    | Alloca t =>
      let new_block := make_empty_block t in
      ret (add (size m) new_block m,
           DVALUE_Addr (size m, 0))
          
    | Load t dv =>
        match dv with
        | DVALUE_Addr (b, i) =>
          ret match lookup b m with
              | Some block =>
                (m, deserialize_sbytes (lookup_all_index i (sizeof_dtyp t) block SUndef) t)
              | None => (m, DVALUE_Undef)
              end
        | _ => raise "Load got non-address dvalue"
        end

    | Store dv v => 
      match dv with
      | DVALUE_Addr (b, i) =>
        match lookup b m with
        | Some m' =>
          ret (add b (add_all_index (serialize_dvalue v) i m') m, tt) 
        | None => raise "stored to unallocated address"
        end
      | _ => raise "Store got non-address dvalue"
      end

    | GEP t dv vs =>
      match handle_gep t dv vs m with
      | inl err => raise err
      | inr v => ret v
      end

    | ItoP i =>
      match i with
      | DVALUE_I64 i => ret (m, DVALUE_Addr (0, unsigned i))
      | DVALUE_I32 i => ret (m, DVALUE_Addr (0, unsigned i))
      | DVALUE_I8 i => ret (m, DVALUE_Addr (0, unsigned i))
      | DVALUE_I1 i => ret (m, DVALUE_Addr (0, unsigned i))
      | _ => raise "Non integer passed to ItoP"
      end
  
    | PtoI a =>
      match a with
      | DVALUE_Addr (b, i) =>
        if Z.eqb b 0 then ret (m, DVALUE_Addr(0, i))
        else let (k, m) := concretize_block b m in
             ret (m, DVALUE_Addr (0, (k + i)))
      | _ => raise "PtoI got non-address dvalue"
      end

    | Call t f args =>
      if string_dec f "llvm.memcpy.p0i8.p0i8.i32" then  (* FIXME: use reldec typeclass? *)
        match handle_memcpy args m with
        | inl err => raise err
        | inr m' => ret (m', DVALUE_None)
        end
      else            
        vis (Call t f args) (fun x => ret (m, x))
    end.
             


Definition handleMem {X} : (IO +' (failureE +' debugE)) X -> memory -> (LLVM (failureE +' debugE)) (memory * X)%type :=
  fun e m => 
    match e with
    | inl1 io => handle_mem io m
    | inr1 (inl1 (Throw s)) => raise s
    | inr1 (inr1 d) =>
      match d with
      | Debug s => vis (Debug s) (fun _ => ret (m, tt)) (* SAZ: should be able to use lift *)
      end
    end.

Definition memD {X} (m:memory) (d: LLVM (failureE +' debugE) X) : LLVM (failureE +' debugE) (memory * X)%type :=
  interp_state (fun T => @handleMem T) d m.
  
End Make.

