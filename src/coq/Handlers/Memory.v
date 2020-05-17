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
     Morphisms ZArith List String Omega
     FSets.FMapAVL
     Structures.OrderedTypeEx
     ZMicromega.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     LLVMAst
     Util
     DynamicTypes
     Denotation
     MemoryAddress
     LLVMEvents
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

Require Import Ceres.Ceres.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
  Definition t := addr.
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
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


Module Make(LLVMEvents: LLVM_INTERACTIONS(A)).
  Import LLVMEvents.
  Import DV.
  Open Scope list.

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

  Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
    fold_left (fun a b => if leq a b then b else a) l def.

  (* Get a fresh key for use in memory map *)
  Definition next_key {a} (m : IM.t a) : Z
    := let keys := map fst (IM.elements m) in
       1 + maximumBy Z.leb (-1) keys.

  Inductive SByte :=
  | Byte : byte -> SByte
  | Ptr : addr -> SByte
  | PtrFrag : SByte
  | SUndef : SByte.

  (* TODO SAZ: mem_block should keep track of its allocation size so
    that operations can fail if they are out of range

    CB: I think this might happen implicitly with make_empty_block --
    it initializes the IntMap with only the valid indices. As long as the
    lookup functions handle this properly, anyway.
   *)

  (* Simple view of memory *)
  Inductive concrete_block :=
  | CBlock (size : Z) (block_id : Z) : concrete_block.

  Inductive logical_block :=
  | LBlock (size : Z) (bytes : IntMap SByte) (concrete_id : option Z) : logical_block.

  Definition mem_block       := IntMap SByte.

  Definition concrete_memory := IntMap concrete_block.
  Definition logical_memory  := IntMap logical_block.
  Definition memory          := (concrete_memory * logical_memory)%type.

  (* Stack frames *)
  Definition mem_frame := list Z.  (* A list of block ids that need to be freed when popped *)
  Definition mem_stack := list mem_frame.

  (* Memory + stack for freeing *)
  Definition memory_stack : Type := memory * mem_stack.

  Definition empty_memory_stack : memory_stack := ((empty, empty), [[]]).

  Fixpoint max_default (l:list Z) (x:Z) :=
    match l with
    | [] => x
    | h :: tl =>
      max_default tl (if h >? x then h else x)
    end.

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

  (* CB TODO: Is interpreting everything except for bytes as undef reasonable? *)
  Definition Sbyte_to_byte (sb:SByte) : option byte :=
    match sb with
    | Byte b => ret b
    | Ptr _ | PtrFrag | SUndef => None
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

  (* CB TODO: does this really not exist somewhere? *)
  Definition is_some {A} (o : option A) :=
    match o with
    | Some x => true
    | None => false
    end.

  Definition all_not_sundef (bytes : list SByte) : bool :=
    forallb is_some (map Sbyte_to_byte bytes).

  (* Deserialize a list of SBytes into a uvalue, assuming that none of the bytes are undef *)
  Fixpoint deserialize_sbytes_defined (bytes:list SByte) (t:dtyp) : uvalue :=
    match t with
    | DTYPE_I sz =>
      let des_int := sbyte_list_to_Z bytes in
      match sz with
      | 1  => UVALUE_I1 (repr des_int)
      | 8  => UVALUE_I8 (repr des_int)
      | 32 => UVALUE_I32 (repr des_int)
      | 64 => UVALUE_I64 (repr des_int)
      | _  => UVALUE_None (* invalid size. *)
      end
    | DTYPE_Float => UVALUE_Float (Float32.of_bits (repr (sbyte_list_to_Z bytes)))
    | DTYPE_Double => UVALUE_Double (Float.of_bits (repr (sbyte_list_to_Z bytes)))

    | DTYPE_Pointer =>
      match bytes with
      | Ptr addr :: tl => UVALUE_Addr addr
      | _ => UVALUE_None (* invalid pointer. *)
      end
    | DTYPE_Array sz t' =>
      let fix array_parse count byte_sz bytes :=
          match count with
          | O => []
          | S n => (deserialize_sbytes_defined (firstn byte_sz bytes) t')
                     :: array_parse n byte_sz (skipn byte_sz bytes)
          end in
      UVALUE_Array (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_dtyp t')) bytes)
    | DTYPE_Struct fields =>
      let fix struct_parse typ_list bytes :=
          match typ_list with
          | [] => []
          | t :: tl =>
            let size_ty := Z.to_nat (sizeof_dtyp t) in
            (deserialize_sbytes_defined (firstn size_ty bytes) t)
              :: struct_parse tl (skipn size_ty bytes)
          end in
      UVALUE_Struct (struct_parse fields bytes)
    | _ => UVALUE_None (* TODO add more as serialization support increases *)
    end.

  Definition deserialize_sbytes (bytes : list SByte) (t : dtyp) : uvalue :=
    if all_not_sundef bytes
    then deserialize_sbytes_defined bytes t
    else UVALUE_Undef t.

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
  Definition make_empty_mem_block (ty:dtyp) : mem_block :=
    init_block (sizeof_dtyp ty).

  Definition make_empty_block (ty:dtyp) : logical_block :=
    let block := make_empty_mem_block ty in
    LBlock (sizeof_dtyp ty) block None.

  Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): err Z :=
    match vs with
    | v :: vs' =>
      match v with
      | DVALUE_I32 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
        | DTYPE_Struct ts
        | DTYPE_Packed_struct ts => (* Handle these differently in future *)
          let offset := fold_left (fun acc t => acc + sizeof_dtyp t)
                                  (firstn n ts) 0 in
          match nth_error ts n with
          | None => failwith "overflow"
          | Some t' =>
            handle_gep_h t' (off + offset) vs'
          end
        | _ => failwith ("non-i32-indexable type")
        end
      | DVALUE_I8 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                              handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
        | _ => failwith ("non-i8-indexable type")
        end
      | DVALUE_I64 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
        | _ => failwith ("non-i64-indexable type")
        end
      | _ => failwith "non-I32 index"
      end
    | [] => ret off
    end.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
      match dv with
      | DVALUE_Addr (b, o) =>
        off <- handle_gep_h t (o + (sizeof_dtyp t) * (unsigned i)) vs' ;;
        ret (DVALUE_Addr (b, off))
      | _ => failwith "non-address"
      end
    | DVALUE_I64 i :: vs' =>
      match dv with
      | DVALUE_Addr (b, o) =>
        off <- handle_gep_h t (o + (sizeof_dtyp t) * (unsigned i)) vs' ;;
        ret (DVALUE_Addr (b, off))
      | _ => failwith "non-address"
      end
    | _ => failwith "non-I32 index"
    end.


  Definition lookup_concrete (b : Z) (m : memory) : option concrete_block :=
    let concrete_map := fst m in
    lookup b concrete_map.

  Definition lookup_logical (b : Z) (m : memory) : option logical_block :=
    let logical_map := snd m in
    lookup b logical_map.

  (* Get next key in logical map *)
  Definition next_logical_key (m : memory) : Z :=
    next_key (snd m).


  (* Get next key in concrete map *)
  Definition next_concrete_key (m : memory) : Z :=
    let concrete_map := fst m in
    let keys         := List.map fst (IM.elements concrete_map) in
    let max          := max_default keys 0 in
    let offset       := 1 in (* TODO: This should be "random" *)
    match lookup_concrete max m with
    | None => offset
    | Some (CBlock sz _) => max + sz + offset
    end.

  Definition add_concrete (id : Z) (b : concrete_block) (m : memory) : memory :=
    match m with
    | (cm, lm) =>
      (add id b cm, lm)
    end.

  Definition add_logical (id : Z) (b : logical_block) (m : memory) : memory :=
    match m with
    | (cm, lm) =>
      (cm, add id b lm)
    end.

  Definition concretize_block (b:Z) (m:memory) : Z * memory :=
    match lookup_logical b m with
    | None => (b, m) (* TODO: Not sure this makes sense ??? *)
    | Some (LBlock sz bytes (Some cid)) => (cid, m)
    | Some (LBlock sz bytes None) =>
      (* Allocate a concrete block for this one *)
      let id        := next_concrete_key m in
      let new_block := CBlock sz b in
      let m'        := add_concrete id new_block m in
      let m''       := add_logical  b (LBlock sz bytes (Some id)) m' in
      (id, m'')
    end.

  (* LLVM 5.0 memcpy
   According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
   this operation can never fail?  It doesn't return any status code...
   *)

  (* TODO probably doesn't handle sizes correctly... *)
  Definition handle_memcpy (args : List.list dvalue) (m:memory) : err memory :=
    match args with
    | DVALUE_Addr (dst_b, dst_o) ::
      DVALUE_Addr (src_b, src_o) ::
      DVALUE_I32 len ::
      DVALUE_I32 align :: (* alignment ignored *)
      DVALUE_I1 volatile :: [] (* volatile ignored *)  =>

      src_block <- trywith "memcpy src block not found" (lookup_logical src_b m) ;;
      dst_block <- trywith "memcpy dst block not found" (lookup_logical dst_b m) ;;

      let src_bytes
          := match src_block with
             | LBlock size bytes concrete_id => bytes
             end in
      let '(dst_sz, dst_bytes, dst_cid)
          := match dst_block with
             | LBlock size bytes concrete_id => (size, bytes, concrete_id)
             end in
      let sdata := lookup_all_index src_o (unsigned len) src_bytes SUndef in
      let dst_bytes' := add_all_index sdata dst_o dst_bytes in
      let dst_block' := LBlock dst_sz dst_bytes' dst_cid in
      let m' := add_logical dst_b dst_block' m in
      (ret m' : err memory)
    | _ => failwith "memcpy got incorrect arguments"
    end.

  (* TODO:
   - we can use the handler combinators to make these more modular

   - these operations are too defined: load and store should fail if the
     address isn't in range
   *)

  Definition free_concrete_of_logical
             (b : Z)
             (lm : logical_memory)
             (cm : concrete_memory) : concrete_memory
    := match lookup b lm with
       | None => cm
       | Some (LBlock _ _ None) => cm
       | Some (LBlock _ _ (Some cid)) => delete cid cm
       end.

  Definition free_frame (f : mem_frame) (m : memory) : memory
    := match m with
       | (cm, lm) =>
         let cm' := fold_left (fun m key => free_concrete_of_logical key lm m) f cm in
         (cm', fold_left (fun m key => delete key m) f lm)
       end.

  (* Get the cid stored in the memory map *)
  Definition get_real_cid (cid : Z) (m : memory) : option (Z * concrete_block)
    := IM.fold (fun k '(CBlock sz bid) a => if (k <=? cid) && (cid <? k + sz)
                                         then Some (k, CBlock sz bid)
                                         else a) (fst m) None.

  (* Convert a concrete address to a block and offset *)
  Definition concrete_address_to_logical (cid : Z) (m : memory) : option (Z * Z)
    := match m with
       | (cm, lm) =>
         '(rid, CBlock sz bid) <- get_real_cid cid m ;;
          ret (bid, cid-rid)
       end.

  Definition handle_memory {E} `{FailureE -< E} `{UBE -< E}: MemoryE ~> stateT memory_stack (itree E) :=
    fun _ e '(m, s) =>
      match e with
      | MemPush => ret ((m, [] :: s), tt)

      | MemPop =>
        match s with
        | [] => raise "Tried to pop memory stack, but there's nothing to pop."
        | frame :: stack_rest =>
          let m' := free_frame frame m in
          ret ((m', stack_rest), tt)
        end

      | Alloca t =>
        let new_block := make_empty_block t in
        let key := next_logical_key m in
        let new_mem := add_logical key new_block m in

        match s with
        | [] => raise "No stack frame for alloca."
        | frame :: stack_rest =>
          let new_stack := (key :: frame) :: stack_rest in
          ret ((new_mem, new_stack), DVALUE_Addr (key, 0))
        end

      | Load t dv =>
        match dv with
        | DVALUE_Addr (b, i) =>
          match lookup_logical b m with
          | Some (LBlock _ block _) =>
            ret ((m, s), deserialize_sbytes (lookup_all_index i (sizeof_dtyp t) block SUndef) t)
          (* Asking for a non-allocated block is undefined behaviour. *)
          | None => raiseUB "Loading from block that has never been allocated."
          end
        | _ => raise "Load got non-address dvalue"
        end

      | Store dv v =>
        match dv with
        | DVALUE_Addr (b, i) =>
          match lookup_logical b m with
          | Some (LBlock sz bytes cid) =>
            let bytes' := add_all_index (serialize_dvalue v) i bytes in
            let block' := LBlock sz bytes' cid in
            ret ((add_logical b block' m, s), tt)
          | None => raise "stored to unallocated address"
          end
        | _ => raise ("Store got non-address dvalue: " ++ (to_string dv))
        end

      | GEP t dv vs =>
        match handle_gep t dv vs with
        | inl err => raise err
        | inr dv => ret ((m, s), dv)
        end

      | ItoP x =>
        match x with
        | DVALUE_I64 i =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise ("Invalid concrete address " ++ (to_string x))
          | Some (b, o) => ret ((m, s), DVALUE_Addr (b, o))
          end
        | DVALUE_I32 i =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address "
          | Some (b, o) => ret ((m, s), DVALUE_Addr (b, o))
          end
        | DVALUE_I8 i  =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address"
          | Some (b, o) => ret ((m, s), DVALUE_Addr (b, o))
          end
        | DVALUE_I1 i  =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address"
          | Some (b, o) => ret ((m, s), DVALUE_Addr (b, o))
          end
        | _            => raise "Non integer passed to ItoP"
        end

      (* TODO take integer size into account *)
      | PtoI t a =>
        match a, t with
        | DVALUE_Addr (b, i), DTYPE_I sz =>
          let (cid, m') := concretize_block b m in
          'addr <- lift_undef_or_err ret (coerce_integer_to_int sz (cid+i)) ;;
           ret ((m', s), addr)
        | _, _ => raise "PtoI type error."
        end
      end.

  Definition handle_intrinsic {E} `{FailureE -< E} `{PickE -< E}: IntrinsicE ~> stateT memory_stack (itree E) :=
    fun _ e '(m, s) =>
      match e with
      | Intrinsic t name args =>
        (* Pick all arguments, they should all be unique. *)
        if string_dec name "llvm.memcpy.p0i8.p0i8.i32" then  (* FIXME: use reldec typeclass? *)
          match handle_memcpy args m with
          | inl err => raise err
          | inr m' => ret ((m', s), DVALUE_None)
          end
        else
          raise ("Unknown intrinsic: " ++ name)
      end.


  (* TODO: clean this up *)
  (* {E} `{failureE -< E} : IO ~> stateT memory (itree E)  *)
  (* Won't need to be case analysis, just passes through failure + debug *)
  (* Might get rid of this one *)
  (* This can't show that IO ∉ E :( *)
  (* Alternative 2: Fix order of effects

   Layer interpretors so that they each chain into the next. Have to
   do ugly matches everywhere :(.

   Split the difference:

   `{IO -< IO +' failureE +' debugE}

   Alternative 3: follow 2, and then use notations to make things better.

   Alternative 4: Extend itrees mechanisms with some kind of set operations.

   If you want to allow sums on the left of your handlers, you want
   this notion of an atomic handler / event, which is different from a
   variable or a sum...

   `{E +' F -< G}

   This seems too experimental to try to work out now --- chat with Li-yao about it.

   Alternative 2 might be the most straightforward way to get things working in the short term.

   We just want to get everything hooked together to build and test
   it. Then think about making the interfaces nicer. The steps to alt
   2, start with LLVM1 ordering as the basic default. Then each stage
   of interpretation peels off one, or reintroduces the same kind of
   events / changes it.


   *)
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_memory_h := case_ E_trigger (case_ handle_intrinsic  (case_ handle_memory  F_trigger)).
    Definition interp_memory :
      itree Effin ~> stateT memory_stack (itree Effout) :=
      interp_state interp_memory_h.

    Section Structural_Lemmas.
      
      Lemma interp_memory_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) m,
          interp_memory (ITree.bind t k) m ≅
                        ITree.bind (interp_memory t m) (fun '(m',r) => interp_memory (k r) m').
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inv EQ; reflexivity.
      Qed.

      Lemma interp_memory_ret :
        forall (R : Type) g (x: R),
          interp_memory (Ret x: itree Effin R) g ≅ Ret (g,x).
      Proof.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_memory_vis_eqit:
        forall S X (kk : X -> itree Effin S) m
          (e : Effin X),
          interp_memory (Vis e kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_vis:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (Vis e kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_memory_trigger:
        forall (m : memory_stack) X (e : Effin X),
          interp_memory (ITree.trigger e) m ≈ interp_memory_h e m. 
      Proof.
        intros.
        unfold interp_memory.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger_eqit:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger:
        forall m S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Global Instance eutt_interp_memory {R} :
        Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_memory R). 
      Proof.
        repeat intro.
        unfold interp_memory. 
        subst; rewrite H2.
        reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Make.
