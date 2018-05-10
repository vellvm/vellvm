Require Import ZArith List String Omega.
Require Import Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.LLVMIO.
Require Import FSets.FMapAVL.
Require Import Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
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
    destruct (a1 == b1); 
      destruct (a2 == b2); subst.
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
  map (fun x =>
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

Definition mem_block := IntMap SByte.
Definition memory := IntMap mem_block.
Definition undef := DVALUE_Undef. (* TODO: should this be an empty block? *)

(* Computes the byte size of this type. *)
Fixpoint sizeof_dtyp (ty:dtyp) : Z :=
  match ty with
  | DTYPE_I sz => 8 (* All integers are padded to 8 bytes. *)
  | DTYPE_Pointer => 8
  | DTYPE_Struct l => fold_left (fun x acc => x + sizeof_dtyp acc) l 0
  | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
  | _ => 0 (* TODO: add support for more types as necessary *)
  end.

(* Convert integer to its SByte representation. *)
Fixpoint Z_to_sbyte_list (count:nat) (z:Z) : list SByte :=
  match count with
  | O => []
  | S n => (Z_to_sbyte_list n (z / 256)) ++ [Byte (Byte.repr (z mod 256))]
  end.

(* Converts SBytes into their integer representation. *)
Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
  fst (fold_right (fun x acc =>
               match x with
               | Byte b =>
                 let shift := snd acc in
                 ((fst acc) + ((Byte.intval b) * shift), shift * 256)
               | _ => acc (* should not have other kinds bytes in an int *)
               end) (0, 1) bytes).

(* Serializes a dvalue into its SByte-sensitive form. *)
Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
  match dval with
  | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
  | DVALUE_I1 i => Z_to_sbyte_list 8 (DynamicValues.Int1.unsigned i)
  | DVALUE_I32 i => Z_to_sbyte_list 8 (DynamicValues.Int32.unsigned i)
  | DVALUE_I64 i => Z_to_sbyte_list 8 (Int64.unsigned i)
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
    | 1 => DVALUE_I1 (DynamicValues.Int1.repr des_int)
    | 32 => DVALUE_I32 (DynamicValues.Int32.repr des_int)
    | 64 => DVALUE_I64 (Int64.repr des_int)
    | _ => DVALUE_None (* invalid size. *)
    end
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

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (memory * X) :=
  match e with
  | Alloca t =>
    let new_block := make_empty_block t in
    inr  (add (size m) new_block m,
          DVALUE_Addr (size m, 0))
         
  | Load t dv =>
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some block =>
          inr (m,
               deserialize_sbytes (lookup_all_index i (sizeof_dtyp t) block SUndef) t)
        | None => inl (Load t dv)
        end
      end
    | _ => inl (Load t dv)
    end 

  | Store dv v =>
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some m' =>
          inr (add b (add_all_index (serialize_dvalue v) i m') m, ()) 
        | None => inl (Store dv v)
        end
      end
    | _ => inl (Store dv v)
    end
      
  | GEP t dv vs =>
    (* Index into a structured data type. *)
    let index_into_type typ index :=
        match typ with
        | DTYPE_Array sz ty =>
          if sz <=? index then None else
            Some (ty, index * (sizeof_dtyp ty))
        | DTYPE_Struct fields =>
          let new_typ := List.nth_error fields (Z.to_nat index) in
          match new_typ with
          | Some new_typ' =>
            (* Compute the byte-offset induced by the first i elements of the struct. *)
            let fix compute_offset typ_list i :=
                match typ_list with
                | [] => 0
                | hd :: tl =>
                  if i <? index
                  then sizeof_dtyp hd + compute_offset tl (i + 1)
                  else 0
                end
              in
            Some (new_typ', compute_offset fields 0)
          | None => None
          end
        | _ => None (* add type support as necessary *)
        end
    in
    (* Give back the final byte-offset into mem_bytes *)
    let fix gep_helper mem_bytes cur_type offsets offset_acc :=
        match offsets with
        | [] => offset_acc
        | dval :: tl =>
          match dval with
          | DVALUE_I32 x =>
            let nat_index := DynamicValues.Int32.unsigned x in
            let new_typ_info := index_into_type cur_type nat_index in
            match new_typ_info with
              | Some (new_typ, offset) => 
                gep_helper mem_bytes new_typ tl (offset_acc + offset)
              | None => 0 (* fail *)
            end
          | _ => 0 (* fail, at least until supporting non-i32 indexes *)
          end
        end
    in
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some block =>
          let mem_val := lookup_all_index i (sizeof_dtyp t) block SUndef in
          let answer := gep_helper mem_val t vs 0 in
          inr (m, DVALUE_Addr (b, i + answer))
        | None => inl (GEP t dv vs)
        end
      end
    | _ => inl (GEP t dv vs)
    end
  | ItoP i => inl (ItoP i) (* TODO: ItoP semantics *)

  | PtoI a => inl (PtoI a) (* TODO: ItoP semantics *)                     
                       
  | Call t f args  => inl (Call t f args)
  end.

(*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
*)

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Trace.Tau d'            => Trace.Tau (memD m d')
  | Trace.Vis _ io k =>
    match mem_step io m with
    | inr (m', v) => Trace.Tau (memD m' (k v))
    | inl e => Trace.Vis io k
    end
  | Trace.Ret x => d
  | Trace.Err x => d
  end.

End Make.

