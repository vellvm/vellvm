Require Import ZArith List String Omega.
Require Import Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics Vellvm.LLVMIO.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.LLVMIO.
Require Import ITree.
Require Import FSets.FMapAVL.
Require Import compcert.lib.Integers compcert.lib.Coqlib.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monad.
Require Import LLVMAddr.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import MemoryModel.

Module Make(LLVMIO: LLVMInters).
  Import LLVMIO.
  Import DV.

  Module CerberusTypes : MemoryTypes.

    Definition name := "Cerberus".

    Definition pointer_value := A.addr.
    Definition integer_value := Z.
    Definition floating_value := unit.

    Definition mem_value := dvalue.

    Definition footprint := unit.

    Definition mem_state := unit.
    Definition initial_mem_state := tt.

    (* TODO Original just uses Cthread.thread_id, not sure what we would use. *)
    Definition thread_id := nat.

    (* TODO Original used Core_ctype.ctype0... Not sure what this is, though. *)
    Definition ctype0 := dtyp.

    (* TODO Symbol.prefix *)
    Definition symbol_prefix := string.

    Definition symbol_sym := string.
    Definition null_ptrval := fun (_ : ctype0) => A.null.
    Definition fun_ptrval := fun (_ : symbol_sym) => A.null.
  End CerberusTypes.

  Module MTC : MemoryTypeConversion LLVMIO CerberusTypes.
    Definition pointer_value_to_dvalue := DVALUE_Addr.
    Definition dvalue_to_pointer_value (dv : dvalue) : pointer_value
      := match dv with
         | DVALUE_Addr a => a
         | _ => A.null
         end.

    Definition integer_value_to_dvalue (iv : integer_value) : dvalue :=
      DVALUE_I64 (repr iv).
    
    Definition dvalue_to_integer_value (dv : dvalue) : integer_value :=
      match dv with
      | DVALUE_I1 x => signed x
      | DVALUE_I8 x => signed x
      | DVALUE_I32 x => signed x
      | DVALUE_I64 x => signed x
      | _ => 0
      end.

    Definition floating_value_to_dvalue (fv : floating_value) : dvalue := DVALUE_None.
    Definition dvalue_to_floating_value (dv : dvalue) : floating_value := tt.
  End MTC.


  Require Import ExtLib.Data.Monads.IdentityMonad.

  Module CerberusMonad <: MemoryMonad.
    Definition memM := ident.
    Definition ret := @ret ident Monad_ident.
    Definition bind := @bind ident Monad_ident.
  End CerberusMonad.

  Module Type MemoryInst := Memory CerberusTypes CerberusMonad.

  Import LLVMIO.
  Import DV.
  Module MTC := MTC LLVMIO.
  Import MTC.

(* Cerberus memory model *)

Module MemoryLLVM (CMM : MemoryInst).

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

(* Definition mem_block := unit. *)
Print MemoryInst.
Definition memory := CMM.mem_state.
Definition undef := DVALUE_Undef. (* TODO: should this be an empty block? *)

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
  | [] => mret (m, DVALUE_Addr (b, off))
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


(* TODO *)
Definition dvalue_to_mem_value (dv : dvalue) : CMM.mem_value := tt.
Definition dtyp_to_ail_integer_type (dt : dtyp) : CMM.AilIntegerType := tt.

Definition mem_step {X} (e:IO X) (m:memory) : err ((IO X) + (CMM.memM X)) :=
  match e with
  | Alloca t =>
    let new_block := CMM.allocate_dynamic 0%nat "" 0 (sizeof_dtyp t) in
    let new_block_dvalue := CMM.bind _ _ new_block (fun p => CMM.ret _ (MTC.pointer_value_to_dvalue p)) in
    mret (inr (new_block_dvalue))
         
  | Load t dv => mret
    match dv with
    | DVALUE_Addr a => CMM.load "" t a
    | _ => mret (inl (Load t dv))
    end

  | Store t dv v => mret
    match dv with
    | DVALUE_Addr a => inr (CMM.bind _ _ (CMM.store "" t a (dvalue_to_mem_value v)) (fun a => CMM.ret _ tt))
    | _ => mret (inl (Store t dv v))
    end
      
  | GEP t dv vs =>
    match handle_gep t dv vs m with
    | inl s => raise s
    | inr r => mret (inr r)
    end

  | ItoP s t i =>
    match i with
    | DVALUE_I64 i => mret (inr (CMM.bind _ _ (CMM.ptrcast_ival s t (unsigned i)) (fun p => CMM.ret _ (MTC.pointer_value_to_dvalue p))))
    | DVALUE_I32 i => mret (inr (CMM.bind _ _ (CMM.ptrcast_ival s t (unsigned i)) (fun p => CMM.ret _ (MTC.pointer_value_to_dvalue p))))
    | DVALUE_I8 i => mret (inr (CMM.bind _ _ (CMM.ptrcast_ival s t (unsigned i)) (fun p => CMM.ret _ (MTC.pointer_value_to_dvalue p))))
    | DVALUE_I1 i => mret (inr (CMM.bind _ _ (CMM.ptrcast_ival s t (unsigned i)) (fun p => CMM.ret _ (MTC.pointer_value_to_dvalue p))))
    | _ => raise "Non integer passed to ItoP"
    end
    
  | PtoI s t a =>
    match a with
    | DVALUE_Addr p => raise "bleh" (* mret (inr (CMM.intcast_ptrval s (dtyp_to_ail_integer_type t) p)) *)
    | _ => raise "Non pointer passed to PtoI"
    end
                       
  | Call t f args  => mret (inl (Call t f args))
  end.

(*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
*)

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Tau d' => Tau (memD m d')
  | Vis _ io k =>
    match mem_step io m with
    | inr (inr (m', v)) => Tau (memD m' (k v))
    | inr (inl e) => Vis io k
    | inl s => raise s
    end
  | Ret x => d
  end.
End MemoryLLVM.

End Make.
