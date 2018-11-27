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

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Axiom mfix_weak : forall `{Monad M} A B, ((A -> M B) -> (A -> M B)) -> A -> M B.
Extract Constant mfix_weak => "fun m -> let rec mfixw f a = f (mfixw f) a in mfixw".


Module Make (LLVMIO: LLVMInters) (CMM: Memory).
  Import LLVMIO.
  Import DV.
  Import CMM.

  (* Conversion functions *)
  Axiom pointer_value_to_dvalue : pointer_value -> dvalue.
  Coercion pointer_value_to_dvalue : pointer_value >-> dvalue.
  Extract Constant pointer_value_to_dvalue => "string".

  Axiom dvalue_to_pointer_value : dvalue -> pointer_value.
  Coercion dvalue_to_pointer_value : dvalue >-> pointer_value.

  Axiom integer_value_to_dvalue : integer_value -> dvalue.
  Coercion integer_value_to_dvalue : integer_value >-> dvalue.

  Axiom dvalue_to_integer_value : dvalue -> integer_value.
  Coercion dvalue_to_integer_value : dvalue >-> integer_value.

  Axiom floating_value_to_dvalue : floating_value -> dvalue.
  Coercion floating_value_to_dvalue : floating_value >-> dvalue.

  Axiom dvalue_to_floating_value : dvalue -> floating_value.
  Coercion dvalue_to_floating_value : dvalue >-> floating_value.

  Axiom mem_value_to_dvalue : mem_value -> dvalue.
  Coercion mem_value_to_dvalue : mem_value >-> dvalue.

  Axiom dvalue_to_mem_value : dvalue -> mem_value.
  Coercion dvalue_to_mem_value : dvalue >-> mem_value.

  Axiom dtyp_to_ctype : dtyp -> ctype0.
  Coercion dtyp_to_ctype : dtyp >-> ctype0.
  Extract Constant dtyp_to_ctype => "CoqCerberus.dtyp_to_ctype".

  Axiom Z_to_iv : Z -> integer_value.
  Coercion Z_to_iv : Z >-> integer_value.

  Axiom dtyp_to_ail_integer_type : dtyp -> AilIntegerType.
  Coercion dtyp_to_ail_integer_type : dtyp >-> AilIntegerType.

  Axiom thread_zero : thread_id.
  Axiom empty_prefix : symbol_prefix.
  Axiom empty_loc : loc_ocaml_t.

  Definition retC := ret.
  Definition bindC := bind.

  Definition memM_map {A B : Type} (f : A -> B) (ma : memM A) : memM B
    := bindC ma (fun a => retC (f a)).


  Program Instance FunctorMemM : Functor memM :=
    {
      fmap := @memM_map;
    }.


  Program Instance MonadMemM : Monad memM :=
    {
      ret := @retC;
      bind := @bindC;
    }.


  Definition addr := A.addr.

  Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
  Definition IntMap := IM.t.

  Definition add {a} k (v:a) := IM.add k v.
  Definition delete {a} k (m:IntMap a) := IM.remove k m.
  Definition member {a} k (m:IntMap a) := IM.mem k m.
  Definition lookup {a} k (m:IntMap a) := IM.find k m.
  Definition empty := CMM.initial_mem_state.

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

  Fixpoint handle_gep_h (t:dtyp) (pv:pointer_value) (vs:list dvalue) : err pointer_value :=
    match vs with
    | v :: vs' =>
      match v with
      | DVALUE_I32 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                              handle_gep_h ta (array_shift_ptrval pv (dtyp_to_ctype t) (Z_to_iv k)) vs'
        | DTYPE_Struct ts | DTYPE_Packed_struct ts => (* Handle these differently in future *)
                            raise "unimplemented structure indexing"
        (*
        let offset := fold_left (fun acc t => acc + sizeof_dtyp t)
                                (firstn n ts) 0 in
        match nth_error ts n with
        | None => raise "overflow"
        | Some t' =>
          handle_gep_h t' b (off + offset) vs' m
        end *)
        | _ => raise ("non-i32-indexable type")
        end
      | DVALUE_I8 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                              handle_gep_h ta (array_shift_ptrval pv (dtyp_to_ctype t) k) vs'
        | _ => raise ("non-i8-indexable type")
        end
      | DVALUE_I64 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta | DTYPE_Array _ ta =>
                              handle_gep_h ta (array_shift_ptrval pv (dtyp_to_ctype t) (Z_to_iv k)) vs'
        | _ => raise ("non-i64-indexable type")
        end
      | _ => raise "non-I32 index"
      end
    | [] => mret pv
    end.


  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue:=
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 indices *)
      match dv with
      | DVALUE_Addr pv =>
        let k := unsigned i in
        fmap pointer_value_to_dvalue (handle_gep_h t (array_shift_ptrval (dvalue_to_pointer_value (DVALUE_Addr pv)) (dtyp_to_ctype t) (Z_to_iv k)) vs')
      | _ => raise "non-address" 
      end
    | _ => raise "non-I32 index"
    end.


  Definition mem_step {X} (e:IO X) : err ((IO X) + (memM X)) :=
    match e with
    | Alloca t =>
      let new_block := allocate_dynamic thread_zero empty_prefix 0 (sizeof_dtyp t) in
      let new_block_dvalue := bind _ _ new_block (fun p => ret _ (pointer_value_to_dvalue p)) in
      mret (inr (new_block_dvalue))
           
    | Load t dv => mret
                    match dv with
                    | DVALUE_Addr a => inr (bind _ _ (CMM.load empty_loc (dtyp_to_ctype t) (dvalue_to_pointer_value dv)) (fun fm => let (f, m) := fm in ret _ (mem_value_to_dvalue m)))
                    | _ => inl (Load t dv)
                    end

    | Store t dv v => mret
                       match dv with
                       | DVALUE_Addr a => inr (bind _ _ (CMM.store empty_loc (dtyp_to_ctype t) (dvalue_to_pointer_value dv) (dvalue_to_mem_value v)) (fun a => CMM.ret _ tt))
                       | _ => inl (Store t dv v)
                       end
                       
    | GEP t dv vs =>
      match handle_gep t dv vs with
      | inl s => raise s
      | inr r => mret (inr (ret _ r))
      end

    | ItoP s t i =>
      match i with
      | DVALUE_I64 i => mret (inr (bind _ _ (ptrcast_ival s t (unsigned i)) (fun p => ret _ (pointer_value_to_dvalue p))))
      | DVALUE_I32 i => mret (inr (bind _ _ (ptrcast_ival s t (unsigned i)) (fun p => ret _ (pointer_value_to_dvalue p))))
      | DVALUE_I8 i => mret (inr (bind _ _ (ptrcast_ival s t (unsigned i)) (fun p => ret _ (pointer_value_to_dvalue p))))
      | DVALUE_I1 i => mret (inr (bind _ _ (ptrcast_ival s t (unsigned i)) (fun p => ret _ (pointer_value_to_dvalue p))))
      | _ => raise "Non integer passed to ItoP"
      end
        
    | PtoI s t a =>
      match a with
      | DVALUE_Addr p => mret (inr (bind _ _ (intcast_ptrval s (dtyp_to_ail_integer_type t) a) (fun iv => ret _ (integer_value_to_dvalue iv))))
      | _ => raise "Non pointer passed to PtoI"
      end
        
    | Call t f args  => mret (inl (Call t f args))
    end.


  (*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
   *)
  (* Definition mem_step {X} (e:IO X) : err ((IO X) + (memM X)) := *)

  Import ExtLib.Structures.Monad.

  Definition memD {X} (m:memory) (d:Trace X) : memM (Trace X) :=
    mfix_weak _ (fun memD =>
                   fun u =>
                     match u with
                     | Tau d' => bind (memD d') (fun t => ret (Tau t))
                     | Vis _ io k =>
                       match mem_step io with
                       | inr (inr cont) => bind cont (fun v => bind (memD (k v))
                                                                (fun memkv => ret (Tau memkv))) (* (Tau (memD m' (k v)))) *)
                       | inr (inl e) => ret (Vis io k)
                       | inl s => ret (@raise string Trace _ _ _ X s)
                       end
                     | Ret x => ret u
                     end) d.

End Make.
