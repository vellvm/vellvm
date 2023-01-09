From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.LLVMParams
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.


Module Type AddrConvert (ADDR1 : ADDRESS) (ADDR2 : ADDRESS).
  Parameter addr_convert : ADDR1.addr -> OOM ADDR2.addr.
  Parameter addr_convert_null :
    addr_convert ADDR1.null = NoOom ADDR2.null.

  Parameter addr_convert_injective :
    forall a b c,
      addr_convert a = NoOom c ->
      addr_convert b = NoOom c ->
      a = b.
End AddrConvert.

Module InfToFinAddrConvert : AddrConvert InfAddr FinAddr
with Definition addr_convert :=
  fun a =>
    match a with
    | (ix, pr) =>
        FinITOP.int_to_ptr ix pr
    end.

Definition addr_convert (a : InfAddr.addr) : OOM FinAddr.addr :=
  match a with
  | (ix, pr) =>
      FinITOP.int_to_ptr ix pr
  end.

Lemma addr_convert_null :
  addr_convert InfAddr.null = NoOom FinAddr.null.
Proof.
  unfold addr_convert.
  cbn.
  reflexivity.
Qed.

Lemma addr_convert_injective :
  forall a b c,
    addr_convert a = NoOom c ->
    addr_convert b = NoOom c ->
    a = b.
Proof.
  intros a b c AC BC.
  unfold addr_convert in *.
  destruct a, b.
  unfold FinITOP.int_to_ptr in *.
  break_match_hyp; inv BC.
  break_match_hyp; inv AC.
  induction i, i0;
    cbn in *; auto; inv Heqb0.

  {
    break_match.
    break_match.
    subst.

    pose proof proof_irrelevance _ intrange intrange0; subst.
    rewrite <- Heqi in Heqi0.
    exfalso.

    inversion Heqi0.

    inv Heqi0.
    break_match.
    break_match.
    subst.
    inv Heqi.
    Transparent Int64.repr.
    unfold Int64.repr in *.
    Opaque Int64.repr.
    admit.
  }
Admitted.

End InfToFinAddrConvert.

Module FinToInfAddrConvert : AddrConvert FinAddr InfAddr
with Definition addr_convert :=
  fun a =>
    match a with
    | (ix, pr) =>
        InfITOP.int_to_ptr (Int64.unsigned ix) pr
    end.

Definition addr_convert (a : FinAddr.addr) : OOM InfAddr.addr :=
  match a with
  | (ix, pr) =>
      InfITOP.int_to_ptr (Int64.unsigned ix) pr
  end.

Lemma addr_convert_null :
  addr_convert FinAddr.null = NoOom InfAddr.null.
Proof.
  unfold addr_convert.
  cbn.
  reflexivity.
Qed.

Lemma addr_convert_injective :
  forall a b c,
    addr_convert a = NoOom c ->
    addr_convert b = NoOom c ->
    a = b.
Proof.
  intros a b c AC BC.
  unfold addr_convert in *.
  destruct a, b.
  inv AC. inv BC.
  unfold Int64.unsigned in *.
  destruct i0, i.
  cbn in *.
  inv H0.
  pose proof proof_irrelevance _ intrange intrange0; subst.
  reflexivity.
Qed.

End FinToInfAddrConvert.

Module Type AddrConvertSafe (ADDR1 : ADDRESS) (ADDR2 : ADDRESS) (AC1 : AddrConvert ADDR1 ADDR2) (AC2 : AddrConvert ADDR2 ADDR1).
  (* ADDR1 is "contained within" ADDR2 *)

  Parameter addr_convert_succeeds :
    forall a1,
    exists a2, AC1.addr_convert a1 = NoOom a2.

  Parameter addr_convert_safe :
    forall a1 a2,
      AC1.addr_convert a1 = NoOom a2 ->
      AC2.addr_convert a2 = NoOom a1.
End AddrConvertSafe.

Module Type IPConvertSafe (IP1 : INTPTR) (IP2 : INTPTR).
  (* IP1 is contained within IP2 *)

  Parameter intptr_convert_succeeds :
    forall i1,
    exists i2, IP2.from_Z (IP1.to_Z i1) = NoOom i2.

  Parameter intptr_convert_safe :
    forall i1 i2,
      IP2.from_Z (IP1.to_Z i1) = NoOom i2 ->
      IP1.from_Z (IP2.to_Z i2) = NoOom i1.
End IPConvertSafe.

Module FinToInfAddrConvertSafe : AddrConvertSafe FinAddr InfAddr FinToInfAddrConvert InfToFinAddrConvert.
  Lemma addr_convert_succeeds :
    forall a1,
    exists a2, FinToInfAddrConvert.addr_convert a1 = NoOom a2.
  Proof.
    intros a1.
    destruct a1.
    cbn.
    eexists; reflexivity.
  Qed.

  Lemma addr_convert_safe :
    forall a1 a2,
      FinToInfAddrConvert.addr_convert a1 = NoOom a2 ->
      InfToFinAddrConvert.addr_convert a2 = NoOom a1.
  Proof.
    intros a1 a2 FI.
    unfold FinToInfAddrConvert.addr_convert in FI.
    cbn in FI.
    destruct a1.
    inv FI.
    unfold FiniteAddresses.Iptr in *.
    unfold InfToFinAddrConvert.addr_convert.
    unfold FinITOP.int_to_ptr.
    pose proof (Int64.unsigned_range i) as RANGE.
    assert (((Int64.unsigned i <? 0)%Z || (Int64.unsigned i >=? Int64.modulus)%Z)%bool = false)
      as COND by lia.

    rewrite COND.
    rewrite Int64.repr_unsigned.
    reflexivity.
  Qed.
End FinToInfAddrConvertSafe.

Module FinToInfIntptrConvertSafe : IPConvertSafe IP64Bit BigIP.
  Lemma intptr_convert_succeeds :
    forall i1,
    exists i2, BigIP.from_Z (IP64Bit.to_Z i1) = NoOom i2.
  Proof.
    intros i1.
    cbn.
    exists (IP64Bit.to_Z i1).
    reflexivity.
  Qed.

  Lemma intptr_convert_safe :
    forall i1 i2,
      BigIP.from_Z (IP64Bit.to_Z i1) = NoOom i2 ->
      IP64Bit.from_Z (BigIP.to_Z i2) = NoOom i1.
  Proof.
    intros i1 i2 H.
    cbn in *.
    inv H.
    unfold FiniteIntptr.BigIP.to_Z.
    apply IP64Bit.to_Z_from_Z.
  Qed.
End FinToInfIntptrConvertSafe.

Module Type DVConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  Import AC.

  Module DV1 := Events1.DV.
  Module DV2 := Events2.DV.

  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | DV1.solve_dvalue_measure | DV1.solve_uvalue_measure].

  Program Fixpoint dvalue_convert_lazy (dv1 : DV1.dvalue) {measure (DV1.dvalue_measure dv1)} : DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           match addr_convert a with
           | Oom msg => DV2.DVALUE_Oom DTYPE_Pointer
           | NoOom a' => DV2.DVALUE_Addr a'
           end
       | DV1.DVALUE_I1 x  => DV2.DVALUE_I1 x
       | DV1.DVALUE_I8 x  => DV2.DVALUE_I8 x
       | DV1.DVALUE_I32 x => DV2.DVALUE_I32 x
       | DV1.DVALUE_I64 x => DV2.DVALUE_I64 x
       | DV1.DVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           match LP2.IP.from_Z xz with
           | Oom msg => DV2.DVALUE_Oom DTYPE_IPTR
           | NoOom x' => DV2.DVALUE_IPTR x'
           end
       | DV1.DVALUE_Double x => DV2.DVALUE_Double x
       | DV1.DVALUE_Float x => DV2.DVALUE_Float x
       | DV1.DVALUE_Poison t => DV2.DVALUE_Poison t
       | DV1.DVALUE_Oom t => DV2.DVALUE_Oom t
       | DV1.DVALUE_None => DV2.DVALUE_None
       | DV1.DVALUE_Struct fields =>
           let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Struct fields'
       | DV1.DVALUE_Packed_struct fields =>
           let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Packed_struct fields'
       | DV1.DVALUE_Array elts =>
           let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Array elts'
       | DV1.DVALUE_Vector elts =>
           let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Vector elts'
       end.

  Program Fixpoint uvalue_convert_lazy (uv1 : DV1.uvalue) {measure (DV1.uvalue_measure uv1)} : DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           match addr_convert a with
           | Oom msg => DV2.UVALUE_Oom DTYPE_Pointer
           | NoOom a' => DV2.UVALUE_Addr a'
           end
       | DV1.UVALUE_I1 x  => DV2.UVALUE_I1 x
       | DV1.UVALUE_I8 x  => DV2.UVALUE_I8 x
       | DV1.UVALUE_I32 x => DV2.UVALUE_I32 x
       | DV1.UVALUE_I64 x => DV2.UVALUE_I64 x
       | DV1.UVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           match LP2.IP.from_Z xz with
           | Oom msg => DV2.UVALUE_Oom DTYPE_IPTR
           | NoOom x' => DV2.UVALUE_IPTR x'
           end
       | DV1.UVALUE_Double x => DV2.UVALUE_Double x
       | DV1.UVALUE_Float x => DV2.UVALUE_Float x
       | DV1.UVALUE_Poison t => DV2.UVALUE_Poison t
       | DV1.UVALUE_Oom t => DV2.UVALUE_Oom t
       | DV1.UVALUE_None => DV2.UVALUE_None
       | DV1.UVALUE_Struct fields =>
           let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Struct fields'
       | DV1.UVALUE_Packed_struct fields =>
           let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Packed_struct fields'
       | DV1.UVALUE_Array elts =>
           let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Array elts'
       | DV1.UVALUE_Vector elts =>
           let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Vector elts'
       | DV1.UVALUE_Undef dt =>
           (* Could be a bit odd with intptr *)
           DV2.UVALUE_Undef dt
       | DV1.UVALUE_IBinop iop v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_IBinop iop v1' v2'
       | DV1.UVALUE_ICmp cmp v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_ICmp cmp v1' v2'
       | DV1.UVALUE_FBinop fop fm v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_FBinop fop fm v1' v2'
       | DV1.UVALUE_FCmp cmp v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_FCmp cmp v1' v2'
       | DV1.UVALUE_Conversion conv t_from v t_to =>
           let v' := uvalue_convert_lazy v in
           DV2.UVALUE_Conversion conv t_from v' t_to
       | DV1.UVALUE_GetElementPtr t ptrval idxs =>
           let ptrval' := uvalue_convert_lazy ptrval in
           let idxs' := map_In idxs (fun elt Hin => uvalue_convert_lazy elt) in
           DV2.UVALUE_GetElementPtr t ptrval' idxs'
       | DV1.UVALUE_ExtractElement t vec idx =>
           let vec' := uvalue_convert_lazy vec in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_ExtractElement t vec' idx'
       | DV1.UVALUE_InsertElement t vec elt idx =>
           let vec' := uvalue_convert_lazy vec in
           let elt' := uvalue_convert_lazy elt in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_InsertElement t vec' elt' idx'
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           let vec1' := uvalue_convert_lazy vec1 in
           let vec2' := uvalue_convert_lazy vec2 in
           let idxmask' := uvalue_convert_lazy idxmask in
           DV2.UVALUE_ShuffleVector vec1' vec2' idxmask'
       | DV1.UVALUE_ExtractValue t vec idxs =>
           let vec' := uvalue_convert_lazy vec in
           DV2.UVALUE_ExtractValue t vec' idxs
       | DV1.UVALUE_InsertValue t vec elt idxs =>
           let vec' := uvalue_convert_lazy vec in
           let elt' := uvalue_convert_lazy elt in
           DV2.UVALUE_InsertValue t vec' elt' idxs
       | DV1.UVALUE_Select cnd v1 v2 =>
           let cnd' := uvalue_convert_lazy cnd in
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_Select cnd' v1' v2'
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           let uv' := uvalue_convert_lazy uv in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_ExtractByte uv' dt idx' sid
       | DV1.UVALUE_ConcatBytes uvs dt =>
           let uvs' := map_In uvs (fun elt Hin => uvalue_convert_lazy elt) in
           DV2.UVALUE_ConcatBytes uvs' dt
       end.

  Opaque dvalue_convert_lazy.
  Lemma dvalue_convert_lazy_equation :
    forall dv,
      dvalue_convert_lazy dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.DVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.DVALUE_Addr a'
            end
        | DV1.DVALUE_I1 x  => DV2.DVALUE_I1 x
        | DV1.DVALUE_I8 x  => DV2.DVALUE_I8 x
        | DV1.DVALUE_I32 x => DV2.DVALUE_I32 x
        | DV1.DVALUE_I64 x => DV2.DVALUE_I64 x
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.DVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.DVALUE_IPTR x'
            end
        | DV1.DVALUE_Double x => DV2.DVALUE_Double x
        | DV1.DVALUE_Float x => DV2.DVALUE_Float x
        | DV1.DVALUE_Poison t => DV2.DVALUE_Poison t
        | DV1.DVALUE_Oom t => DV2.DVALUE_Oom t
        | DV1.DVALUE_None => DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Struct fields'
        | DV1.DVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Packed_struct fields'
        | DV1.DVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Array elts'
        | DV1.DVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Vector elts'
        end.
  Proof.
    intros dv.
    Transparent dvalue_convert_lazy.
    unfold dvalue_convert_lazy at 1.
    rewrite Wf.WfExtensionality.fix_sub_eq_ext.
    destruct dv; try reflexivity.
    break_match; reflexivity.
    break_match; reflexivity.
  Qed.

  Lemma uvalue_convert_lazy_equation:
    forall uv,
      uvalue_convert_lazy uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.UVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.UVALUE_Addr a'
            end
        | DV1.UVALUE_I1 x  => DV2.UVALUE_I1 x
        | DV1.UVALUE_I8 x  => DV2.UVALUE_I8 x
        | DV1.UVALUE_I32 x => DV2.UVALUE_I32 x
        | DV1.UVALUE_I64 x => DV2.UVALUE_I64 x
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.UVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.UVALUE_IPTR x'
            end
        | DV1.UVALUE_Double x => DV2.UVALUE_Double x
        | DV1.UVALUE_Float x => DV2.UVALUE_Float x
        | DV1.UVALUE_Poison t => DV2.UVALUE_Poison t
        | DV1.UVALUE_Oom t => DV2.UVALUE_Oom t
        | DV1.UVALUE_None => DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Struct fields'
        | DV1.UVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Packed_struct fields'
        | DV1.UVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Array elts'
        | DV1.UVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Vector elts'
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            DV2.UVALUE_Undef dt
        | DV1.UVALUE_IBinop iop v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_IBinop iop v1' v2'
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_ICmp cmp v1' v2'
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FBinop fop fm v1' v2'
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FCmp cmp v1' v2'
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            let v' := uvalue_convert_lazy v in
            DV2.UVALUE_Conversion conv t_from v' t_to
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            let ptrval' := uvalue_convert_lazy ptrval in
            let idxs' := map_In idxs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_GetElementPtr t ptrval' idxs'
        | DV1.UVALUE_ExtractElement t vec idx =>
            let vec' := uvalue_convert_lazy vec in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractElement t vec' idx'
        | DV1.UVALUE_InsertElement t vec elt idx =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_InsertElement t vec' elt' idx'
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            let vec1' := uvalue_convert_lazy vec1 in
            let vec2' := uvalue_convert_lazy vec2 in
            let idxmask' := uvalue_convert_lazy idxmask in
            DV2.UVALUE_ShuffleVector vec1' vec2' idxmask'
        | DV1.UVALUE_ExtractValue t vec idxs =>
            let vec' := uvalue_convert_lazy vec in
            DV2.UVALUE_ExtractValue t vec' idxs
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            DV2.UVALUE_InsertValue t vec' elt' idxs
        | DV1.UVALUE_Select cnd v1 v2 =>
            let cnd' := uvalue_convert_lazy cnd in
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_Select cnd' v1' v2'
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            let uv' := uvalue_convert_lazy uv in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractByte uv' dt idx' sid
        | DV1.UVALUE_ConcatBytes uvs dt =>
            let uvs' := map_In uvs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_ConcatBytes uvs' dt
        end.
  Proof.
    (* intros uv. *)
    (* Transparent uvalue_convert_lazy. *)
    (* unfold uvalue_convert_lazy at 1. *)
    (* Opaque uvalue_convert_lazy. *)
    (* (* TODO: This is really slow *) *)
    (* rewrite Wf.WfExtensionality.fix_sub_eq_ext. *)
    (* destruct uv; reflexivity. *)
  Admitted.

  Obligation Tactic :=
    try Tactics.program_simpl;
  try solve [ cbn; try lia
            | DV1.solve_dvalue_measure
            | DV1.solve_uvalue_measure
            | repeat split;
              intros * [CONTRA1 CONTRA2];
              solve [ inv CONTRA1
                    | inv CONTRA2
                ]
    ].

  Definition uvalue_converted_lazy (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop :=
    uvalue_convert_lazy uv1 = uv2.

  Definition dvalue_converted_lazy (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop :=
    dvalue_convert_lazy dv1 = dv2.

  (** A version of dvalue refinement between languages where OOM can be the lazy OOM value *)
  Program Fixpoint dvalue_refine_lazy (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) {measure (DV1.dvalue_measure dv1)} : Prop
    := dvalue_converted_lazy dv1 dv2 \/
         match dv1, dv2 with
         | _, DV2.DVALUE_Oom t2 =>
             DV1.dvalue_has_dtyp dv1 t2
         | DV1.DVALUE_Struct fields1, DV2.DVALUE_Struct fields2 =>
             Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
         | DV1.DVALUE_Packed_struct fields1, DV2.DVALUE_Packed_struct fields2 =>
             Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
         | DV1.DVALUE_Array elts1, DV2.DVALUE_Array elts2 =>
             Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
         | DV1.DVALUE_Vector elts1, DV2.DVALUE_Vector elts2 =>
             Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
         | _, _ =>
             False
         end.

  Lemma dvalue_refine_lazy_equation :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 =
        (dvalue_converted_lazy dv1 dv2 \/
          match dv1, dv2 with
          | _, DV2.DVALUE_Oom t2 =>
              DV1.dvalue_has_dtyp dv1 t2
          | DV1.DVALUE_Struct fields1, DV2.DVALUE_Struct fields2 =>
              Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
          | DV1.DVALUE_Packed_struct fields1, DV2.DVALUE_Packed_struct fields2 =>
              Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
          | DV1.DVALUE_Array elts1, DV2.DVALUE_Array elts2 =>
              Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
          | DV1.DVALUE_Vector elts1, DV2.DVALUE_Vector elts2 =>
              Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
          | _, _ =>
              False
          end).
  Proof.
  Admitted.

  Program Fixpoint uvalue_refine_lazy (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) {measure (DV1.uvalue_measure uv1)} : Prop
    := uvalue_converted_lazy uv1 uv2 \/
         match uv1, uv2 with
         | _, DV2.UVALUE_Oom t2 =>
             DV1.uvalue_has_dtyp uv1 t2
         | DV1.UVALUE_Struct fields1, DV2.UVALUE_Struct fields2 =>
             Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
         | DV1.UVALUE_Packed_struct fields1, DV2.UVALUE_Packed_struct fields2 =>
             Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
         | DV1.UVALUE_Array elts1, DV2.UVALUE_Array elts2 =>
             Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
         | DV1.UVALUE_Vector elts1, DV2.UVALUE_Vector elts2 =>
             Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
         | DV1.UVALUE_IBinop iop1 v1_1 v2_1, DV2.UVALUE_IBinop iop2 v1_2 v2_2 =>
             iop1 = iop2 /\
               uvalue_refine_lazy v1_1 v1_2 /\
               uvalue_refine_lazy v2_1 v2_2
         | DV1.UVALUE_ICmp cmp1 v1_1 v2_1, DV2.UVALUE_ICmp cmp2 v1_2 v2_2 =>
             cmp1 = cmp2 /\
               uvalue_refine_lazy v1_1 v1_2 /\
               uvalue_refine_lazy v2_1 v2_2
         | DV1.UVALUE_FBinop fop1 fm1 v1_1 v2_1, DV2.UVALUE_FBinop fop2 fm2 v1_2 v2_2 =>
             fop1 = fop2 /\
               fm1 = fm2 /\
               uvalue_refine_lazy v1_1 v1_2 /\
               uvalue_refine_lazy v2_1 v2_2
         | DV1.UVALUE_FCmp cmp1 v1_1 v2_1, DV2.UVALUE_FCmp cmp2 v1_2 v2_2 =>
             cmp1 = cmp2 /\
               uvalue_refine_lazy v1_1 v1_2 /\
               uvalue_refine_lazy v2_1 v2_2
         | DV1.UVALUE_Conversion conv1 t_from1 v1 t_to1, DV2.UVALUE_Conversion conv2 t_from2 v2 t_to2 =>
             conv1 = conv2 /\
               uvalue_refine_lazy v1 v2 /\
               t_from1 = t_from2 /\
               t_to1 = t_to2
         | DV1.UVALUE_GetElementPtr t1 ptrval1 idxs1, DV2.UVALUE_GetElementPtr t2 ptrval2 idxs2 =>
             t1 = t2 /\
               uvalue_refine_lazy ptrval1 ptrval2 /\
               Forall2_HIn idxs1 idxs2 (fun ix1 ix2 IN1 IN2 => uvalue_refine_lazy ix1 ix2)
         | DV1.UVALUE_ExtractElement vec_typ1 vec1 idx1, DV2.UVALUE_ExtractElement vec_typ2 vec2 idx2 =>
             vec_typ1 = vec_typ2 /\
               uvalue_refine_lazy vec1 vec2 /\
               uvalue_refine_lazy idx1 idx2
         | DV1.UVALUE_InsertElement vec_typ1 vec1 elt1 idx1, DV2.UVALUE_InsertElement vec_typ2 vec2 elt2 idx2 =>
             vec_typ1 = vec_typ2 /\
               uvalue_refine_lazy vec1 vec2 /\
               uvalue_refine_lazy elt1 elt2 /\
               uvalue_refine_lazy idx1 idx2
         | DV1.UVALUE_ShuffleVector vec1_1 vec2_1 idxmask1, DV2.UVALUE_ShuffleVector vec1_2 vec2_2 idxmask2 =>
             uvalue_refine_lazy vec1_1 vec1_2 /\
             uvalue_refine_lazy vec2_1 vec2_2 /\
               uvalue_refine_lazy idxmask1 idxmask2
         | DV1.UVALUE_ExtractValue vec_typ1 vec1 idxs1, DV2.UVALUE_ExtractValue vec_typ2 vec2 idxs2 =>
             vec_typ1 = vec_typ2 /\
               uvalue_refine_lazy vec1 vec2 /\
               idxs1 = idxs2
         | DV1.UVALUE_InsertValue vec_typ1 vec1 elt1 idxs1, DV2.UVALUE_InsertValue vec_typ2 vec2 elt2 idxs2 =>
             vec_typ1 = vec_typ2 /\
               uvalue_refine_lazy vec1 vec2 /\
               uvalue_refine_lazy elt1 elt2 /\
               idxs1 = idxs2
         | DV1.UVALUE_Select cnd1 v1_1 v2_1, DV2.UVALUE_Select cnd2 v1_2 v2_2 =>
             uvalue_refine_lazy cnd1 cnd2 /\
               uvalue_refine_lazy v1_1 v1_2 /\
               uvalue_refine_lazy v2_1 v2_2
         | DV1.UVALUE_ExtractByte uv1 dt1 idx1 sid1, DV2.UVALUE_ExtractByte uv2 dt2 idx2 sid2 =>
             uvalue_refine_lazy uv1 uv2 /\
               dt1 = dt2 /\
               uvalue_refine_lazy idx1 idx2 /\
               sid1 = sid2
         | DV1.UVALUE_ConcatBytes uvs1 dt1, DV2.UVALUE_ConcatBytes uvs2 dt2 =>
             Forall2_HIn uvs1 uvs2 (fun uv1 uv2 IN1 IN2 => uvalue_refine_lazy uv1 uv2) /\
               dt1 = dt2
         | _, _ =>
             False
         end.

  Lemma uvalue_refine_lazy_equation :
    forall uv1 uv2,
      uvalue_refine_lazy uv1 uv2 =
        (uvalue_converted_lazy uv1 uv2 \/
          match uv1, uv2 with
          | _, DV2.UVALUE_Oom t2 =>
              DV1.uvalue_has_dtyp uv1 t2
          | DV1.UVALUE_Struct fields1, DV2.UVALUE_Struct fields2 =>
              Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
          | DV1.UVALUE_Packed_struct fields1, DV2.UVALUE_Packed_struct fields2 =>
              Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
          | DV1.UVALUE_Array elts1, DV2.UVALUE_Array elts2 =>
              Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
          | DV1.UVALUE_Vector elts1, DV2.UVALUE_Vector elts2 =>
              Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
          | DV1.UVALUE_IBinop iop1 v1_1 v2_1, DV2.UVALUE_IBinop iop2 v1_2 v2_2 =>
              iop1 = iop2 /\
                uvalue_refine_lazy v1_1 v1_2 /\
                uvalue_refine_lazy v2_1 v2_2
          | DV1.UVALUE_ICmp cmp1 v1_1 v2_1, DV2.UVALUE_ICmp cmp2 v1_2 v2_2 =>
              cmp1 = cmp2 /\
                uvalue_refine_lazy v1_1 v1_2 /\
                uvalue_refine_lazy v2_1 v2_2
          | DV1.UVALUE_FBinop fop1 fm1 v1_1 v2_1, DV2.UVALUE_FBinop fop2 fm2 v1_2 v2_2 =>
              fop1 = fop2 /\
                fm1 = fm2 /\
                uvalue_refine_lazy v1_1 v1_2 /\
                uvalue_refine_lazy v2_1 v2_2
          | DV1.UVALUE_FCmp cmp1 v1_1 v2_1, DV2.UVALUE_FCmp cmp2 v1_2 v2_2 =>
              cmp1 = cmp2 /\
                uvalue_refine_lazy v1_1 v1_2 /\
                uvalue_refine_lazy v2_1 v2_2
          | DV1.UVALUE_Conversion conv1 t_from1 v1 t_to1, DV2.UVALUE_Conversion conv2 t_from2 v2 t_to2 =>
              conv1 = conv2 /\
                uvalue_refine_lazy v1 v2 /\
                t_from1 = t_from2 /\
                t_to1 = t_to2
          | DV1.UVALUE_GetElementPtr t1 ptrval1 idxs1, DV2.UVALUE_GetElementPtr t2 ptrval2 idxs2 =>
              t1 = t2 /\
                uvalue_refine_lazy ptrval1 ptrval2 /\
                Forall2_HIn idxs1 idxs2 (fun ix1 ix2 IN1 IN2 => uvalue_refine_lazy ix1 ix2)
          | DV1.UVALUE_ExtractElement vec_typ1 vec1 idx1, DV2.UVALUE_ExtractElement vec_typ2 vec2 idx2 =>
              vec_typ1 = vec_typ2 /\
                uvalue_refine_lazy vec1 vec2 /\
                uvalue_refine_lazy idx1 idx2
          | DV1.UVALUE_InsertElement vec_typ1 vec1 elt1 idx1, DV2.UVALUE_InsertElement vec_typ2 vec2 elt2 idx2 =>
              vec_typ1 = vec_typ2 /\
                uvalue_refine_lazy vec1 vec2 /\
                uvalue_refine_lazy elt1 elt2 /\
                uvalue_refine_lazy idx1 idx2
          | DV1.UVALUE_ShuffleVector vec1_1 vec2_1 idxmask1, DV2.UVALUE_ShuffleVector vec1_2 vec2_2 idxmask2 =>
              uvalue_refine_lazy vec1_1 vec1_2 /\
                uvalue_refine_lazy vec2_1 vec2_2 /\
                uvalue_refine_lazy idxmask1 idxmask2
          | DV1.UVALUE_ExtractValue vec_typ1 vec1 idxs1, DV2.UVALUE_ExtractValue vec_typ2 vec2 idxs2 =>
              vec_typ1 = vec_typ2 /\
                uvalue_refine_lazy vec1 vec2 /\
                idxs1 = idxs2
          | DV1.UVALUE_InsertValue vec_typ1 vec1 elt1 idxs1, DV2.UVALUE_InsertValue vec_typ2 vec2 elt2 idxs2 =>
              vec_typ1 = vec_typ2 /\
                uvalue_refine_lazy vec1 vec2 /\
                uvalue_refine_lazy elt1 elt2 /\
                idxs1 = idxs2
          | DV1.UVALUE_Select cnd1 v1_1 v2_1, DV2.UVALUE_Select cnd2 v1_2 v2_2 =>
              uvalue_refine_lazy cnd1 cnd2 /\
                uvalue_refine_lazy v1_1 v1_2 /\
                uvalue_refine_lazy v2_1 v2_2
          | DV1.UVALUE_ExtractByte uv1 dt1 idx1 sid1, DV2.UVALUE_ExtractByte uv2 dt2 idx2 sid2 =>
              uvalue_refine_lazy uv1 uv2 /\
                dt1 = dt2 /\
                uvalue_refine_lazy idx1 idx2 /\
                sid1 = sid2
          | DV1.UVALUE_ConcatBytes uvs1 dt1, DV2.UVALUE_ConcatBytes uvs2 dt2 =>
              Forall2_HIn uvs1 uvs2 (fun uv1 uv2 IN1 IN2 => uvalue_refine_lazy uv1 uv2) /\
                dt1 = dt2
          | _, _ =>
              False
          end).
  Proof.
  Admitted.

  Lemma dvalue_refine_lazy_dvalue_convert_lazy :
    forall dv,
      dvalue_refine_lazy dv (dvalue_convert_lazy dv).
  Proof.
    intros dv.
    induction dv;
      rewrite dvalue_refine_lazy_equation;
      left; red; auto.
  Qed.

  Lemma uvalue_refine_lazy_uvalue_convert_lazy :
    forall dv,
      uvalue_refine_lazy dv (uvalue_convert_lazy dv).
  Proof.
    intros dv.
    induction dv;
      rewrite uvalue_refine_lazy_equation;
      left; red; auto.
  Qed.

  Lemma dvalue_refine_lazy_dvalue_converted_lazy :
    forall dv1 dv2,
      dvalue_converted_lazy dv1 dv2 ->
      dvalue_refine_lazy dv1 dv2.
  Proof.
    intros dv1 dv2 CONV; inv CONV.
    apply dvalue_refine_lazy_dvalue_convert_lazy.
  Qed.

  Lemma uvalue_refine_uvalue_converted :
    forall uv1 uv2,
      uvalue_converted_lazy uv1 uv2 ->
      uvalue_refine_lazy uv1 uv2.
  Proof.
    intros uv1 uv2 CONV; inv CONV.
    apply uvalue_refine_lazy_uvalue_convert_lazy.
  Qed.

  Program Fixpoint dvalue_convert_strict (dv1 : DV1.dvalue) {measure (DV1.dvalue_measure dv1)} : OOM DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.DVALUE_Addr a')
       | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
       | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
       | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
       | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
       | DV1.DVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.DVALUE_IPTR x')
       | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
       | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
       | DV1.DVALUE_Oom t => ret (DV2.DVALUE_Oom t)
       | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
       | DV1.DVALUE_None => ret DV2.DVALUE_None
       | DV1.DVALUE_Struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Struct fields')
       | DV1.DVALUE_Packed_struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Packed_struct fields')
       | DV1.DVALUE_Array elts =>
           elts' <- map_monad_In elts (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Array elts')
       | DV1.DVALUE_Vector elts =>
           elts' <- map_monad_In elts (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Vector elts')
       end.

  Program Fixpoint uvalue_convert_strict (uv1 : DV1.uvalue) {measure (DV1.uvalue_measure uv1)} : OOM DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.UVALUE_Addr a')
       | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
       | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
       | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
       | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
       | DV1.UVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.UVALUE_IPTR x')
       | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
       | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
       | DV1.UVALUE_Oom t => ret (DV2.UVALUE_Oom t)
       | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
       | DV1.UVALUE_None => ret DV2.UVALUE_None
       | DV1.UVALUE_Struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Struct fields')
       | DV1.UVALUE_Packed_struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Packed_struct fields')
       | DV1.UVALUE_Array elts =>
           elts' <- map_monad_In elts (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Array elts')
       | DV1.UVALUE_Vector elts =>
           elts' <- map_monad_In elts (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Vector elts')
       | DV1.UVALUE_Undef dt =>
           (* Could be a bit odd with intptr *)
           ret (DV2.UVALUE_Undef dt)
       | DV1.UVALUE_IBinop iop v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_IBinop iop v1' v2')
       | DV1.UVALUE_ICmp cmp v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_ICmp cmp v1' v2')
       | DV1.UVALUE_FBinop fop fm v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_FBinop fop fm v1' v2')
       | DV1.UVALUE_FCmp cmp v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_FCmp cmp v1' v2')
       | DV1.UVALUE_Conversion conv t_from v t_to =>
           v' <- uvalue_convert_strict v;;
           ret (DV2.UVALUE_Conversion conv t_from v' t_to)
       | DV1.UVALUE_GetElementPtr t ptrval idxs =>
           ptrval' <- uvalue_convert_strict ptrval;;
           idxs' <- map_monad_In idxs (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
       | DV1.UVALUE_ExtractElement t vec idx =>
           vec' <- uvalue_convert_strict vec;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_ExtractElement t vec' idx')
       | DV1.UVALUE_InsertElement t vec elt idx =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_InsertElement t vec' elt' idx')
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           vec1' <- uvalue_convert_strict vec1;;
           vec2' <- uvalue_convert_strict vec2;;
           idxmask' <- uvalue_convert_strict idxmask;;
           ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue t vec idxs =>
           vec' <- uvalue_convert_strict vec;;
           ret (DV2.UVALUE_ExtractValue t vec' idxs)
       | DV1.UVALUE_InsertValue t vec elt idxs =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
       | DV1.UVALUE_Select cnd v1 v2 =>
           cnd' <- uvalue_convert_strict cnd;;
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_Select cnd' v1' v2')
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           uv' <- uvalue_convert_strict uv;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
       | DV1.UVALUE_ConcatBytes uvs dt =>
           uvs' <- map_monad_In uvs (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_ConcatBytes uvs' dt)
       end.

  Opaque dvalue_convert_strict.
  Lemma dvalue_convert_strict_equation :
    forall dv,
      dvalue_convert_strict dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.DVALUE_Addr a')
        | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
        | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
        | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
        | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.DVALUE_IPTR x')
        | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
        | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
        | DV1.DVALUE_Oom t => ret (DV2.DVALUE_Oom t)
        | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
        | DV1.DVALUE_None => ret DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            fields' <- map_monad_In fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Struct fields')
        | DV1.DVALUE_Packed_struct fields =>
            fields' <- map_monad_In fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Packed_struct fields')
        | DV1.DVALUE_Array elts =>
            elts' <- map_monad_In elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Array elts')
        | DV1.DVALUE_Vector elts =>
            elts' <- map_monad_In elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Vector elts')
        end.
  Proof.
    intros dv.
    Transparent dvalue_convert_strict.
    unfold dvalue_convert_strict at 1.
    rewrite Wf.WfExtensionality.fix_sub_eq_ext.
    destruct dv; reflexivity.
  Qed.

  Lemma uvalue_convert_strict_equation:
    forall uv,
      uvalue_convert_strict uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.UVALUE_Addr a')
        | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
        | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
        | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
        | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.UVALUE_IPTR x')
        | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
        | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
        | DV1.UVALUE_Oom t => ret (DV2.UVALUE_Oom t)
        | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
        | DV1.UVALUE_None => ret DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            fields' <- map_monad_In fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Struct fields')
        | DV1.UVALUE_Packed_struct fields =>
            fields' <- map_monad_In fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Packed_struct fields')
        | DV1.UVALUE_Array elts =>
            elts' <- map_monad_In elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Array elts')
        | DV1.UVALUE_Vector elts =>
            elts' <- map_monad_In elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Vector elts')
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            ret (DV2.UVALUE_Undef dt)
        | DV1.UVALUE_IBinop iop v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_IBinop iop v1' v2')
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_ICmp cmp v1' v2')
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FBinop fop fm v1' v2')
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FCmp cmp v1' v2')
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            v' <- uvalue_convert_strict v;;
            ret (DV2.UVALUE_Conversion conv t_from v' t_to)
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            ptrval' <- uvalue_convert_strict ptrval;;
            idxs' <- map_monad_In idxs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
        | DV1.UVALUE_ExtractElement t vec idx =>
            vec' <- uvalue_convert_strict vec;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractElement t vec' idx')
        | DV1.UVALUE_InsertElement t vec elt idx =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_InsertElement t vec' elt' idx')
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            vec1' <- uvalue_convert_strict vec1;;
            vec2' <- uvalue_convert_strict vec2;;
            idxmask' <- uvalue_convert_strict idxmask;;
            ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
        | DV1.UVALUE_ExtractValue t vec idxs =>
            vec' <- uvalue_convert_strict vec;;
            ret (DV2.UVALUE_ExtractValue t vec' idxs)
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
        | DV1.UVALUE_Select cnd v1 v2 =>
            cnd' <- uvalue_convert_strict cnd;;
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_Select cnd' v1' v2')
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            uv' <- uvalue_convert_strict uv;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
        | DV1.UVALUE_ConcatBytes uvs dt =>
            uvs' <- map_monad_In uvs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_ConcatBytes uvs' dt)
        end.
  Proof.
    (* intros uv. *)
    (* Transparent uvalue_convert_strict. *)
    (* unfold uvalue_convert_strict at 1. *)
    (* Opaque uvalue_convert_strict. *)
    (* (* TODO: This is really slow *) *)
    (* rewrite Wf.WfExtensionality.fix_sub_eq_ext. *)
    (* destruct uv; reflexivity. *)
  Admitted.

  Definition dvalue_refine_strict (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop
    := dvalue_convert_strict dv1 = NoOom dv2.

  Definition uvalue_refine_strict (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop
    := uvalue_convert_strict uv1 = NoOom uv2.

  Lemma dvalue_refine_strict_equation :
    forall (dv1 : DV1.dvalue) (dv2 : DV2.dvalue),
      dvalue_refine_strict dv1 dv2 = (dvalue_convert_strict dv1 = NoOom dv2).
  Proof.
    intros dv1 dv2.
    reflexivity.
  Qed.

  Lemma uvalue_refine_strict_equation :
    forall (uv1 : DV1.uvalue) (uv2 : DV2.uvalue),
      uvalue_refine_strict uv1 uv2 = (uvalue_convert_strict uv1 = NoOom uv2).
  Proof.
    reflexivity.
  Qed.

  #[global] Opaque dvalue_convert_lazy.
  #[global] Opaque uvalue_convert_lazy.
  #[global] Opaque dvalue_refine_lazy.
  #[global] Opaque uvalue_refine_lazy.

  #[global] Opaque dvalue_convert_strict.
  #[global] Opaque uvalue_convert_strict.
  #[global] Opaque dvalue_refine_strict.
  #[global] Opaque uvalue_refine_strict.
End DVConvert.

Module DVConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) : DVConvert LP1 LP2 AC Events1 Events2.
  Include DVConvert LP1 LP2 AC Events1 Events2.
End DVConvertMake.

Module Type DVConvertSafe (LP1 : LLVMParams) (LP2 : LLVMParams) (AC1 : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR) (ACSafe : AddrConvertSafe LP1.ADDR LP2.ADDR AC1 AC2) (BIG_IP : INTPTR_BIG LP2.IP) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) (DVC1 : DVConvert LP1 LP2 AC1 Events1 Events2) (DVC2 : DVConvert LP2 LP1 AC2 Events2 Events1).
  Import ACSafe.
  Import BIG_IP.

  (* Lemma dvalue_convert_safe : *)
  (*   forall dv_i, *)
  (*   exists dv_f, *)
  (*     DVC1.dvalue_convert dv_i = NoOom dv_f /\ *)
  (*       DVC2.dvalue_convert dv_f = NoOom dv_i. *)
  (* Proof. *)
  (*   intros dv_i. *)
  (*   rewrite DVC1.dvalue_convert_equation. *)
  (*   induction dv_i; *)
  (*     try solve [eexists; split; auto]. *)
  (*   - (* Addresses *) *)
  (*     cbn. *)
  (*     pose proof (ACSafe.addr_convert_succeeds a) as [a2 ACSUC]. *)
  (*     rewrite ACSUC. *)
  (*     exists (DVC1.DV2.DVALUE_Addr a2). *)
  (*     rewrite (ACSafe.addr_convert_safe a); *)
  (*       auto. *)
  (*   - (* Intptr expressions... *) *)
  (*     cbn. *)
  (*     pose proof (from_Z_safe (LP1.IP.to_Z x)) as FZS. *)
  (*     destruct (LP2.IP.from_Z (LP1.IP.to_Z x)); inv FZS. *)
  (*     exists (DVC1.DV2.DVALUE_IPTR i). *)
  (*     split; auto. *)
  (*     (* TODO: Need to know something about the round trip of these intptr conversions :) *) *)
  (*     admit. *)
  (*   - (* Structures *) *)
  (*     induction fields. *)
  (*     + (* No fields *) *)
  (*       exists (DVC1.DV2.DVALUE_Struct []). *)
  (*       cbn. *)
  (*       split; auto. *)
  (*     + (* Fields *) *)
  (*       assert (In a (a :: fields)) as INA by (cbn; auto). *)
  (*       pose proof (H a INA) as HA. *)
  (*       destruct HA as [dv_a [CONV1_a CONV2_a]]. *)

  (*       rewrite map_monad_In_unfold. *)
  (*       rewrite DVC1.dvalue_convert_equation. *)
  (*       rewrite CONV1_a. *)
  (*       Opaque DVC1.dvalue_convert. *)
  (*       Opaque DVC2.dvalue_convert. *)
  (*       cbn. *)

  (*       destruct (map_monad_In fields (fun (x : DVC1.DV1.dvalue) (_ : In x fields) => DVC1.dvalue_convert x)) eqn:HMAPM. *)
  (*       -- (* Fields converted successfully *) *)
  (*         exists (DVC1.DV2.DVALUE_Struct (dv_a :: l)). *)
  (*         cbn; split; auto. *)

  (*         rewrite DVC2.dvalue_convert_equation. *)
  (*         cbn. *)
  (*         rewrite CONV2_a. *)
  (*         cbn. *)
  (*         admit. *)
  (*       -- (* OOM when converting fields, should be a contradiction. *)

  (*             Contradiction should arise from HMAPM returning OOM... *)

  (*             This means there exists u in fields, such that *)
  (*             dvalue_convert u returns OOM, but IHfields contradicts *)
  (*             that. *)
  (*           *) *)
  (*         admit. *)
  (* Admitted. *)
End DVConvertSafe.

Notation LLVM_syntax :=
  (list (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))).

Module EventConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR) (E1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (E2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  (* TODO: should this be a parameter? *)
  Module DVC := DVConvertMake LP1 LP2 AC E1 E2.
  Module DVCrev := DVConvertMake LP2 LP1 AC2 E2 E1.
  Import DVC.

  Definition L0_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L0 E2.L0.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e0)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e0)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* Globals *)
    { inversion e0.
      - (* Global write *)
        apply (dv <- lift_OOM (dvalue_convert dv);;
               trigger (GlobalWrite id dv)).
      - (* Global read *)
        apply (dv <- trigger (GlobalRead id);;
               lift_OOM (rev_dvalue_convert dv)).
    }

    (* Locals *)
    { inversion e0.
      - (* Local write *)
        apply (dv <- lift_OOM (uvalue_convert dv);;
               trigger (LocalWrite id dv)).
      - (* Local read *)
        apply (dv <- trigger (LocalRead id);;
               lift_OOM (rev_uvalue_convert dv)).
    }

    (* Stack *)
    { inversion e0.
      - (* Stack Push *)
        apply (args' <- lift_OOM
                         (map_monad_In args
                            (fun '(id, uv) Hin =>
                               uv' <- uvalue_convert uv;;
                               ret (id, uv')
                         ));;
               trigger (StackPush args')).
      - (* Stack Pop *)
        apply (trigger StackPop).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L1_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L1 E2.L1.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e0))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e0))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0))))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* Locals *)
    { inversion e0.
      - (* Local write *)
        apply (dv <- lift_OOM (uvalue_convert dv);;
               trigger (LocalWrite id dv)).
      - (* Local read *)
        apply (dv <- trigger (LocalRead id);;
               lift_OOM (rev_uvalue_convert dv)).
    }

    (* Stack *)
    { inversion e0.
      - (* Stack Push *)
        apply (args' <- lift_OOM
                         (map_monad_In args
                            (fun '(id, uv) Hin =>
                               uv' <- uvalue_convert uv;;
                               ret (id, uv')
                         ));;
               trigger (StackPush args')).
      - (* Stack Pop *)
        apply (trigger StackPop).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L2_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L2 E2.L2.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L3_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L3 E2.L3.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e0)))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L4_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L4 E2.L4.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                _
            | inr1 (inr1 (inl1 e0)) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 e0))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L5_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L5 E2.L5 := L4_convert_helper dvalue_convert uvalue_convert rev_dvalue_convert rev_uvalue_convert.

  Definition L6_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L6 E2.L6 := L5_convert_helper dvalue_convert uvalue_convert rev_dvalue_convert rev_uvalue_convert.

  Definition L0_convert_lazy : Handler E1.L0 E2.L0 := L0_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L1_convert_lazy : Handler E1.L1 E2.L1 := L1_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L2_convert_lazy : Handler E1.L2 E2.L2 := L2_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L3_convert_lazy : Handler E1.L3 E2.L3 := L3_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L4_convert_lazy : Handler E1.L4 E2.L4 := L4_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L5_convert_lazy : Handler E1.L5 E2.L5 := L5_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L6_convert_lazy : Handler E1.L6 E2.L6 := L6_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).

  Definition L0_convert_strict : Handler E1.L0 E2.L0 := L0_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L1_convert_strict : Handler E1.L1 E2.L1 := L1_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L2_convert_strict : Handler E1.L2 E2.L2 := L2_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L3_convert_strict : Handler E1.L3 E2.L3 := L3_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L4_convert_strict : Handler E1.L4 E2.L4 := L4_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L5_convert_strict : Handler E1.L5 E2.L5 := L5_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L6_convert_strict : Handler E1.L6 E2.L6 := L6_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
End EventConvert.

Module TreeConvert (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR).
  Module E1 := IS1.LP.Events.
  Module E2 := IS2.LP.Events.

  Module EC := EventConvert IS1.LP IS2.LP AC1 AC2 E1 E2.
  Import EC.
  Import EC.DVC.

  (** Converting trees with events in language 1 to trees with events in language 2 *)

  (* TODO: move this? *)
  Definition L0_convert_tree_lazy {T} (t : itree E1.L0 T) : itree E2.L0 T := interp L0_convert_lazy t.
  Definition L1_convert_tree_lazy {T} (t : itree E1.L1 T) : itree E2.L1 T := interp L1_convert_lazy t.
  Definition L2_convert_tree_lazy {T} (t : itree E1.L2 T) : itree E2.L2 T := interp L2_convert_lazy t.
  Definition L3_convert_tree_lazy {T} (t : itree E1.L3 T) : itree E2.L3 T := interp L3_convert_lazy t.
  Definition L4_convert_tree_lazy {T} (t : itree E1.L4 T) : itree E2.L4 T := interp L4_convert_lazy t.
  Definition L5_convert_tree_lazy {T} (t : itree E1.L5 T) : itree E2.L5 T := interp L5_convert_lazy t.
  Definition L6_convert_tree_lazy {T} (t : itree E1.L6 T) : itree E2.L6 T := interp L6_convert_lazy t.

  Definition L0_convert_tree_strict {T} (t : itree E1.L0 T) : itree E2.L0 T := interp L0_convert_strict t.
  Definition L1_convert_tree_strict {T} (t : itree E1.L1 T) : itree E2.L1 T := interp L1_convert_strict t.
  Definition L2_convert_tree_strict {T} (t : itree E1.L2 T) : itree E2.L2 T := interp L2_convert_strict t.
  Definition L3_convert_tree_strict {T} (t : itree E1.L3 T) : itree E2.L3 T := interp L3_convert_strict t.
  Definition L4_convert_tree_strict {T} (t : itree E1.L4 T) : itree E2.L4 T := interp L4_convert_strict t.
  Definition L5_convert_tree_strict {T} (t : itree E1.L5 T) : itree E2.L5 T := interp L5_convert_strict t.
  Definition L6_convert_tree_strict {T} (t : itree E1.L6 T) : itree E2.L6 T := interp L6_convert_strict t.

  #[global] Instance L0_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L0_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    unfold L0_convert_tree_lazy.
    eapply eutt_interp'.
    eauto.
  Defined.

  #[global] Instance L1_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L1_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L2_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L2_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L3_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L3_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L4_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L4_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L5_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L5_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L6_convert_tree_lazy_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L6_convert_tree_lazy.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L0_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L0_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    unfold L0_convert_tree_strict.
    eapply eutt_interp'.
    eauto.
  Defined.

  #[global] Instance L1_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L1_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L2_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L2_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L3_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L3_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L4_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L4_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L5_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L5_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  #[global] Instance L6_convert_tree_strict_eutt_proper {T} {RR : relation T} :
    Proper (eutt RR ==> eutt RR) L6_convert_tree_strict.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    eapply eutt_interp'; eauto.
  Defined.

  (* TODO: move this? *)
  Definition L0_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L0 A) : itree E2.L0 B
    := fmap f (L0_convert_tree_lazy t).

  Definition L1_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L1 A) : itree E2.L1 B
    := fmap f (L1_convert_tree_lazy t).

  Definition L2_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L2 A) : itree E2.L2 B
    := fmap f (L2_convert_tree_lazy t).

  Definition L3_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L3 A) : itree E2.L3 B
    := fmap f (L3_convert_tree_lazy t).

  Definition L4_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L4 A) : itree E2.L4 B
    := fmap f (L4_convert_tree_lazy t).

  Definition L5_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L5 A) : itree E2.L5 B
    := fmap f (L5_convert_tree_lazy t).

  Definition L6_convert_tree_lazy' {A B} (f : A -> B) (t : itree E1.L6 A) : itree E2.L6 B
    := fmap f (L6_convert_tree_lazy t).

  (* TODO: move this? *)
  Definition L0_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L0 A) : itree E2.L0 B
    := x <- L0_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L1_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L1 A) : itree E2.L1 B
    := x <- L1_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L2_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L2 A) : itree E2.L2 B
    := x <- L2_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L3_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L3 A) : itree E2.L3 B
    := x <- L3_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L4_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L4 A) : itree E2.L4 B
    := x <- L4_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L5_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L5 A) : itree E2.L5 B
    := x <- L5_convert_tree_strict t;;
       lift_OOM (f x).

  Definition L6_convert_tree_strict' {A B} (f : A -> OOM B) (t : itree E1.L6 A) : itree E2.L6 B
    := x <- L6_convert_tree_strict t;;
       lift_OOM (f x).

  #[global] Instance L0_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L0 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L0_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L0_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L0_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L1_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L1 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L1_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L1_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L1_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L2_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L2 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L2_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L2_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L2_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L3_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L3 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L3_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L3_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L3_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L4_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L4 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L4_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L4_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L4_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L5_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L5 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L5_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L5_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L5_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L6_convert_tree_lazy'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L6 _ _ RB (ret (f u1)) (ret (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L6_convert_tree_lazy' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L6_convert_tree_lazy'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L6_convert_tree_lazy_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L0_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L0 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L0_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L0_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L0_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L1_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L1 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L1_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L1_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L1_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L2_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L2 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L2_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L2_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L2_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L3_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L3 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L3_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L3_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L3_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L4_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L4 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L4_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L4_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L4_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L5_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L5 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L5_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L5_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L5_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  #[global] Instance L6_convert_tree_strict'_eutt_proper {A B} {RA : relation A} {RB : relation B} f :
    (forall u1 u2, RA u1 u2 -> @eutt E2.L6 _ _ RB (lift_OOM (f u1)) (lift_OOM (f u2))) ->
    Proper (eutt RA ==> eutt RB) (L6_convert_tree_strict' f).
  Proof.
    unfold Proper, respectful.
    intros F x y EQ.
    unfold L6_convert_tree_strict'.
    eapply eutt_clo_bind with (UU:=RA).
    eapply L6_convert_tree_strict_eutt_proper; eauto. (* Ugh, why can't I just rewrite? *)
    eauto.
  Defined.

  Definition convert_uvalue_tree_lazy {E} `{OOME -< E} (t : itree E E1.DV.uvalue) : itree E E2.DV.uvalue
    := fmap uvalue_convert_lazy t.

  Definition convert_dvalue_tree_lazy {E} `{OOME -< E} (t : itree E E1.DV.dvalue) : itree E E2.DV.dvalue
    := fmap dvalue_convert_lazy t.

  Definition convert_uvalue_tree_strict {E} `{OOME -< E} (t : itree E E1.DV.uvalue) : itree E E2.DV.uvalue
    := x <- t;;
       lift_OOM (uvalue_convert_strict x).

  Definition convert_dvalue_tree_strict {E} `{OOME -< E} (t : itree E E1.DV.dvalue) : itree E E2.DV.dvalue
    := x <- t;;
       lift_OOM (dvalue_convert_strict x).

  Definition L3_convert_PropT_lazy {A B} (RB : relation B) (f : A -> B) (ts : PropT E1.L3 A) : PropT E2.L3 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\
             refine_OOM_h RB
               (L3_convert_tree_lazy' f t_e1)
               t_e2.

  Definition L4_convert_PropT_lazy {A B} (RB : relation B) (f : A -> B) (ts : PropT IS1.LP.Events.L4 A) : PropT E2.L4 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\
             refine_OOM_h RB
               (L4_convert_tree_lazy' f t_e1)
               t_e2.

  Definition L5_convert_PropT_lazy {A B}
    (RB : relation B) (f : A -> B) (ts : PropT IS1.LP.Events.L5 A)
    : PropT E2.L5 B
    := L4_convert_PropT_lazy RB f ts.

  Definition L6_convert_PropT_lazy {A B}
    (RB : relation B) (f : A -> B) (ts : PropT IS1.LP.Events.L6 A)
    : PropT E2.L6 B
    := L4_convert_PropT_lazy RB f ts.

  Definition L3_convert_PropT_strict {A B} (RB : relation B) (f : A -> OOM B) (ts : PropT E1.L3 A) : PropT E2.L3 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\
             refine_OOM_h RB
               (L3_convert_tree_strict' f t_e1)
               t_e2.

  Definition L4_convert_PropT_strict {A B} (RB : relation B) (f : A -> OOM B) (ts : PropT IS1.LP.Events.L4 A) : PropT E2.L4 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\
             refine_OOM_h RB
               (L4_convert_tree_strict' f t_e1)
               t_e2.

  Definition L5_convert_PropT_strict {A B}
    (RB : relation B) (f : A -> OOM B) (ts : PropT IS1.LP.Events.L5 A)
    : PropT E2.L5 B
    := L4_convert_PropT_strict RB f ts.

  Definition L6_convert_PropT_strict {A B}
    (RB : relation B) (f : A -> OOM B) (ts : PropT IS1.LP.Events.L6 A)
    : PropT E2.L6 B
    := L4_convert_PropT_strict RB f ts.

End TreeConvert.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) (ACS : AddrConvertSafe IS2.LP.ADDR IS1.LP.ADDR AC2 AC1) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP).
  Import TLR.

  Module TC1 := TreeConvert IS1 IS2 AC1 AC2.
  Import TC1.
  Import EC.
  Import EC.DVC.
  Import ACS.
  Import IPS.

  (**  Converting state between the two languages *)

  Definition convert_global_env_lazy (g : IS1.LLVM.Global.global_env) : IS2.LLVM.Global.global_env
    := map (fun '(k, dv) => (k, dvalue_convert_lazy dv)) g.

  Definition convert_local_env_lazy (l : IS1.LLVM.Local.local_env) : IS2.LLVM.Local.local_env
    := map (fun '(k, uv) => (k, uvalue_convert_lazy uv)) l.

  Definition convert_global_env_strict (g : IS1.LLVM.Global.global_env) : OOM IS2.LLVM.Global.global_env
    := map_monad (fun '(k, dv) => dv' <- dvalue_convert_strict dv;;
                               ret (k, dv')) g.

  Definition convert_local_env_strict (l : IS1.LLVM.Local.local_env) : OOM IS2.LLVM.Local.local_env
    := map_monad (fun '(k, uv) => uv' <- uvalue_convert_strict uv;;
                               ret (k, uv')) l.

  Definition convert_stack_lazy (s : @stack IS1.LLVM.Local.local_env) : (@stack IS2.LLVM.Local.local_env)
    := map convert_local_env_lazy s.

  Definition convert_stack_strict (s : @stack IS1.LLVM.Local.local_env) : OOM (@stack IS2.LLVM.Local.local_env)
    := map_monad convert_local_env_strict s.

  (** Conversions between results at different levels of interpretation *)

  (* Ideally we would convert memstates / local envs / local stacks /
     global envs... But for now we can get away with placeholders for
     these because the refine_resX relations used by refine_LX ignores
     these.
   *)
  Definition res_L1_convert_lazy_unsafe (res : LLVM1.res_L1) : LLVM2.res_L1
    := match res with
       | (genv, dv) =>
           ([], dvalue_convert_lazy dv)
       end.

  Definition res_L2_convert_lazy_unsafe (res : LLVM1.res_L2) : LLVM2.res_L2
    := match res with
       | ((lenv, lstack), (genv, dv)) =>
           (([], []), ([], dvalue_convert_lazy dv))
       end.

  Definition res_L3_convert_lazy_unsafe (res : LLVM1.res_L3) : LLVM2.res_L3
    := match res with
       | (ms, (sid, ((lenv, lstack), (genv, dv)))) =>
           (IS2.MEM.MMEP.MMSP.initial_memory_state, (0, (([], []), ([], dvalue_convert_lazy dv))))
       end.

  Definition res_L4_convert_lazy_unsafe (res : LLVM1.res_L4) : LLVM2.res_L4
    := res_L3_convert_lazy_unsafe res.

  Definition res_L5_convert_lazy_unsafe (res : LLVM1.res_L5) : LLVM2.res_L5
    := res_L4_convert_lazy_unsafe res.

  Definition res_L6_convert_lazy_unsafe (res : LLVM1.res_L6) : LLVM2.res_L6
    := res_L5_convert_lazy_unsafe res.

  Definition res_L1_convert_strict_unsafe (res : LLVM1.res_L1) : OOM LLVM2.res_L1
    := match res with
       | (genv, dv) =>
           dv' <- dvalue_convert_strict dv;;
           ret ([], dv')
       end.

  Definition res_L2_convert_strict_unsafe (res : LLVM1.res_L2) : OOM LLVM2.res_L2
    := match res with
       | ((lenv, lstack), (genv, dv)) =>
           dv' <- dvalue_convert_strict dv;;
           ret (([], []), ([], dv'))
       end.

  Definition res_L3_convert_strict_unsafe (res : LLVM1.res_L3) : OOM LLVM2.res_L3
    := match res with
       | (ms, (sid, ((lenv, lstack), (genv, dv)))) =>
           dv' <- dvalue_convert_strict dv;;
           ret (IS2.MEM.MMEP.MMSP.initial_memory_state, (0, (([], []), ([], dv'))))
       end.

  Definition res_L4_convert_strict_unsafe (res : LLVM1.res_L4) : OOM LLVM2.res_L4
    := res_L3_convert_strict_unsafe res.

  Definition res_L5_convert_strict_unsafe (res : LLVM1.res_L5) : OOM LLVM2.res_L5
    := res_L4_convert_strict_unsafe res.

  Definition res_L6_convert_strict_unsafe (res : LLVM1.res_L6) : OOM LLVM2.res_L6
    := res_L5_convert_strict_unsafe res.

  (** Refinements between languages at different levels of interpretation *)

  Definition refine_E1E2_L0_lazy (src : itree E1.L0 E1.DV.dvalue) (tgt : itree E2.L0 E2.DV.dvalue) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L0 (L0_convert_tree_lazy' dvalue_convert_lazy src') tgt.

  Definition refine_E1E2_L1_lazy (src : itree E1.L1 LLVM1.res_L1) (tgt : itree E2.L1 LLVM2.res_L1) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L1 (L1_convert_tree_lazy' res_L1_convert_lazy_unsafe src) tgt.

  Definition refine_E1E2_L2_lazy (src : itree E1.L2 LLVM1.res_L2) (tgt : itree E2.L2 LLVM2.res_L2) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L2 (L2_convert_tree_lazy' res_L2_convert_lazy_unsafe src) tgt.

  Definition refine_E1E2_L3_lazy (srcs : PropT IS1.LP.Events.L3 LLVM1.res_L3) (tgts : PropT E2.L3 LLVM2.res_L3) : Prop
    := (* res_L3_convert_lazy_unsafe should be fine here because refine_L3
          ignores all of the placeholder values *)
    refine_L3 (L3_convert_PropT_lazy refine_res3 res_L3_convert_lazy_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L4_lazy (srcs : PropT IS1.LP.Events.L4 LLVM1.res_L4) (tgts : PropT E2.L4 LLVM2.res_L4) : Prop
    := (* res_L4_convert_lazy_unsafe should be fine here because refine_L4
          ignores all of the placeholder values *)
    refine_L4 (L4_convert_PropT_lazy refine_res3 res_L4_convert_lazy_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L5_lazy (srcs : PropT IS1.LP.Events.L5 LLVM1.res_L5) (tgts : PropT E2.L5 LLVM2.res_L5) : Prop
    := (* res_L5_convert_lazy_unsafe should be fine here because refine_L5
          ignores all of the placeholder values *)
    refine_L5 (L5_convert_PropT_lazy refine_res3 res_L5_convert_lazy_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L6_lazy (srcs : PropT IS1.LP.Events.L6 LLVM1.res_L6) (tgts : PropT E2.L6 LLVM2.res_L6) : Prop
    :=
    (* res_L4_convert_lazy_unsafe should be fine here because refine_L6
       ignores all of the placeholder values *)
    refine_L6 (L6_convert_PropT_lazy refine_res3 res_L6_convert_lazy_unsafe srcs) tgts.

  Definition refine_E1E2_L0_strict (src : itree E1.L0 E1.DV.dvalue) (tgt : itree E2.L0 E2.DV.dvalue) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L0 (L0_convert_tree_strict' dvalue_convert_strict src') tgt.

  Definition refine_E1E2_L1_strict (src : itree E1.L1 LLVM1.res_L1) (tgt : itree E2.L1 LLVM2.res_L1) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L1 (L1_convert_tree_strict' res_L1_convert_strict_unsafe src) tgt.

  Definition refine_E1E2_L2_strict (src : itree E1.L2 LLVM1.res_L2) (tgt : itree E2.L2 LLVM2.res_L2) : Prop
    := exists src',
      (* Need to allow for target to have more OOM than source *)
      refine_OOM_h eq src src' /\
        refine_L2 (L2_convert_tree_strict' res_L2_convert_strict_unsafe src) tgt.

  Definition refine_E1E2_L3_strict (srcs : PropT IS1.LP.Events.L3 LLVM1.res_L3) (tgts : PropT E2.L3 LLVM2.res_L3) : Prop
    := (* res_L3_convert_strict_unsafe should be fine here because refine_L3
          ignores all of the placeholder values *)
    refine_L3 (L3_convert_PropT_strict refine_res3 res_L3_convert_strict_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L4_strict (srcs : PropT IS1.LP.Events.L4 LLVM1.res_L4) (tgts : PropT E2.L4 LLVM2.res_L4) : Prop
    := (* res_L4_convert_strict_unsafe should be fine here because refine_L4
          ignores all of the placeholder values *)
    refine_L4 (L4_convert_PropT_strict refine_res3 res_L4_convert_strict_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L5_strict (srcs : PropT IS1.LP.Events.L5 LLVM1.res_L5) (tgts : PropT E2.L5 LLVM2.res_L5) : Prop
    := (* res_L5_convert_strict_unsafe should be fine here because refine_L5
          ignores all of the placeholder values *)
    refine_L5 (L5_convert_PropT_strict refine_res3 res_L5_convert_strict_unsafe (refine_OOM eq srcs)) tgts.

  Definition refine_E1E2_L6_strict (srcs : PropT IS1.LP.Events.L6 LLVM1.res_L6) (tgts : PropT E2.L6 LLVM2.res_L6) : Prop
    :=
    (* res_L4_convert_strict_unsafe should be fine here because refine_L6
       ignores all of the placeholder values *)
    refine_L6 (L6_convert_PropT_strict refine_res3 res_L6_convert_strict_unsafe srcs) tgts.

  (** Refinement between states *)

  Definition alist_refine {K V1 V2} `{RD_K : RelDec.RelDec K} (R: V1 -> V2 -> Prop) (m1 : FMapAList.alist K V1) (m2 : FMapAList.alist K V2) :=
    (forall k,
        (exists v1, FMapAList.alist_find k m1 = Some v1) <->
          (exists v2, FMapAList.alist_find k m2 = Some v2)) /\
      (forall k v1 v2,
          FMapAList.alist_find k m1 = Some v1 ->
          FMapAList.alist_find k m2 = Some v2 ->
          R v1 v2).

  Lemma alist_refine_empty {K V1 V2} `{RD_K : RelDec.RelDec K} (R: V1 -> V2 -> Prop) :
    alist_refine R [] [].
  Proof.
    red.
    split.
    { intros k.
      split; intros [dv CONTRA];
        cbn in *; inv CONTRA.
    }

    { intros k dv1 dv2 CONTRA1 CONTRA2.
      inv CONTRA1.
    }
  Qed.

  Lemma alist_refine_cons :
    forall {K V1 V2}
      `{RD_K : @RelDec.RelDec K (@eq K)}
      `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K}
      (R: V1 -> V2 -> Prop) xs ys x y,
      fst x = fst y ->
      R (snd x) (snd y) ->
      alist_refine R xs ys ->
      alist_refine R (x :: xs) (y :: ys).
  Proof.
    intros K V1 V2 RD_K RD_K_CORRECT R.
    induction xs, ys; intros x y H H0 H1.
    - destruct x, y.
      cbn in *.
      split.
      intros k1.

      split; intros FIND.
      + destruct FIND as [v1 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        cbn.
        rewrite Heqb.
        exists v0.
        reflexivity.
      + destruct FIND as [v1 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        cbn.
        rewrite Heqb.
        exists v.
        reflexivity.
      + intros k1 v1 v2 H2 H3.
        cbn in H2, H3.
        break_match_hyp; inv H3.
        break_match_hyp; inv H2.
        auto.
    - destruct x, y.
      cbn in *.
      split.
      intros k1.

      split; intros FIND.
      + destruct FIND as [v1 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        cbn.
        rewrite Heqb.
        exists v0.
        reflexivity.
      + destruct p.
        destruct FIND as [v2 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        * exists v.
          cbn.
          rewrite Heqb.
          reflexivity.
        * break_match_hyp; inv H3.
          -- exfalso.
             red in H1. destruct H1 as [[H1 H1'] H2].
             cbn in *.
             rewrite Heqb0 in H1'.
             forward H1'.
             exists v2; auto.
             destruct H1' as [v1 CONTRA].
             inv CONTRA.
          -- exfalso.
             red in H1. destruct H1 as [[H1 H1'] H3].
             cbn in *.
             rewrite Heqb0 in H1'.
             forward H1'.
             exists v2; auto.
             destruct H1' as [v1' CONTRA].
             inv CONTRA.
      + destruct p; subst.
        intros k v2 v3 H2 H3.
        cbn in H2, H3.
        break_match_hyp; inv H2.
        inv H3.
        auto.
    - destruct x, y, a.
      cbn in *; subst.
      split.
      intros k.

      split; intros FIND.
      + destruct FIND as [v2 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        * cbn.
          rewrite Heqb.
          exists v0.
          reflexivity.
        * break_match_hyp; inv H2.
          -- exfalso.
             red in H1. destruct H1 as [[H1 H1'] H2].
             cbn in *.
             rewrite Heqb0 in H1.
             forward H1.
             eexists; auto.
             destruct H1 as [v2' CONTRA].
             inv CONTRA.
          -- exfalso.
             red in H1. destruct H1 as [[H1 H1'] H2].
             cbn in *.
             rewrite Heqb0 in H1.
             rewrite H3 in H1.
             forward H1.
             eexists; auto.
             destruct H1 as [v2' CONTRA].
             inv CONTRA.
      + destruct FIND as [v2 FIND].
        cbn in FIND.
        break_match_hyp; inv FIND.
        cbn.
        rewrite Heqb.
        eexists; auto.
      + intros k v2 v3 H2 H3.
        cbn in H2, H3.
        break_match_hyp; inv H3.
        inv H2.
        auto.
    - pose proof IHxs ys a p as IH.
      destruct x, y, a, p; cbn in *; subst.
      red.
      split.
      + intros k.
        split; intros FIND.
        * cbn in *.
          break_match_hyp; inv FIND;
            try solve [eexists; auto].

          break_match_hyp; inv H.
          -- break_match_goal.
             eexists; auto.

             red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1.
             rewrite Heqb0 in H1'.
             destruct H1 as [H1a H1b].
             forward H1a.
             eexists; auto.
             rewrite Heqb1 in H1a.
             auto.
          -- break_match_goal.
             eexists; auto.

             red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1.
             rewrite Heqb0 in H1'.
             destruct H1 as [H1a H1b].
             forward H1a.
             eexists; eauto.
             rewrite Heqb1 in H1a.
             auto.
        * cbn in *.
          break_match_hyp; inv FIND;
            try solve [eexists; auto].

          break_match_hyp; inv H.
          -- break_match_goal.
             eexists; auto.

             red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             destruct H1 as [H1a H1b].
             forward H1b.
             eexists; auto.
             auto.
          -- break_match_goal.
             eexists; auto.

             red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             destruct H1 as [H1a H1b].
             eapply H1b.
             eexists; eauto.
      + intros k v3 v4 H H2.
        cbn in *.
        break_match_hyp; inv H; inv H2; auto.
        break_match_hyp; inv H3.
        * break_match_hyp; inv H4.
          -- forward IH.
             pose proof (@RelDec.rel_dec_correct _ _ RD_K RD_K_CORRECT k k1) as [KK1 _].
             pose proof (@RelDec.rel_dec_correct _ _ RD_K RD_K_CORRECT k k2) as [KK2 _].
             rewrite <- KK1, KK2; auto.

             red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             eauto.
          -- red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             eauto.
        * break_match_hyp; inv H4.
          -- red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             eauto.
          -- red in H1.
             destruct H1 as [H1 H1'].
             cbn in *.
             specialize (H1 k).
             specialize (H1' k).
             rewrite Heqb0 in H1, H1'.
             rewrite Heqb1 in H1, H1'.
             eauto.
  Qed.

  (* Not sure if this is right...

     Presumably if [g1] OOMs when converted, we wouldn't have a [g2]
     anyway?
   *)
  Definition global_refine_lazy (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_lazy g1 g2.

  Lemma global_refine_lazy_empty :
    global_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Definition global_refine_strict (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_strict g1 g2.

  Lemma global_refine_strict_empty :
    global_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Definition local_refine_lazy (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_lazy l1 l2.

  Lemma local_refine_lazy_empty :
    local_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Definition local_refine_strict (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_strict l1 l2.

  Lemma local_refine_strict_empty :
    local_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Definition stack_refine_lazy (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_lazy s1 s2.

  Lemma stack_refine_lazy_empty :
    stack_refine_lazy [] [].
  Proof.
    constructor.
  Qed.

  Definition stack_refine_strict (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_strict s1 s2.

  Lemma stack_refine_strict_empty :
    stack_refine_strict [] [].
  Proof.
    constructor.
  Qed.

  Definition local_stack_refine_lazy
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_lazy l1 l2 /\ stack_refine_lazy s1 s2
    end.

  Lemma local_stack_refine_lazy_empty :
    local_stack_refine_lazy ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_lazy_empty.
    apply stack_refine_lazy_empty.
  Qed.

  Definition local_stack_refine_strict
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_strict l1 l2 /\ stack_refine_strict s1 s2
    end.

  Lemma local_stack_refine_strict_empty :
    local_stack_refine_strict ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_strict_empty.
    apply stack_refine_strict_empty.
  Qed.

  (** OOM Refinements *)
  (* Lemma Returns_uvalue_convert_L1_L2 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma Returns_uvalue_convert_L0 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns E2.L0 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L0 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma Returns_uvalue_convert_L3 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns E2.L3 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L3 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma refine_OOM_h_L0_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L0_convert_tree x_inf) (L0_convert_tree y_inf). *)
  (* Proof. *)
  (*   (* intros T. *) *)

  (*   (* unfold refine_OOM_h, L0_convert_tree, refine_OOM_h_flip. *) *)
  (*   (* intros. *) *)
  (*   (* rewrite (unfold_interp y_inf). *) *)
  (*   (* rewrite (unfold_interp x_inf). *) *)
  (*   (* cbn. *) *)

  (*   (* match goal with *) *)
  (*   (* | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0 *) *)
  (*   (* end. *) *)

  (*   (* assert (i ≅ _interp EC.L0_convert (observe y_inf)). { *) *)
  (*   (*   rewrite Heqi. reflexivity. *) *)
  (*   (* } clear Heqi. *) *)
  (*   (* remember (_interp EC.L0_convert (observe x_inf)). *) *)
  (*   (* assert (i0 ≅ _interp EC.L0_convert (observe x_inf)). { *) *)
  (*   (*   subst; reflexivity. *) *)
  (*   (* } clear Heqi1 Heqi0. *) *)
  (*   (* revert x_inf y_inf H i i0 H0 H1. *) *)

  (*   (* pcofix CIH. *) *)

  (*   (* intros * H. *) *)
  (*   (* punfold H; red in H. *) *)
  (*   (* remember (observe y_inf) as oy; remember (observe x_inf) as ox. *) *)
  (*   (* clear Heqoy Heqox. *) *)

  (*   (* induction H; pclearbot; intros; subst; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *) *)
  (*   (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *) *)
  (*   (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)

  (*   (*   right; eapply CIH; eauto; *) *)
  (*   (*   rewrite unfold_interp in H1, H2; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; *) *)
  (*   (*     try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (*   rewrite unfold_interp in H1. *) *)
  (*   (*   specialize (IHinterp_PropTF _ _ H1 H2). *) *)

  (*   (*   punfold IHinterp_PropTF. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i0) eqn: Heqi; *) *)
  (*   (*     try apply eqit_inv in H2; cbn in H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (*   rewrite unfold_interp in H2. *) *)
  (*   (*   specialize (IHinterp_PropTF _ _ H1 H2). *) *)

  (*   (*   punfold IHinterp_PropTF. *) *)
  (*   (* - pstep. apply bisimulation_is_eq in HT1. *) *)
  (*   (*   rewrite HT1 in H1. cbn in H1. *) *)
  (*   (*   destruct (resum IFun A e). *) *)
  (*   (*   cbn in H1. *) *)
  (*   (*   repeat setoid_rewrite bind_vis in H1. *) *)
  (*   (*   apply bisimulation_is_eq in H1. rewrite H1. *) *)
  (*   (*   econstructor; eauto. *) *)
  (*   (*   eapply eqit_Vis; intros; inv u. *) *)
  (*   (* - pstep. cbn in H2, H3. red in H. *) *)
  (*   (*   rewrite H in H0. *) *)
  (*   (*   rename H2 into H1. *) *)
  (*   (*   rename H3 into H2. *) *)

  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   repeat destruct e; cbn in *. *) *)
  (*   (*   + rewrite bind_bind in H1. *) *)
  (*   (*     unfold lift_OOM in H1. *) *)
  (*   (*     rename H0 into KS. rewrite bind_trigger in KS. *) *)
  (*   (*     cbn in *. *) *)
  (*   (*     destruct (EC.DVC.uvalue_convert f) eqn : Hf. *) *)
  (*   (*     { rewrite bind_ret_l, bind_bind in H1. *) *)
  (*   (*       destruct *) *)
  (*   (*         (map_monad_In args *) *)
  (*   (*           (fun (elt : E1.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm. *) *)
  (*   (*       { rewrite bind_ret_l, bind_bind in H1. *) *)
  (*   (*         rewrite bind_trigger in H1. *) *)

  (*   (*         destruct (observe i) eqn: Heqi; *) *)
  (*   (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*         red. *) *)
  (*   (*         setoid_rewrite Heqi. *) *)
  (*   (*         destruct H1 as (?&?&?). *) *)
  (*   (*         dependent destruction x. *) *)
  (*   (*         red in H, H0. *) *)
  (*   (*         econstructor; [ constructor | ..]; eauto; cycle 1. *) *)
  (*   (*         - red; reflexivity. *) *)
  (*   (*         - cbn in *. *) *)
  (*   (*           rewrite <- unfold_interp in H2. *) *)
  (*   (*           rewrite <- itree_eta in H2. *) *)
  (*   (*           rewrite H2. rewrite KS. rewrite interp_vis. cbn. *) *)
  (*   (*           rewrite bind_bind. unfold lift_OOM. *) *)
  (*   (*           rewrite Hf. setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. rewrite Hm. *) *)
  (*   (*           setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. *) *)
  (*   (*           setoid_rewrite bind_trigger. *) *)
  (*   (*           unfold subevent. rewrite H0. *) *)
  (*   (*           eapply eqit_Vis. intros. *) *)
  (*   (*           Unshelve. *) *)
  (*   (*           3 : exact (fun u0 : E2.DV.dvalue => *) *)
  (*   (*           ITree.bind match EC.DVCrev.dvalue_convert u0 with *) *)
  (*   (*                     | NoOom a0 => ret a0 *) *)
  (*   (*                     | Oom s => raise_oom s *) *)
  (*   (*                      end (fun x1 : E1.DV.dvalue => Tau (interp EC.L0_convert (k2 x1)))). *) *)
  (*   (*           reflexivity. intros. inv H. *) *)
  (*   (*         - cbn. red in H1. subst. *) *)
  (*   (*           eapply bisimulation_is_eq in H1. rewrite H1. *) *)

  (*   (*           destruct (EC.DVCrev.dvalue_convert a) eqn: Ht. *) *)
  (*   (*           + setoid_rewrite H in HK. subst. *) *)
  (*   (*             eapply Returns_uvalue_convert_L0 in H3; eauto. *) *)
  (*   (*             specialize (HK _ H3). pclearbot. *) *)
  (*   (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ. *) *)
  (*   (*             pstep; constructor; eauto. right; eauto. *) *)
  (*   (*             eapply CIH; try rewrite <- unfold_interp; try reflexivity. *) *)
  (*   (*             eapply HK. *) *)
  (*   (*           + setoid_rewrite H in HK. subst. *) *)
  (*   (*             unfold raiseOOM. *) *)
  (*   (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pstep; econstructor; eauto. unfold subevent. *) *)
  (*   (*             reflexivity. } *) *)
  (*   (*       { unfold raiseOOM in H1. rewrite bind_trigger in H1. *) *)
  (*   (*         red. destruct (observe i) eqn: Heqi; *) *)
  (*   (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*         destruct H1 as (?&?&?). *) *)
  (*   (*         dependent destruction x. *) *)
  (*   (*         red in H, H0. *) *)
  (*   (*         (* rewrite H1. *) *) *)
  (*   (*         econstructor; eauto. *) *)
  (*   (*         - intros. inv a. *) *)
  (*   (*         - red; reflexivity. *) *)
  (*   (*         - cbn in *. rewrite <- itree_eta in H2. *) *)
  (*   (*           rewrite H2. rewrite <- unfold_interp. *) *)
  (*   (*           rewrite KS. rewrite interp_vis. cbn. *) *)
  (*   (*           rewrite bind_bind. unfold lift_OOM. *) *)
  (*   (*           rewrite Hf. setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. rewrite Hm. *) *)
  (*   (*           setoid_rewrite bind_trigger. *) *)
  (*   (*           setoid_rewrite bind_vis. *) *)
  (*   (*           unfold subevent. rewrite H0. *) *)
  (*   (*           eapply eqit_Vis. intros. inv u0. } } *) *)

  (*   (*       unfold raiseOOM in H1. rewrite bind_trigger in H1. *) *)
  (*   (*       red. destruct (observe i) eqn: Heqi; *) *)
  (*   (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*       destruct H1 as (?&?&?). *) *)
  (*   (*       dependent destruction x. *) *)
  (*   (*       red in H, H0. cbn in *. *) *)
  (*   (*       econstructor; eauto. *) *)
  (*   (*     * intros. inv a. *) *)
  (*   (*     * red; reflexivity. *) *)
  (*   (*     * rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*       rewrite <- unfold_interp. rewrite KS. *) *)
  (*   (*       rewrite interp_vis. *) *)
  (*   (*       cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf. *) *)
  (*   (*       setoid_rewrite bind_trigger. *) *)
  (*   (*       setoid_rewrite bind_vis. *) *)
  (*   (*       unfold subevent. rewrite H0. *) *)
  (*   (*       eapply eqit_Vis. intros. inv u. *) *)
  (*   (*   + destruct s. *) *)
  (*   (*     { (* Intrinsic *) *) *)
  (*   (*       admit. *) *)
  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     { (* Globals *) *) *)
  (*   (*       admit. *) *)
  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     { (* Locals + Stack *) *) *)
  (*   (*       admit. *) *)
  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     { (* Memory *) *) *)
  (*   (*       admit. *) *)
  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     { (* Pick *) *) *)
  (*   (*       admit. *) *)
  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     * unfold raiseOOM in H1. *) *)
  (*   (*       destruct o. *) *)
  (*   (*       cbn in H1. *) *)
  (*   (*       rewrite bind_bind, bind_trigger in H1. *) *)
  (*   (*       rewrite itree_eta in H1, H2. *) *)
  (*   (*       red. *) *)
  (*   (*       destruct (observe i) eqn: Heqi; *) *)
  (*   (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*       destruct H1 as (?&?&?). *) *)
  (*   (*       dependent destruction x. *) *)
  (*   (*       red in H, H0. cbn in *. *) *)
  (*   (*       econstructor; eauto. *) *)
  (*   (*       -- intros. inv a. *) *)
  (*   (*       -- red; reflexivity. *) *)
  (*   (*       -- rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*          rewrite <- unfold_interp. rewrite H0. *) *)
  (*   (*          rewrite bind_trigger. *) *)
  (*   (*          rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger. *) *)
  (*   (*          rewrite bind_vis. subst. *) *)
  (*   (*          apply eqit_Vis; intros; inv u. *) *)
  (*   (*     * destruct s; try destruct u; cbn in H1. *) *)
  (*   (*       -- repeat red in HTA. *) *)
  (*   (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *) *)
  (*   (*           red. *) *)
  (*   (*           destruct (observe i) eqn: Heqi; *) *)
  (*   (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*           destruct H1 as (?&?&?). *) *)
  (*   (*           dependent destruction x. *) *)
  (*   (*           red in H, H0. *) *)
  (*   (*           econstructor; eauto. *) *)
  (*   (*           repeat red. intros. inv a. *) *)
  (*   (*           red; reflexivity. *) *)
  (*   (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*           rewrite <- unfold_interp. *) *)
  (*   (*           rewrite H0. rewrite bind_trigger. *) *)
  (*   (*           rewrite interp_vis. *) *)
  (*   (*           cbn. *) *)
  (*   (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *) *)
  (*   (*           intros. inv u. *) *)
  (*   (*       -- destruct s; try destruct u; cbn in H1. *) *)
  (*   (*          ++ destruct d. cbn in H1. *) *)
  (*   (*             rewrite <- unfold_interp in H2. *) *)

  (*   (*             rename H0 into KS. *) *)
  (*   (*             setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             setoid_rewrite bind_trigger in KS. *) *)

  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. subst. *) *)
  (*   (*             assert (Returns tt ta). *) *)
  (*   (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *) *)
  (*   (*               unfold subevent. reflexivity. *) *)
  (*   (*               constructor; reflexivity. } *) *)
  (*   (*             specialize (HK _ H0). pclearbot. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             ** intros. red in H1. specialize (H1 tt). *) *)
  (*   (*                eapply bisimulation_is_eq in H1. destruct a. *) *)
  (*   (*                rewrite H1. *) *)
  (*   (*                right; eapply CIH. *) *)
  (*   (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *) *)
  (*   (*                pstep; econstructor; eauto. punfold HK. *) *)
  (*   (*                rewrite <- unfold_interp. Unshelve. *) *)
  (*   (*                16 : exact (fun x => interp EC.L0_convert (k2 x)). reflexivity. *) *)
  (*   (*                all : shelve. *) *)
  (*   (*             ** red; reflexivity. *) *)
  (*   (*             ** rewrite <- itree_eta in H2. *) *)
  (*   (*                rewrite H2. rewrite KS. *) *)
  (*   (*                rewrite interp_vis. cbn. unfold debug. *) *)
  (*   (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *) *)
  (*   (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *) *)
  (*   (*          ++ repeat red in HTA. *) *)
  (*   (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. cbn in *; subst. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             intros. inv a. *) *)
  (*   (*             red; reflexivity. *) *)
  (*   (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*             rewrite <- unfold_interp. *) *)
  (*   (*             rewrite H0. cbn. rewrite interp_bind. *) *)
  (*   (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *) *)
  (*   (*             do 2 rewrite bind_trigger. rewrite bind_vis. *) *)
  (*   (*             apply eqit_Vis; intros; inv u. *) *)

  (*   (*             Unshelve. *) *)
  (*   (*             all : eauto. *) *)
  (*   (*             all : inv x. *) *)
  (* Admitted. *)

  (* Lemma refine_OOM_h_L1_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L1_convert_tree x_inf) (L1_convert_tree y_inf). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma refine_OOM_h_L2_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L2_convert_tree x_inf) (L2_convert_tree y_inf). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma refine_OOM_h_L3_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L3_convert_tree x_inf) (L3_convert_tree y_inf). *)
  (* Proof. *)
  (*   (* intros T. *) *)

  (*   (* unfold refine_OOM_h, L3_convert_tree, refine_OOM_h_flip. *) *)
  (*   (* intros. *) *)
  (*   (* rewrite (unfold_interp y_inf). *) *)
  (*   (* rewrite (unfold_interp x_inf). *) *)
  (*   (* cbn. *) *)

  (*   (* match goal with *) *)
  (*   (* | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0 *) *)
  (*   (* end. *) *)

  (*   (* assert (i ≅ _interp EC.L3_convert (observe y_inf)). { *) *)
  (*   (*   rewrite Heqi. reflexivity. *) *)
  (*   (* } clear Heqi. *) *)
  (*   (* remember (_interp EC.L3_convert (observe x_inf)). *) *)
  (*   (* assert (i0 ≅ _interp EC.L3_convert (observe x_inf)). { *) *)
  (*   (*   subst; reflexivity. *) *)
  (*   (* } clear Heqi1 Heqi0. *) *)
  (*   (* revert x_inf y_inf H i i0 H0 H1. *) *)

  (*   (* pcofix CIH. *) *)

  (*   (* intros * H. *) *)
  (*   (* punfold H; red in H. *) *)
  (*   (* remember (observe y_inf) as oy; remember (observe x_inf) as ox. *) *)
  (*   (* clear Heqoy Heqox. *) *)

  (*   (* induction H; pclearbot; intros; subst; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *) *)
  (*   (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *) *)
  (*   (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)

  (*   (*   right; eapply CIH; eauto; *) *)
  (*   (*   rewrite unfold_interp in H1, H2; auto. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i) eqn: Heqi; *) *)
  (*   (*     try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (*   rewrite unfold_interp in H1. *) *)
  (*   (*   specialize (IHinterp_PropTF _ _ H1 H2). *) *)

  (*   (*   punfold IHinterp_PropTF. *) *)
  (*   (* - pstep. cbn in H1, H2. *) *)
  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   red. *) *)
  (*   (*   destruct (observe i0) eqn: Heqi; *) *)
  (*   (*     try apply eqit_inv in H2; cbn in H2; try contradiction; auto. *) *)
  (*   (*   subst; constructor; auto. *) *)
  (*   (*   rewrite unfold_interp in H2. *) *)
  (*   (*   specialize (IHinterp_PropTF _ _ H1 H2). *) *)

  (*   (*   punfold IHinterp_PropTF. *) *)
  (*   (* - pstep. apply bisimulation_is_eq in HT1. *) *)
  (*   (*   rewrite HT1 in H1. cbn in H1. *) *)
  (*   (*   destruct (resum IFun A e). *) *)
  (*   (*   cbn in H1. *) *)
  (*   (*   repeat setoid_rewrite bind_vis in H1. *) *)
  (*   (*   apply bisimulation_is_eq in H1. rewrite H1. *) *)
  (*   (*   econstructor; eauto. *) *)
  (*   (*   eapply eqit_Vis; intros; inv u. *) *)
  (*   (* - pstep. cbn in H2, H3. red in H. *) *)
  (*   (*   rewrite H in H0. *) *)
  (*   (*   rename H2 into H1. *) *)
  (*   (*   rename H3 into H2. *) *)

  (*   (*   rewrite itree_eta in H1, H2. *) *)
  (*   (*   repeat destruct e; cbn in *. *) *)
  (*   (*   + rewrite bind_bind in H1. *) *)
  (*   (*     unfold lift_OOM in H1. *) *)
  (*   (*     rename H0 into KS. rewrite bind_trigger in KS. *) *)
  (*   (*     cbn in *. *) *)
  (*   (*     destruct (EC.DVC.uvalue_convert f) eqn : Hf. *) *)
  (*   (*     { rewrite bind_ret_l, bind_bind in H1. *) *)
  (*   (*       destruct *) *)
  (*   (*         (map_monad_In args *) *)
  (*   (*           (fun (elt : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm. *) *)
  (*   (*       { rewrite bind_ret_l, bind_bind in H1. *) *)
  (*   (*         rewrite bind_trigger in H1. *) *)

  (*   (*         destruct (observe i) eqn: Heqi; *) *)
  (*   (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*         red. *) *)
  (*   (*         setoid_rewrite Heqi. *) *)
  (*   (*         destruct H1 as (?&?&?). *) *)
  (*   (*         dependent destruction x. *) *)
  (*   (*         red in H, H0. *) *)
  (*   (*         econstructor; [ constructor | ..]; eauto; cycle 1. *) *)
  (*   (*         - red; reflexivity. *) *)
  (*   (*         - cbn in *. *) *)
  (*   (*           rewrite <- unfold_interp in H2. *) *)
  (*   (*           rewrite <- itree_eta in H2. *) *)
  (*   (*           rewrite H2. rewrite KS. rewrite interp_vis. cbn. *) *)
  (*   (*           rewrite bind_bind. unfold lift_OOM. *) *)
  (*   (*           rewrite Hf. setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. rewrite Hm. *) *)
  (*   (*           setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. *) *)
  (*   (*           setoid_rewrite bind_trigger. *) *)
  (*   (*           unfold subevent. rewrite H0. *) *)
  (*   (*           eapply eqit_Vis. intros. *) *)
  (*   (*           Unshelve. *) *)
  (*   (*           3 : exact (fun u0 : E2.DV.dvalue => *) *)
  (*   (*           ITree.bind match EC.DVCrev.dvalue_convert u0 with *) *)
  (*   (*                     | NoOom a0 => ret a0 *) *)
  (*   (*                     | Oom s => raise_oom s *) *)
  (*   (*                      end (fun x1 : E1.DV.dvalue => Tau (interp EC.L3_convert (k2 x1)))). *) *)
  (*   (*           reflexivity. intros. inv H. *) *)
  (*   (*         - cbn. red in H1. subst. *) *)
  (*   (*           eapply bisimulation_is_eq in H1. rewrite H1. *) *)

  (*   (*           destruct (EC.DVCrev.dvalue_convert a) eqn: Ht. *) *)
  (*   (*           + setoid_rewrite H in HK. subst. *) *)
  (*   (*             rewrite subevent_subevent in H3. *) *)
  (*   (*             eapply Returns_uvalue_convert_L3 in H3; eauto. *) *)
  (*   (*             specialize (HK _ H3). pclearbot. *) *)
  (*   (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ. *) *)
  (*   (*             pstep; constructor; eauto. right; eauto. *) *)
  (*   (*             eapply CIH; try rewrite <- unfold_interp; try reflexivity. *) *)
  (*   (*             eapply HK. *) *)
  (*   (*           + setoid_rewrite H in HK. subst. *) *)
  (*   (*             unfold raiseOOM. *) *)
  (*   (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *) *)
  (*   (*             pstep; econstructor; eauto. unfold subevent. *) *)
  (*   (*             reflexivity. } *) *)
  (*   (*       { unfold raiseOOM in H1. rewrite bind_trigger in H1. *) *)
  (*   (*         red. destruct (observe i) eqn: Heqi; *) *)
  (*   (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*         destruct H1 as (?&?&?). *) *)
  (*   (*         dependent destruction x. *) *)
  (*   (*         red in H, H0. *) *)
  (*   (*         (* rewrite H1. *) *) *)
  (*   (*         econstructor; eauto. *) *)
  (*   (*         - intros. inv a. *) *)
  (*   (*         - red; reflexivity. *) *)
  (*   (*         - cbn in *. rewrite <- itree_eta in H2. *) *)
  (*   (*           rewrite H2. rewrite <- unfold_interp. *) *)
  (*   (*           rewrite KS. rewrite interp_vis. cbn. *) *)
  (*   (*           rewrite bind_bind. unfold lift_OOM. *) *)
  (*   (*           rewrite Hf. setoid_rewrite bind_ret_l. *) *)
  (*   (*           setoid_rewrite bind_bind. rewrite Hm. *) *)
  (*   (*           setoid_rewrite bind_trigger. *) *)
  (*   (*           setoid_rewrite bind_vis. *) *)
  (*   (*           unfold subevent. rewrite H0. *) *)
  (*   (*           eapply eqit_Vis. intros. inv u0. } } *) *)

  (*   (*       unfold raiseOOM in H1. rewrite bind_trigger in H1. *) *)
  (*   (*       red. destruct (observe i) eqn: Heqi; *) *)
  (*   (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*       destruct H1 as (?&?&?). *) *)
  (*   (*       dependent destruction x. *) *)
  (*   (*       red in H, H0. cbn in *. *) *)
  (*   (*       econstructor; eauto. *) *)
  (*   (*     * intros. inv a. *) *)
  (*   (*     * red; reflexivity. *) *)
  (*   (*     * rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*       rewrite <- unfold_interp. rewrite KS. *) *)
  (*   (*       rewrite interp_vis. *) *)
  (*   (*       cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf. *) *)
  (*   (*       setoid_rewrite bind_trigger. *) *)
  (*   (*       setoid_rewrite bind_vis. *) *)
  (*   (*       unfold subevent. rewrite H0. *) *)
  (*   (*       eapply eqit_Vis. intros. inv u. *) *)
  (*   (*   + destruct s. *) *)
  (*   (*     { destruct p. *) *)
  (*   (*       cbn in *. *) *)
  (*   (*       destruct (EC.DVC.uvalue_convert x) eqn:Ht. *) *)
  (*   (*       - cbn in *. *) *)
  (*   (*         rewrite bind_ret_l in H1. *) *)
  (*   (*         rewrite bind_trigger in H1. *) *)
  (*   (*         rewrite bind_vis in H1. *) *)
  (*   (*         red. *) *)
  (*   (*         destruct (observe i) eqn: Heqi; *) *)
  (*   (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*         destruct H1 as (?&?&?). *) *)
  (*   (*         cbn in *. *) *)
  (*   (*         dependent destruction x. *) *)
  (*   (*         red in H, H0. *) *)
  (*   (*         econstructor; eauto. *) *)
  (*   (*         repeat red. intros. inv a. *) *)
  (*   (*         red; reflexivity. *) *)
  (*   (*         setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*         rewrite <- unfold_interp. *) *)
  (*   (*         rewrite H0. rewrite bind_trigger. *) *)
  (*   (*         rewrite interp_vis. *) *)
  (*   (*         cbn. *) *)
  (*   (*         setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *) *)
  (*   (*         intros. inv u. *) *)

  (*   (*         rewrite bind_trigger in H1. *) *)


  (*   (*       destruct s; try destruct u; cbn in H1. *) *)
  (*   (*       -- repeat red in HTA. *) *)
  (*   (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *) *)
  (*   (*           red. *) *)
  (*   (*           destruct (observe i) eqn: Heqi; *) *)
  (*   (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*           destruct H1 as (?&?&?). *) *)
  (*   (*           dependent destruction x. *) *)
  (*   (*           red in H, H0. *) *)
  (*   (*           econstructor; eauto. *) *)
  (*   (*           repeat red. intros. inv a. *) *)
  (*   (*           red; reflexivity. *) *)
  (*   (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*           rewrite <- unfold_interp. *) *)
  (*   (*           rewrite H0. rewrite bind_trigger. *) *)
  (*   (*           rewrite interp_vis. *) *)
  (*   (*           cbn. *) *)
  (*   (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *) *)
  (*   (*           intros. inv u. *) *)
  (*   (*       -- destruct s; try destruct u; cbn in H1. *) *)
  (*   (*          ++ destruct d. cbn in H1. *) *)
  (*   (*             rewrite <- unfold_interp in H2. *) *)

  (*   (*             rename H0 into KS. *) *)
  (*   (*             setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             setoid_rewrite bind_trigger in KS. *) *)

  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. subst. *) *)
  (*   (*             assert (Returns tt ta). *) *)
  (*   (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *) *)
  (*   (*               unfold subevent. reflexivity. *) *)
  (*   (*               constructor; reflexivity. } *) *)
  (*   (*             specialize (HK _ H0). pclearbot. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             ** intros. red in H1. specialize (H1 tt). *) *)
  (*   (*                eapply bisimulation_is_eq in H1. destruct a. *) *)
  (*   (*                rewrite H1. *) *)
  (*   (*                right; eapply CIH. *) *)
  (*   (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *) *)
  (*   (*                pstep; econstructor; eauto. punfold HK. *) *)
  (*   (*                rewrite <- unfold_interp. Unshelve. *) *)
  (*   (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *) *)
  (*   (*                all : shelve. *) *)
  (*   (*             ** red; reflexivity. *) *)
  (*   (*             ** rewrite <- itree_eta in H2. *) *)
  (*   (*                rewrite H2. rewrite KS. *) *)
  (*   (*                rewrite interp_vis. cbn. unfold debug. *) *)
  (*   (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *) *)
  (*   (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *) *)
  (*   (*          ++ repeat red in HTA. *) *)
  (*   (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. cbn in *; subst. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             intros. inv a. *) *)
  (*   (*             red; reflexivity. *) *)
  (*   (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*             rewrite <- unfold_interp. *) *)
  (*   (*             rewrite H0. cbn. rewrite interp_bind. *) *)
  (*   (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *) *)
  (*   (*             do 2 rewrite bind_trigger. rewrite bind_vis. *) *)
  (*   (*             apply eqit_Vis; intros; inv u. *) *)


  (*   (*     } *) *)
  (*   (*     destruct s. *) *)
  (*   (*     * unfold raiseOOM in H1. *) *)
  (*   (*       destruct o. *) *)
  (*   (*       cbn in H1. *) *)
  (*   (*       rewrite bind_bind, bind_trigger in H1. *) *)
  (*   (*       rewrite itree_eta in H1, H2. *) *)
  (*   (*       red. *) *)
  (*   (*       destruct (observe i) eqn: Heqi; *) *)
  (*   (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*       destruct H1 as (?&?&?). *) *)
  (*   (*       dependent destruction x. *) *)
  (*   (*       red in H, H0. cbn in *. *) *)
  (*   (*       econstructor; eauto. *) *)
  (*   (*       -- intros. inv a. *) *)
  (*   (*       -- red; reflexivity. *) *)
  (*   (*       -- rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*          rewrite <- unfold_interp. rewrite H0. *) *)
  (*   (*          rewrite bind_trigger. *) *)
  (*   (*          rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger. *) *)
  (*   (*          rewrite bind_vis. subst. *) *)
  (*   (*          apply eqit_Vis; intros; inv u. *) *)
  (*   (*     * destruct s; try destruct u; cbn in H1. *) *)
  (*   (*       -- repeat red in HTA. *) *)
  (*   (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *) *)
  (*   (*           red. *) *)
  (*   (*           destruct (observe i) eqn: Heqi; *) *)
  (*   (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*           destruct H1 as (?&?&?). *) *)
  (*   (*           dependent destruction x. *) *)
  (*   (*           red in H, H0. *) *)
  (*   (*           econstructor; eauto. *) *)
  (*   (*           repeat red. intros. inv a. *) *)
  (*   (*           red; reflexivity. *) *)
  (*   (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*           rewrite <- unfold_interp. *) *)
  (*   (*           rewrite H0. rewrite bind_trigger. *) *)
  (*   (*           rewrite interp_vis. *) *)
  (*   (*           cbn. *) *)
  (*   (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *) *)
  (*   (*           intros. inv u. *) *)
  (*   (*       -- destruct s; try destruct u; cbn in H1. *) *)
  (*   (*          ++ destruct d. cbn in H1. *) *)
  (*   (*             rewrite <- unfold_interp in H2. *) *)

  (*   (*             rename H0 into KS. *) *)
  (*   (*             setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             setoid_rewrite bind_trigger in KS. *) *)

  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. subst. *) *)
  (*   (*             assert (Returns tt ta). *) *)
  (*   (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *) *)
  (*   (*               unfold subevent. reflexivity. *) *)
  (*   (*               constructor; reflexivity. } *) *)
  (*   (*             specialize (HK _ H0). pclearbot. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             ** intros. red in H1. specialize (H1 tt). *) *)
  (*   (*                eapply bisimulation_is_eq in H1. destruct a. *) *)
  (*   (*                rewrite H1. *) *)
  (*   (*                right; eapply CIH. *) *)
  (*   (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *) *)
  (*   (*                pstep; econstructor; eauto. punfold HK. *) *)
  (*   (*                rewrite <- unfold_interp. Unshelve. *) *)
  (*   (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *) *)
  (*   (*                all : shelve. *) *)
  (*   (*             ** red; reflexivity. *) *)
  (*   (*             ** rewrite <- itree_eta in H2. *) *)
  (*   (*                rewrite H2. rewrite KS. *) *)
  (*   (*                rewrite interp_vis. cbn. unfold debug. *) *)
  (*   (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *) *)
  (*   (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *) *)
  (*   (*          ++ repeat red in HTA. *) *)
  (*   (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *) *)
  (*   (*             red. *) *)
  (*   (*             destruct (observe i) eqn: Heqi; *) *)
  (*   (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *) *)
  (*   (*             destruct H1 as (?&?&?). *) *)
  (*   (*             dependent destruction x. *) *)
  (*   (*             red in H, H0. cbn in *; subst. *) *)
  (*   (*             econstructor; eauto. *) *)
  (*   (*             intros. inv a. *) *)
  (*   (*             red; reflexivity. *) *)
  (*   (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *) *)
  (*   (*             rewrite <- unfold_interp. *) *)
  (*   (*             rewrite H0. cbn. rewrite interp_bind. *) *)
  (*   (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *) *)
  (*   (*             do 2 rewrite bind_trigger. rewrite bind_vis. *) *)
  (*   (*             apply eqit_Vis; intros; inv u. *) *)

  (*   (*             Unshelve. *) *)
  (*   (*             all : eauto. *) *)
  (*   (*             all : inv x.     *) *)
  (* Admitted. *)

  Opaque FinPROV.initial_provenance.
  Opaque InfPROV.initial_provenance.
  Opaque dvalue_convert_lazy.
  Opaque uvalue_convert_lazy.
  Opaque dvalue_refine_lazy.
  Opaque uvalue_refine_lazy.
  Opaque DVCrev.dvalue_convert_lazy.
  Opaque DVCrev.uvalue_convert_lazy.
  Opaque DVCrev.dvalue_refine_lazy.
  Opaque DVCrev.uvalue_refine_lazy.
  Opaque dvalue_convert_strict.
  Opaque uvalue_convert_strict.
  Opaque dvalue_refine_strict.
  Opaque uvalue_refine_strict.
  Opaque DVCrev.dvalue_convert_strict.
  Opaque DVCrev.uvalue_convert_strict.
  Opaque DVCrev.dvalue_refine_strict.
  Opaque DVCrev.uvalue_refine_strict.

  (* Lemma refine_OOM_h_L4_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L4_convert_tree x_inf) (L4_convert_tree y_inf). *)
  (* Proof. *)
  (*   intros T. *)

  (*   unfold refine_OOM_h, L4_convert_tree, refine_OOM_h_flip. *)
  (*   intros. *)
  (*   rewrite (unfold_interp y_inf). *)
  (*   rewrite (unfold_interp x_inf). *)
  (*   cbn. *)

  (*   match goal with *)
  (*   | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0 *)
  (*   end. *)

  (*   assert (i ≅ _interp EC.L4_convert (observe y_inf)). { *)
  (*     rewrite Heqi. reflexivity. *)
  (*   } clear Heqi. *)
  (*   remember (_interp EC.L4_convert (observe x_inf)). *)
  (*   assert (i0 ≅ _interp EC.L4_convert (observe x_inf)). { *)
  (*     subst; reflexivity. *)
  (*   } clear Heqi1 Heqi0. *)
  (*   revert x_inf y_inf H i i0 H0 H1. *)

  (*   pcofix CIH. *)

  (*   intros * H. *)
  (*   punfold H; red in H. *)
  (*   remember (observe y_inf) as oy; remember (observe x_inf) as ox. *)
  (*   clear Heqoy Heqox. *)

  (*   induction H; pclearbot; intros; subst; auto. *)
  (*   - pstep. cbn in H1, H2. *)
  (*     rewrite itree_eta in H1, H2. *)
  (*     red. *)
  (*     destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
  (*       try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
  (*     subst; constructor; auto. *)
  (*   - pstep. cbn in H1, H2. *)
  (*     rewrite itree_eta in H1, H2. *)
  (*     red. *)
  (*     destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
  (*       try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
  (*     subst; constructor; auto. *)

  (*     right; eapply CIH; eauto; *)
  (*     rewrite unfold_interp in H1, H2; auto. *)
  (*   - pstep. cbn in H1, H2. *)
  (*     rewrite itree_eta in H1, H2. *)
  (*     red. *)
  (*     destruct (observe i) eqn: Heqi; *)
  (*       try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*     subst; constructor; auto. *)
  (*     rewrite unfold_interp in H1. *)
  (*     specialize (IHinterp_PropTF _ _ H1 H2). *)

  (*     punfold IHinterp_PropTF. *)
  (*   - pstep. cbn in H1, H2. *)
  (*     rewrite itree_eta in H1, H2. *)
  (*     red. *)
  (*     destruct (observe i0) eqn: Heqi; *)
  (*       try apply eqit_inv in H2; cbn in H2; try contradiction; auto. *)
  (*     subst; constructor; auto. *)
  (*     rewrite unfold_interp in H2. *)
  (*     specialize (IHinterp_PropTF _ _ H1 H2). *)

  (*     punfold IHinterp_PropTF. *)
  (*   - pstep. apply bisimulation_is_eq in HT1. *)
  (*     rewrite HT1 in H1. cbn in H1. *)
  (*     destruct (resum IFun A e). *)
  (*     cbn in H1. *)
  (*     repeat setoid_rewrite bind_vis in H1. *)
  (*     apply bisimulation_is_eq in H1. rewrite H1. *)
  (*     econstructor; eauto. *)
  (*     eapply eqit_Vis; intros; inv u. *)
  (*   - pstep. cbn in H2, H3. red in H. *)
  (*     rewrite H in H0. *)
  (*     rename H2 into H1. *)
  (*     rename H3 into H2. *)

  (*     rewrite itree_eta in H1, H2. *)
  (*     repeat destruct e; cbn in *. *)
  (*     + rewrite bind_bind in H1. *)
  (*       unfold lift_OOM in H1. *)
  (*       rename H0 into KS. rewrite bind_trigger in KS. *)
  (*       cbn in *. *)
  (*       destruct (EC.DVC.uvalue_convert f) eqn : Hf. *)
  (*       { rewrite bind_ret_l, bind_bind in H1. *)
  (*         destruct *)
  (*           (map_monad_In args *)
  (*             (fun (elt : E1.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm. *)
  (*         { rewrite bind_ret_l, bind_bind in H1. *)
  (*           rewrite bind_trigger in H1. *)

  (*           destruct (observe i) eqn: Heqi; *)
  (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*           red. *)
  (*           setoid_rewrite Heqi. *)
  (*           destruct H1 as (?&?&?). *)
  (*           dependent destruction x. *)
  (*           red in H, H0. *)
  (*           econstructor; [ constructor | ..]; eauto; cycle 1. *)
  (*           - red; reflexivity. *)
  (*           - cbn in *. *)
  (*             rewrite <- unfold_interp in H2. *)
  (*             rewrite <- itree_eta in H2. *)
  (*             rewrite H2. rewrite KS. rewrite interp_vis. cbn. *)
  (*             rewrite bind_bind. unfold lift_OOM. *)
  (*             rewrite Hf. setoid_rewrite bind_ret_l. *)
  (*             setoid_rewrite bind_bind. rewrite Hm. *)
  (*             setoid_rewrite bind_ret_l. *)
  (*             setoid_rewrite bind_bind. *)
  (*             setoid_rewrite bind_trigger. *)
  (*             unfold subevent. rewrite H0. *)
  (*             eapply eqit_Vis. intros. *)
  (*             Unshelve. *)
  (*             3 : exact (fun u0 : E2.DV.dvalue => *)
  (*             ITree.bind match EC.DVCrev.dvalue_convert u0 with *)
  (*                       | NoOom a0 => ret a0 *)
  (*                       | Oom s => raise_oom s *)
  (*                        end (fun x1 : E1.DV.dvalue => Tau (interp EC.L4_convert (k2 x1)))). *)
  (*             reflexivity. intros. inv H. *)
  (*           - cbn. red in H1. subst. *)
  (*             eapply bisimulation_is_eq in H1. rewrite H1. *)

  (*             destruct (EC.DVCrev.dvalue_convert a) eqn: Ht. *)
  (*             + setoid_rewrite H in HK. subst. *)
  (*               eapply Returns_uvalue_convert_L1_L2 in H3; eauto. *)
  (*               specialize (HK _ H3). pclearbot. *)
  (*               pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
  (*               pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ. *)
  (*               pstep; constructor; eauto. right; eauto. *)
  (*               eapply CIH; try rewrite <- unfold_interp; try reflexivity. *)
  (*               eapply HK. *)
  (*             + setoid_rewrite H in HK. subst. *)
  (*               unfold raiseOOM. *)
  (*               pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
  (*               pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
  (*               pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
  (*               pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
  (*               pstep; econstructor; eauto. unfold subevent. *)
  (*               reflexivity. } *)
  (*         { unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
  (*           red. destruct (observe i) eqn: Heqi; *)
  (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*           destruct H1 as (?&?&?). *)
  (*           dependent destruction x. *)
  (*           red in H, H0. *)
  (*           (* rewrite H1. *) *)
  (*           econstructor; eauto. *)
  (*           - intros. inv a. *)
  (*           - red; reflexivity. *)
  (*           - cbn in *. rewrite <- itree_eta in H2. *)
  (*             rewrite H2. rewrite <- unfold_interp. *)
  (*             rewrite KS. rewrite interp_vis. cbn. *)
  (*             rewrite bind_bind. unfold lift_OOM. *)
  (*             rewrite Hf. setoid_rewrite bind_ret_l. *)
  (*             setoid_rewrite bind_bind. rewrite Hm. *)
  (*             setoid_rewrite bind_trigger. *)
  (*             setoid_rewrite bind_vis. *)
  (*             unfold subevent. rewrite H0. *)
  (*             eapply eqit_Vis. intros. inv u0. } } *)

  (*         unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
  (*         red. destruct (observe i) eqn: Heqi; *)
  (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*         destruct H1 as (?&?&?). *)
  (*         dependent destruction x. *)
  (*         red in H, H0. cbn in *. *)
  (*         econstructor; eauto. *)
  (*       * intros. inv a. *)
  (*       * red; reflexivity. *)
  (*       * rewrite <- itree_eta in H2. rewrite H2. *)
  (*         rewrite <- unfold_interp. rewrite KS. *)
  (*         rewrite interp_vis. *)
  (*         cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf. *)
  (*         setoid_rewrite bind_trigger. *)
  (*         setoid_rewrite bind_vis. *)
  (*         unfold subevent. rewrite H0. *)
  (*         eapply eqit_Vis. intros. inv u. *)
  (*     + destruct s. *)
  (*       * unfold raiseOOM in H1. *)
  (*         destruct o. *)
  (*         cbn in H1. *)
  (*         rewrite bind_bind, bind_trigger in H1. *)
  (*         rewrite itree_eta in H1, H2. *)
  (*         red. *)
  (*         destruct (observe i) eqn: Heqi; *)
  (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*         destruct H1 as (?&?&?). *)
  (*         dependent destruction x. *)
  (*         red in H, H0. cbn in *. *)
  (*         econstructor; eauto. *)
  (*         -- intros. inv a. *)
  (*         -- red; reflexivity. *)
  (*         -- rewrite <- itree_eta in H2. rewrite H2. *)
  (*            rewrite <- unfold_interp. rewrite H0. *)
  (*            rewrite bind_trigger. *)
  (*            rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger. *)
  (*            rewrite bind_vis. subst. *)
  (*            apply eqit_Vis; intros; inv u. *)
  (*       * destruct s; try destruct u; cbn in H1. *)
  (*         -- repeat red in HTA. *)
  (*             unfold raiseUB in H1. rewrite bind_trigger in H1. *)
  (*             red. *)
  (*             destruct (observe i) eqn: Heqi; *)
  (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*             destruct H1 as (?&?&?). *)
  (*             dependent destruction x. *)
  (*             red in H, H0. *)
  (*             econstructor; eauto. *)
  (*             repeat red. intros. inv a. *)
  (*             red; reflexivity. *)
  (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *)
  (*             rewrite <- unfold_interp. *)
  (*             rewrite H0. rewrite bind_trigger. *)
  (*             rewrite interp_vis. *)
  (*             cbn. *)
  (*             setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
  (*             intros. inv u. *)
  (*         -- destruct s; try destruct u; cbn in H1. *)
  (*            ++ destruct d. cbn in H1. *)
  (*               rewrite <- unfold_interp in H2. *)

  (*               rename H0 into KS. *)
  (*               setoid_rewrite bind_trigger in H1. *)
  (*               setoid_rewrite bind_trigger in KS. *)

  (*               red. *)
  (*               destruct (observe i) eqn: Heqi; *)
  (*                 try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*               destruct H1 as (?&?&?). *)
  (*               dependent destruction x. *)
  (*               red in H, H0. subst. *)
  (*               assert (Returns tt ta). *)
  (*               { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *)
  (*                 unfold subevent. reflexivity. *)
  (*                 constructor; reflexivity. } *)
  (*               specialize (HK _ H0). pclearbot. *)
  (*               econstructor; eauto. *)
  (*               ** intros. red in H1. specialize (H1 tt). *)
  (*                  eapply bisimulation_is_eq in H1. destruct a. *)
  (*                  rewrite H1. *)
  (*                  right; eapply CIH. *)
  (*                  2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *)
  (*                  pstep; econstructor; eauto. punfold HK. *)
  (*                  rewrite <- unfold_interp. Unshelve. *)
  (*                  16 : exact (fun x => interp EC.L4_convert (k2 x)). reflexivity. *)
  (*                  all : shelve. *)
  (*               ** red; reflexivity. *)
  (*               ** rewrite <- itree_eta in H2. *)
  (*                  rewrite H2. rewrite KS. *)
  (*                  rewrite interp_vis. cbn. unfold debug. *)
  (*                  do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *)
  (*                  eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *)
  (*            ++ repeat red in HTA. *)
  (*               destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *)
  (*               red. *)
  (*               destruct (observe i) eqn: Heqi; *)
  (*                 try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
  (*               destruct H1 as (?&?&?). *)
  (*               dependent destruction x. *)
  (*               red in H, H0. cbn in *; subst. *)
  (*               econstructor; eauto. *)
  (*               intros. inv a. *)
  (*               red; reflexivity. *)
  (*               setoid_rewrite <- itree_eta in H2. rewrite H2. *)
  (*               rewrite <- unfold_interp. *)
  (*               rewrite H0. cbn. rewrite interp_bind. *)
  (*               rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *)
  (*               do 2 rewrite bind_trigger. rewrite bind_vis. *)
  (*               apply eqit_Vis; intros; inv u. *)

  (*               Unshelve. *)
  (*               all : eauto. *)
  (*               all : inv x. *)
  (* Admitted. *)

  (* Lemma refine_OOM_h_L5_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L5_convert_tree x_inf) (L5_convert_tree y_inf). *)
  (* Proof. *)
  (*   intros T. *)
  (*   apply refine_OOM_h_L4_convert_tree. *)
  (* Qed. *)

  (* Lemma refine_OOM_h_L6_convert_tree : *)
  (*   forall {T} x_inf y_inf (RR : relation T), *)
  (*     refine_OOM_h RR x_inf y_inf -> *)
  (*     refine_OOM_h RR (L6_convert_tree x_inf) (L6_convert_tree y_inf). *)
  (* Proof. *)
  (*   intros T. *)
  (*   apply refine_OOM_h_L5_convert_tree. *)
  (* Qed. *)


  (** Model *)
  Import DynamicTypes TypToDtyp CFG.

  Definition event_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition event_refine_strict A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition event_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_converted_lazy f1 f2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition event_res_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
               dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition event_res_refine_strict A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_strict res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_strict x x0 /\
               dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0'_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.

  Definition L0'_refine_strict A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_strict _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 uvalue_refine_strict args1 args2).
    }
  Defined.

  Definition L0'_res_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_res_refine_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Calls *)
    { inv c.
      inv c0.

      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2 /\
               uvalue_refine_lazy res1 res2
            ).
    }
  Defined.

  Definition L0'_res_refine_strict A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_res_refine_strict _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Calls *)
    { inv c.
      inv c0.

      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 uvalue_refine_strict args1 args2 /\
               uvalue_refine_strict res1 res2
            ).
    }
  Defined.

  Definition call_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0).
    }
  Defined.

  Definition call_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0).
    }
  Defined.

  Definition call_res_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0 /\
               uvalue_refine_lazy res1 res2).
    }
  Defined.

  Definition call_res_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0 /\
               uvalue_refine_strict res1 res2).
    }
  Defined.

  Definition exp_E_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_res_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
            dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_res_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_strict res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_strict x x0 /\
            dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0_E1E2_rutt_lazy t1 t2
    : Prop :=
    rutt
      event_refine_lazy
      event_res_refine_lazy
      dvalue_refine_lazy
      t1 t2.

  Definition L0_E1E2_rutt_strict t1 t2
    : Prop :=
    orutt
      event_refine_strict
      event_res_refine_strict
      dvalue_refine_strict
      t1 t2 (OOM:=OOME).

  Definition model_E1E2_rutt_strict p1 p2 :=
    L0_E1E2_rutt_strict
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Import TranslateFacts.
  Import RecursionFacts.

  (* TODO: Could be worth considering making sure this isn't behind a module? *)
  Lemma function_name_eq_equiv :
    forall id1 id2,
      LLVM1.function_name_eq id1 id2 = LLVM2.function_name_eq id1 id2.
  Proof.
    intros id1 id2.
    unfold LLVM1.function_name_eq, LLVM2.function_name_eq.
    reflexivity.
  Qed.

  Lemma trigger_alloca_E1E2_rutt_strict_sound :
    forall dt n osz,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict
        (trigger (IS1.LP.Events.Alloca dt n osz)) (trigger (Alloca dt n osz)).
  Proof.
    intros dt n osz.
    apply rutt_trigger.
    - cbn. auto.
    - intros t1 t2 H.
      cbn in *.
      tauto.
  Qed.

  Lemma trigger_globalwrite_E1E2_rutt_strict_sound :
    forall gid r1 r2,
      dvalue_refine_strict r1 r2 ->
      rutt event_refine_strict event_res_refine_strict eq (trigger (GlobalWrite gid r1))
        (trigger (GlobalWrite gid r2)).
  Proof.
    intros gid r1 r2 H.
    apply rutt_trigger.
    - cbn. auto.
    - intros [] [] _.
      auto.
  Qed.

  Lemma allocate_declarations_E1E2_rutt_strict_sound :
    forall a,
      rutt event_refine_strict event_res_refine_strict eq (LLVM1.allocate_declaration a) (allocate_declaration a).
  Proof.
    intros a.
    induction a.
    unfold LLVM1.allocate_declaration, allocate_declaration.
    cbn.
    repeat setoid_rewrite function_name_eq_equiv.
    break_match.
    - apply rutt_Ret; reflexivity.
    - eapply rutt_bind with (RR:=dvalue_refine_strict).
      { apply trigger_alloca_E1E2_rutt_strict_sound.
      }

      intros r1 r2 H.
      apply trigger_globalwrite_E1E2_rutt_strict_sound.
      auto.
  Qed.

  Lemma allocate_one_E1E2_rutt_strict_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
    intros m_declarations m_definitions.
    remember (m_declarations ++ map LLVMAst.df_prototype m_definitions) as declarations.
    clear m_declarations m_definitions Heqdeclarations.
    induction declarations.
    - cbn.
      apply rutt_Ret.
      reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { apply allocate_declarations_E1E2_rutt_strict_sound.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma allocate_global_E1E2_rutt_strict_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
    intros m_globals.
    induction m_globals.
    - cbn; apply rutt_Ret; reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { eapply rutt_bind with (RR:=dvalue_refine_strict).
        { apply trigger_alloca_E1E2_rutt_strict_sound.
        }

        intros r1 r2 H.
        apply trigger_globalwrite_E1E2_rutt_strict_sound; auto.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma exp_E_refine_strict_event_refine_strict :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B),
      exp_E_refine_strict A B e1 e2 ->
      event_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) (exp_to_L0 e2).
  Proof.
    intros A B e1 e2 H.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; auto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; auto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma event_refine_strict_exp_E_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_refine_strict A B e1 e2.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto.
            destruct a, b.
            tauto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma event_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma translate_exp_to_L0_E1E2_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2 ->
      rutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H1.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H1.
      apply H0 in H1.
      pclearbot.
      pfold. red.
      punfold H1.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_L0_E1E2_orutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
      intros o CONTRA.
      specialize (H1 o).
      apply H1.
      destruct e2; inv CONTRA.
      destruct s; inv H3.
      reflexivity.
    - gstep; eauto.
      red.
      cbn.
      change (inr1 (inr1 (inr1 (inr1 (resum IFun A e))))) with (@subevent _ _ (ReSum_inr IFun sum1 OOME
                                                                               (IntrinsicE +'
                                                                                              LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                               ExternalCallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy :
    forall dv,
      uvalue_convert_lazy (IS1.LP.Events.DV.dvalue_to_uvalue dv) = dvalue_to_uvalue (dvalue_convert_lazy dv).
  Proof.
    induction dv; cbn;
      try
        solve [ rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn; auto;
                break_match; cbn; auto
              | rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn; auto
        ].

    { (* Structs *)
      rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn.
      induction fields.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHfields.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHfields.
        rewrite H; cbn; auto.
    }

    { (* Packed structs *)
      rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn.
      induction fields.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHfields.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHfields.
        rewrite H; cbn; auto.
    }

    { (* Arrays *)
      rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn.
      induction elts.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHelts.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHelts.
        rewrite H; cbn; auto.
    }

    { (* Vectors *)
      rewrite uvalue_convert_lazy_equation, dvalue_convert_lazy_equation; cbn.
      induction elts.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHelts.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHelts.
        rewrite H; cbn; auto.
    }
  Qed.

  Definition event_res_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
               dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0'_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.

  Definition L0'_res_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_res_converted_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Calls *)
    { inv c.
      inv c0.

      apply (dt1 = dt2 /\
               uvalue_converted_lazy f1 f2 /\
               Forall2 uvalue_converted_lazy args1 args2 /\
               uvalue_converted_lazy res1 res2
            ).
    }
  Defined.

  Definition call_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0).
    }
  Defined.

  Definition call_res_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0 /\
               uvalue_converted_lazy res1 res2).
    }
  Defined.

  Definition exp_E_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_res_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
            dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0_E1E2_rutt_converted_lazy t1 t2
    : Prop :=
    rutt
      event_converted_lazy
      event_res_converted_lazy
      dvalue_converted_lazy
      t1 t2.

  Definition model_E1E2_rutt_converted_lazy p1 p2 :=
    L0_E1E2_rutt_converted_lazy
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Lemma allocate_one_E1E2_rutt_converted_lazy_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
  Admitted.

  Lemma allocate_global_E1E2_rutt_converted_lazy_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
  Admitted.

  Lemma translate_exp_to_L0_E1E2_converted_lazy_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_converted_lazy exp_E_res_converted_lazy RR
        t1
        t2 ->
      rutt event_converted_lazy event_res_converted_lazy RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
  Proof.
  Admitted.

  (* TODO: Move this? *)
  Lemma dvalue_refine_lazy_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 ->
      uvalue_refine_lazy (IS1.LP.Events.DV.dvalue_to_uvalue dv1) (IS2.LP.Events.DV.dvalue_to_uvalue dv2).
  Proof.
    induction dv1; intros dv2 REF.

    1-11:
      solve [
          rewrite dvalue_refine_lazy_equation in REF;
          unfold dvalue_converted_lazy in *;
          rewrite dvalue_convert_lazy_equation in REF;
          rewrite uvalue_refine_lazy_equation;
          cbn in *; unfold uvalue_converted_lazy in *;
          rewrite uvalue_convert_lazy_equation; cbn in *;
          solve
            [ (cbn in REF;
               destruct REF as [REF | REF];
               [ subst; auto
               | destruct dv2; inv REF;
                 unfold dvalue_to_uvalue;
                 try solve [auto | right; constructor; auto]
              ])
            | break_match_hyp;
              (cbn in REF;
               destruct REF as [REF | REF];
               [ subst; auto
               | destruct dv2; inv REF;
                 unfold dvalue_to_uvalue;
                 try solve [auto | right; constructor; auto]
              ])
            ]
        ].

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *;
        rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        left.
        cbn.

        induction fields.
        + cbn. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *;
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (IS1.LP.Events.DV.dvalue_to_uvalue a) = dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          * right; constructor; auto.
          * (* Struct *)
            right.
            cbn.
            constructor.
            { apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
            }
            { pose proof (DV1.dvalue_to_uvalue_preserves_dtyp H2).
              inv H0.
              - constructor.
              - cbn. constructor; auto.
            }
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold IS1.LP.Events.DV.dvalue_to_uvalue at 1.
          unfold dvalue_to_uvalue at  1.

          induction fields, fields0; inversion REF.
          { cbn; auto.
          }
          { rewrite map_cons.
            rewrite map_cons.
            repeat fold dvalue_to_uvalue in *.
            repeat fold IS1.LP.Events.DV.dvalue_to_uvalue in *.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply dvalue_to_uvalue_inj in DVB'; subst.
              apply IS1.LP.Events.DV.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *;
        rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        left.
        cbn.

        induction fields.
        + cbn. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (IS1.LP.Events.DV.dvalue_to_uvalue a) = dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          * right; constructor; auto.
          * (* Struct *)
            right.
            cbn.
            constructor.
            { apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
            }
            { pose proof (DV1.dvalue_to_uvalue_preserves_dtyp H2).
              inv H0.
              - constructor.
              - cbn. constructor; auto.
            }
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold IS1.LP.Events.DV.dvalue_to_uvalue at 1.
          unfold dvalue_to_uvalue at  1.

          induction fields, fields0; inversion REF.
          { cbn; auto.
          }
          { rewrite map_cons.
            rewrite map_cons.
            repeat fold dvalue_to_uvalue in *.
            repeat fold IS1.LP.Events.DV.dvalue_to_uvalue in *.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply dvalue_to_uvalue_inj in DVB'; subst.
              apply IS1.LP.Events.DV.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *; rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        left.
        cbn.

        rename elts into fields.
        induction fields.
        + cbn. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (IS1.LP.Events.DV.dvalue_to_uvalue a) = dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          right.
          constructor.
          * apply Forall_forall.
            intros x IN.
            apply in_map_iff in IN as [x' [CONV IN]].
            apply Forall_forall with (x:=x') in H1; auto.
            subst.
            apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
          * rewrite map_length; auto.
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold IS1.LP.Events.DV.dvalue_to_uvalue at 1.
          unfold dvalue_to_uvalue at 1.

          repeat fold dvalue_to_uvalue in *.
          repeat fold IS1.LP.Events.DV.dvalue_to_uvalue in *.

          induction elts, elts0; inversion REF.
          { cbn; auto.
          }
          { rewrite map_cons.
            rewrite map_cons.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply dvalue_to_uvalue_inj in DVB'; subst.
              apply IS1.LP.Events.DV.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *; rewrite dvalue_convert_lazy_equation in REF.
      destruct REF as [REF | REF].
      - subst; auto.
        left.
        cbn.
        rename elts into fields.
        induction fields.
        + cbn. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.
          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }
          inv IHfields.
          assert
            (uvalue_convert_lazy (IS1.LP.Events.DV.dvalue_to_uvalue a) = dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          right.
          constructor.
          * apply Forall_forall.
            intros x IN.
            apply in_map_iff in IN as [x' [CONV IN]].
            apply Forall_forall with (x:=x') in H1; auto.
            subst.
            apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
          * rewrite map_length; auto.
          * auto.
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold IS1.LP.Events.DV.dvalue_to_uvalue at 1.
          unfold dvalue_to_uvalue at 1.

          repeat fold dvalue_to_uvalue in *.
          repeat fold IS1.LP.Events.DV.dvalue_to_uvalue in *.

          induction elts, elts0; inversion REF.
          { cbn; auto.
          }
          { rewrite map_cons.
            rewrite map_cons.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply dvalue_to_uvalue_inj in DVB'; subst.
              apply IS1.LP.Events.DV.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    (* This QED takes foreeeever *)
  Admitted.

  Hint Resolve dvalue_refine_lazy_dvalue_to_uvalue : DVALUE_REFINE.

  (* TODO: This seems better than lazy proof... Can probably do the same? *)
  Lemma dvalue_refine_strict_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_strict dv1 dv2 ->
      uvalue_refine_strict (IS1.LP.Events.DV.dvalue_to_uvalue dv1) (IS2.LP.Events.DV.dvalue_to_uvalue dv2).
  Proof.
    induction dv1; intros dv2 REF;
      rewrite dvalue_refine_strict_equation in REF;
      rewrite dvalue_convert_strict_equation in REF;
      rewrite uvalue_refine_strict_equation;
      cbn in *;
      rewrite uvalue_convert_strict_equation; cbn in *.

    1-11:
      solve
        [ break_match_hyp; inv REF; auto
        | inv REF; auto
        ].

    { (* Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction fields; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_In_unfold in Heqo.
          rewrite map_monad_In_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHfields.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHfields l1 eq_refl l0 eq_refl).

          inv IHfields.
          auto.
      - cbn.
        (* TODO: Move this *)
        Set Nested Proofs Allowed.
        Lemma map_monad_In_cons
          {M} `{MM : Monad M}
          {A B} l (x:A) (f: forall (a : A), In a (x::l) -> M B) :
          (map_monad_In (x::l) f) =
            (b <- f x (or_introl eq_refl);;
             bs2 <- map_monad_In l (fun x HIn => f x (or_intror HIn));;
             ret (b :: bs2)).
        Proof.
          reflexivity.
        Qed.

        (* TODO: Move this *)
        Lemma map_monad_In_OOM_fail :
          forall {A B} l (f : forall (a : A), In a l -> OOM B) b,
            map_monad_In l f = Oom b ->
            exists a (HIn : In a l), f a HIn = Oom b.
        Proof.
          intros A B l f b MAP.
          generalize dependent b.
          generalize dependent l.
          induction l; intros f b MAP.
          - cbn in MAP.
            inv MAP.
          - rewrite map_monad_In_cons in MAP.
            cbn in *.
            destruct (f a (or_introl eq_refl)) eqn:Hfa; inv MAP;
              setoid_rewrite Hfa in H0; inv H0.
            + rename H1 into MAP.
              destruct (map_monad_In l (fun (x : A) (HIn : In x l) => f x (or_intror HIn))) eqn:HMAP; inv MAP.
              specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) b HMAP) as [a' [IN FA]].
              exists a'. exists (or_intror IN). auto.
            + exists a. exists (or_introl eq_refl). auto.
        Qed.

        (* TODO: Move this *)
        Lemma map_monad_In_OOM_fail' :
          forall {A B} l (f : forall (a : A), In a l -> OOM B),
          (exists a b (HIn : In a l), f a HIn = Oom b) ->
          (exists s, map_monad_In l f = Oom s).
        Proof.
          intros A B l f FAIL.
          generalize dependent l.
          induction l; intros f FAIL.
          - cbn in FAIL.
            destruct FAIL as [_ [_ [CONTRA _]]].
            contradiction.
          - destruct FAIL as [a0 [b [HIn FAIL]]].
            destruct HIn.
            + subst.
              rewrite map_monad_In_cons.
              cbn.
              setoid_rewrite FAIL.
              eauto.
            + rewrite map_monad_In_cons.
              cbn.
              break_match_goal.
              * specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn))).
                forward IHl; eauto.
                destruct IHl as [s IHl].
                exists s.
                rewrite IHl.
                auto.
              * exists s; auto.
        Qed.

        (* TODO: move / generalize these *)
        Lemma map_monad_In_oom_forall2 :
          forall {A B} l (f : forall (a : A), In a l -> OOM B) res,
            map_monad_In l f = NoOom res <->
              Forall2_HIn l res (fun a b INA INB => f a INA = NoOom b).
        Proof.
          intros A B.
          induction l; intros f res.
          - split; intros MAP.
            + cbn in *.
              inv MAP.
              auto.
            + cbn in *.
              break_match_hyp; tauto.
          - split; intros MAP.
            + rewrite map_monad_In_unfold in MAP.
              cbn in *.
              break_match_hyp; inv MAP.
              break_match_hyp; inv H0.

              pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
              constructor; auto.
              eapply FORALL. eauto.
            + rewrite map_monad_In_cons.
              cbn in *.
              break_match_hyp; try contradiction.
              cbn in *.
              destruct MAP as [FA MAP].
              rewrite FA.

              pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
              apply FORALL in MAP.
              rewrite MAP.
              auto.
        Qed.

        Lemma In_Nth :
          forall {X} xs (x : X),
            In x xs -> exists i, Util.Nth xs i x.
        Proof.
          induction xs; intros x IN.
          - inv IN.
          - destruct IN; subst.
            + exists (0%nat). cbn. auto.
            + apply IHxs in H as [i H].
              exists (S i).
              cbn; auto.
        Qed.

        Lemma map_monad_In_OOM_succeeds' :
          forall {A B} l (f : forall (a : A), In a l -> OOM B) res,
            map_monad_In l f = ret res ->
            (forall a (HIn : In a l), exists b, f a HIn = ret b).
        Proof.
          intros A B.
          induction l; intros f res MAP.
          - intros _ [].
          - rewrite map_monad_In_cons in MAP.
            cbn in *.
            break_match_hyp; inv MAP.
            rename H0 into MAP.
            break_match_hyp; inv MAP.

            intros a0 [HIn | HIn]; subst.
            + exists b; auto.
            + apply IHl with (a:=a0) (HIn:=HIn) in Heqo0.
              auto.
        Qed.

        eapply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply In_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Util.Nth_In in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_In_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x INX b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }

    { (* Packed Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction fields; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_In_unfold in Heqo.
          rewrite map_monad_In_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHfields.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHfields l1 eq_refl l0 eq_refl).

          inv IHfields.
          auto.
      - cbn.

        eapply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply In_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Util.Nth_In in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_In_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x INX b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }

    { (* Arrays *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction elts; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_In_unfold in Heqo.
          rewrite map_monad_In_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHelts.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHelts l1 eq_refl l0 eq_refl).

          inv IHelts.
          auto.
      - cbn.

        eapply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply In_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Util.Nth_In in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_In_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x INX b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }

    { (* Vectors *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction elts; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_In_unfold in Heqo.
          rewrite map_monad_In_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHelts.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHelts l1 eq_refl l0 eq_refl).

          inv IHelts.
          auto.
      - cbn.

        eapply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply In_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Util.Nth_In in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_In_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x INX b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }
  Qed.

  Hint Resolve dvalue_refine_strict_dvalue_to_uvalue : DVALUE_REFINE.

  Lemma translate_LU_to_exp_lookup_id_rutt_lazy :
    forall id : LLVMAst.ident,
      rutt exp_E_refine_lazy exp_E_res_refine_lazy uvalue_refine_lazy
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id)).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      apply dvalue_refine_lazy_dvalue_to_uvalue.
      destruct H.
      auto.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      destruct H.
      auto.
  Qed.

  Lemma translate_LU_to_exp_lookup_id_orutt :
    forall id : LLVMAst.ident,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id))
        (OOM:=OOME).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      cbn in H.
      apply dvalue_refine_strict_dvalue_to_uvalue.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
  Qed.

  (* TODO: generalize *)
  Lemma rutt_raise :
    forall {E1 E2 : Type -> Type} {R1 R2 : Type} `{FailureE -< E1} `{FailureE -< E2}
      {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop}
      msg1 msg2,
      PRE void void (subevent void (Throw msg1)) (subevent void (Throw msg2)) ->
      rutt PRE POST R1R2 (LLVMEvents.raise msg1) (LLVMEvents.raise msg2).
  Proof.
    intros E1 E2 R1 R2 FAIL1 FAIL2 PRE POST R1R2 msg1 msg2 PRETHROW.
    unfold LLVMEvents.raise.
    repeat rewrite bind_trigger.
    apply rutt_Vis; auto.
    intros [] [] _.
  Qed.

  (* TODO: generalize *)
  Lemma orutt_raise :
    forall {E1 E2 OOM : Type -> Type} OOME {R1 R2 : Type} `{FAIL1 : FailureE -< E1} `{FAIL2 : FailureE -< E2}
      {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop}
      msg1 msg2,
      (forall msg (o : OOM _), @subevent FailureE E2 FAIL2 void (Throw msg) <> @subevent OOM E2 OOME void o) ->
      PRE void void (subevent void (Throw msg1)) (subevent void (Throw msg2)) ->
      orutt PRE POST R1R2 (LLVMEvents.raise msg1) (LLVMEvents.raise msg2) (OOM:=OOM) (OOME:=OOME).
  Proof.
    intros E1 E2 OOM OOME R1 R2 FAIL1 FAIL2 PRE POST R1R2 msg1 msg2 OOM_NOT_FAIL PRETHROW.
    unfold LLVMEvents.raise.
    repeat rewrite bind_trigger.
    apply orutt_Vis; auto.
    intros [] [] _.
  Qed.

  Lemma orutt_raiseOOM :
    forall {E1 E2 : Type -> Type} `{OOME2 : OOME -< E2} {R1 R2 : Type}
      {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop} t msg,
        orutt PRE POST R1R2 t (raiseOOM msg) (OOM:=OOME) (OOME:=OOME2).
  Proof.
    intros E1 E2 OOME2 R1 R2 PRE POST R1R2 t msg.
    unfold raiseOOM.
    rewrite bind_trigger.
    pfold. red.
    cbn.
    apply EqVisOOM.
  Qed.

  Lemma orutt_raise_oom :
    forall {E1 E2 : Type -> Type} `{OOME2 : OOME -< E2} {R1 R2 : Type}
      {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop} t msg,
        orutt PRE POST R1R2 t (raise_oom msg) (OOM:=OOME) (OOME:=OOME2).
  Proof.
    intros E1 E2 OOME R1 R2 PRE POST R1R2 t msg.
    cbn.
    apply orutt_raiseOOM.
  Qed.

  (* TODO: Move this? *)
  Ltac unfold_dvalue_refine_strict :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in *.

  Ltac unfold_dvalue_refine_strict_goal :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation.

  Ltac unfold_dvalue_refine_strict_in H :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in H.

  Ltac unfold_uvalue_refine_strict :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in *.

  Ltac unfold_uvalue_refine_strict_goal :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.

  Ltac unfold_uvalue_refine_strict_in H :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H.

  Ltac solve_uvalue_refine_strict :=
    solve [unfold_uvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite AC1.addr_convert_null;
                   reflexivity
             ]
      ].

  Ltac solve_dvalue_refine_strict :=
    solve [unfold_dvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite AC1.addr_convert_null;
                   reflexivity
             ]
      ].

  Ltac solve_orutt_raise :=
    apply orutt_raise; cbn; auto;
    intros msg o CONTRA;
    inv CONTRA.

  (* TODO: move this? *)
  Lemma uvalue_convert_lazy_preserves_is_concrete :
    forall uv uvc b,
      uvalue_convert_lazy uv = uvc ->
      IS1.LP.Events.DV.is_concrete uv = b ->
      IS2.LP.Events.DV.is_concrete uvc = b.
  Proof.
    induction uv using IS1.LP.Events.DV.uvalue_ind';
      intros uvc b UVC CONC; cbn in *;
      rewrite uvalue_convert_lazy_equation in UVC;
      try solve
        [ cbn in *; subst; try break_match; cbn; auto
        ].

    - (* Structs *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Packed Structs *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Packed_struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Packed_struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Arrays *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Array (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Array (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Vectors *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Vector (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Vector (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.
  Qed.

  (* TODO: move this? *)
  Lemma uvalue_refine_strict_preserves_is_concrete :
    forall uv uvc b,
      uvalue_refine_strict uv uvc ->
      IS1.LP.Events.DV.is_concrete uv = b ->
      IS2.LP.Events.DV.is_concrete uvc = b.
  Proof.
    induction uv using IS1.LP.Events.DV.uvalue_ind';
      intros uvc b UVC CONC; cbn in *;
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in UVC;
      try solve
        [ cbn in *; subst; try break_match; inv UVC; cbn; auto
        | cbn in *; subst;
          break_match_hyp; inv UVC;
          break_match_hyp; inv H0;
          eauto
        ].

    - (* Structs *)
      rewrite map_monad_In_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Struct l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Struct l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Packed Structs *)
      rewrite map_monad_In_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Packed_struct l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Packed_struct l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Arrays *)
      rewrite map_monad_In_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Array l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Array l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Vectors *)
      rewrite map_monad_In_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (IS1.LP.Events.DV.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb IS1.LP.Events.DV.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (UVALUE_Vector l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (UVALUE_Vector l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.
    - (* GEP *)
      cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
  Qed.

  (* TODO: Move these? *)
  Lemma uvalue_to_dvalue_dvalue_refine_strict :
    forall uv1 uv2 dv1,
      uvalue_refine_strict uv1 uv2 ->
      IS1.LP.Events.DV.uvalue_to_dvalue uv1 = inr dv1 ->
      exists dv2, uvalue_to_dvalue uv2 = inr dv2 /\
               dvalue_refine_strict dv1 dv2.
  Proof.
    induction uv1 using IS1.LP.Events.DV.uvalue_ind';
      intros uv2 dv1 CONV UV1;
      try solve
        [ unfold_uvalue_refine_strict;
          cbn in CONV;
          (try first [break_match_hyp; inv CONV
                     | inv CONV];
           try solve
             [ cbn in *;
               inv UV1;
               try (break_match_hyp; inv CONV);
               eexists; cbn; split; eauto;
               unfold_dvalue_refine_strict; cbn; try rewrite Heqo; auto
        ])].
    - (* Structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.

      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      rename Heqo into CONV.

      rename l0 into dvs.
      rename d into dv.

      pose proof IHuv1 as IHuv1'.
      pose proof IHuv0 as IHuv0'.
      move IHuv1' at top.
      move IHuv0' at top.

      cbn in *.
      rewrite Heqs in IHuv0.


      specialize (IHuv0 (DV2.UVALUE_Struct l1) (IS1.LP.Events.DV.DVALUE_Struct dvs)).
      forward IHuv0.
      { unfold_uvalue_refine_strict.
        cbn. rewrite CONV.
        reflexivity.
      }
      specialize (IHuv0 eq_refl).
      destruct IHuv0 as [dv2 [IH DV2REF]].
      specialize (IHuv1 u dv).
      forward IHuv1. auto.
      forward IHuv1. reflexivity.
      destruct IHuv1 as [dc [DC DCREF]].

      cbn in IH.
      break_match_hyp; inv IH.
      rename l into dvs2.

      exists (DV2.DVALUE_Struct (dc :: dvs2)).

      split.
      { cbn.
        rewrite DC.
        reflexivity.
      }

      { unfold_dvalue_refine_strict_in DV2REF.
        cbn in DV2REF.
        break_match_hyp; inv DV2REF.
        unfold_dvalue_refine_strict_goal.
        rewrite map_monad_In_cons.
        cbn.
        rewrite DCREF.
        rewrite Heqo.
        reflexivity.
      }
    - (* Packed structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.

      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      rename Heqo into CONV.

      rename l0 into dvs.
      rename d into dv.

      pose proof IHuv1 as IHuv1'.
      pose proof IHuv0 as IHuv0'.
      move IHuv1' at top.
      move IHuv0' at top.

      cbn in *.
      rewrite Heqs in IHuv0.


      specialize (IHuv0 (DV2.UVALUE_Packed_struct l1) (IS1.LP.Events.DV.DVALUE_Packed_struct dvs)).
      forward IHuv0.
      { unfold_uvalue_refine_strict.
        cbn. rewrite CONV.
        reflexivity.
      }
      specialize (IHuv0 eq_refl).
      destruct IHuv0 as [dv2 [IH DV2REF]].
      specialize (IHuv1 u dv).
      forward IHuv1. auto.
      forward IHuv1. reflexivity.
      destruct IHuv1 as [dc [DC DCREF]].

      cbn in IH.
      break_match_hyp; inv IH.
      rename l into dvs2.

      exists (DV2.DVALUE_Packed_struct (dc :: dvs2)).

      split.
      { cbn.
        rewrite DC.
        reflexivity.
      }

      { unfold_dvalue_refine_strict_in DV2REF.
        cbn in DV2REF.
        break_match_hyp; inv DV2REF.
        unfold_dvalue_refine_strict_goal.
        rewrite map_monad_In_cons.
        cbn.
        rewrite DCREF.
        rewrite Heqo.
        reflexivity.
      }
    - (* Arrays cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.

      specialize (IHuv1 u d).
      forward IHuv1; auto.
      specialize (IHuv1 eq_refl).
      destruct IHuv1 as [dv2 [U2Ddv2 DV2REF]].

      cbn.
      rewrite U2Ddv2.

      specialize (IHuv0 (DV2.UVALUE_Array l1) (IS1.LP.Events.DV.DVALUE_Array l0)).
      forward IHuv0.
      { unfold_uvalue_refine_strict_goal.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      specialize (IHuv0 eq_refl).

      destruct IHuv0 as [dvs [U2Ddvs DVSREF]].
      cbn in *.
      break_match_hyp; inv U2Ddvs.
      eexists; split; auto.
      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite DV2REF.
      unfold_dvalue_refine_strict_in DVSREF.
      cbn in DVSREF.
      break_match_hyp; inv DVSREF.
      auto.
    - (* Vectors cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.

      specialize (IHuv1 u d).
      forward IHuv1; auto.
      specialize (IHuv1 eq_refl).
      destruct IHuv1 as [dv2 [U2Ddv2 DV2REF]].

      cbn.
      rewrite U2Ddv2.

      specialize (IHuv0 (DV2.UVALUE_Vector l1) (IS1.LP.Events.DV.DVALUE_Vector l0)).
      forward IHuv0.
      { unfold_uvalue_refine_strict_goal.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      specialize (IHuv0 eq_refl).

      destruct IHuv0 as [dvs [U2Ddvs DVSREF]].
      cbn in *.
      break_match_hyp; inv U2Ddvs.
      eexists; split; auto.
      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite DV2REF.
      unfold_dvalue_refine_strict_in DVSREF.
      cbn in DVSREF.
      break_match_hyp; inv DVSREF.
      auto.
  Qed.

  (* TODO: Move these? *)
  Lemma uvalue_to_dvalue_dvalue_refine_strict_error :
    forall uv1 uv2 s,
      uvalue_refine_strict uv1 uv2 ->
      IS1.LP.Events.DV.uvalue_to_dvalue uv1 = inl s ->
      exists s', uvalue_to_dvalue uv2 = inl s'.
  Proof.
    induction uv1 using IS1.LP.Events.DV.uvalue_ind';
      intros uv2 dv1 CONV UV1;
      try solve
        [ unfold_uvalue_refine_strict;
          cbn in CONV;
          (try first [break_match_hyp; inv CONV
                     | inv CONV];
           try solve
             [ cbn in *;
               inv UV1;
               try (break_match_hyp; inv CONV);
               eexists; cbn; split; eauto;
               unfold_dvalue_refine_strict; cbn; try rewrite Heqo; auto
          ])
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H0;
          cbn;
          eexists; eauto
        | cbn in *;
          unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H1;
          cbn; eexists; eauto
        | cbn in *;
          unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H0;
          break_match_hyp; inv H1;
          cbn; eexists; eauto
        ].
    - (* Structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.
      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        rename Heqo into CONV.

        rename l0 into dvs.

        pose proof IHuv1 as IHuv1'.
        pose proof IHuv0 as IHuv0'.
        move IHuv1' at top.
        move IHuv0' at top.

        cbn in *.
        specialize (IHuv1 u dv1 Heqo0 eq_refl).
        destruct IHuv1.
        exists x. rewrite H.
        reflexivity.
      + break_match_hyp; inv H0.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        cbn.
        destruct (uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        destruct (map_monad uvalue_to_dvalue l0) eqn:Hl0.
        eexists; reflexivity.

        exfalso.

        assert (uvalue_refine_strict (DV1.UVALUE_Struct uvs) (DV2.UVALUE_Struct l0)) as REFSTRUCT.
        { unfold_uvalue_refine_strict.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        epose proof IHuv0 _ _ REFSTRUCT.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        rewrite Hl0 in H.
        destruct H.
        inv H.
    - (* Packed structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_In_cons in CONV.
      cbn in CONV.
      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        rename Heqo into CONV.

        rename l0 into dvs.

        pose proof IHuv1 as IHuv1'.
        pose proof IHuv0 as IHuv0'.
        move IHuv1' at top.
        move IHuv0' at top.

        cbn in *.
        specialize (IHuv1 u dv1 Heqo0 eq_refl).
        destruct IHuv1.
        exists x. rewrite H.
        reflexivity.
      + break_match_hyp; inv H0.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        cbn.
        destruct (uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        destruct (map_monad uvalue_to_dvalue l0) eqn:Hl0.
        eexists; reflexivity.

        exfalso.

        assert (uvalue_refine_strict (DV1.UVALUE_Packed_struct uvs) (DV2.UVALUE_Packed_struct l0)) as REFSTRUCT.
        { unfold_uvalue_refine_strict.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        epose proof IHuv0 _ _ REFSTRUCT.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        rewrite Hl0 in H.
        destruct H.
        inv H.
    - (* Arrays cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + unfold_uvalue_refine_strict.
        rewrite map_monad_In_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHuv1 _ dv1 Heqo0 eq_refl).
        cbn in *.
        destruct IHuv1 as [s' IHuv1].
        rewrite IHuv1.
        eexists; reflexivity.
      + break_match_hyp; inv H0.
        unfold_uvalue_refine_strict.
        rewrite map_monad_In_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        assert (uvalue_refine_strict (DV1.UVALUE_Array uvs) (DV2.UVALUE_Array l0)) as REF.
        { unfold_uvalue_refine_strict_goal.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        cbn.
        destruct (uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        eapply IHuv0 in REF; eauto.
        destruct REF as [s' REF].
        exists s'.
        cbn in *.
        break_match_hyp; inv REF.
        reflexivity.
    - (* Vector cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + unfold_uvalue_refine_strict.
        rewrite map_monad_In_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHuv1 _ dv1 Heqo0 eq_refl).
        cbn in *.
        destruct IHuv1 as [s' IHuv1].
        rewrite IHuv1.
        eexists; reflexivity.
      + break_match_hyp; inv H0.
        unfold_uvalue_refine_strict.
        rewrite map_monad_In_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        assert (uvalue_refine_strict (DV1.UVALUE_Vector uvs) (DV2.UVALUE_Vector l0)) as REF.
        { unfold_uvalue_refine_strict_goal.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        cbn.
        destruct (uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        eapply IHuv0 in REF; eauto.
        destruct REF as [s' REF].
        exists s'.
        cbn in *.
        break_match_hyp; inv REF.
        reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma default_dvalue_of_dtyp_i_dv1_dv2_same_error :
    forall sz s,
      IS1.LP.Events.DV.default_dvalue_of_dtyp_i sz = inl s <->
        IS2.LP.Events.DV.default_dvalue_of_dtyp_i sz = inl s.
  Proof.
    intros sz s.
    split; intros S.
    { pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
      * inv SUPPORTED; cbn in *; inv S.
      * unfold default_dvalue_of_dtyp_i, IS1.LP.Events.DV.default_dvalue_of_dtyp_i in *.
        assert (sz <> 1)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 8)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 32)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 64)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).

        apply N.eqb_neq in H, H0, H1, H2.
        rewrite H, H0, H1, H2 in S.
        rewrite H, H0, H1, H2.
        inv S. auto.
    }
    { pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
      * inv SUPPORTED; cbn in *; inv S.
      * unfold default_dvalue_of_dtyp_i, IS1.LP.Events.DV.default_dvalue_of_dtyp_i in *.
        assert (sz <> 1)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 8)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 32)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 64)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).

        apply N.eqb_neq in H, H0, H1, H2.
        rewrite H, H0, H1, H2 in S.
        rewrite H, H0, H1, H2.
        inv S. auto.
    }
  Qed.

  (* TODO: Move this *)
  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv :
    forall sz v1,
      IS1.LP.Events.DV.default_dvalue_of_dtyp_i sz = inr v1 ->
      exists v2,
        IS2.LP.Events.DV.default_dvalue_of_dtyp_i sz = inr v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v1 V1.
    pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
    - inv SUPPORTED; cbn in *; inv V1;
        (eexists; split; [eauto | unfold_dvalue_refine_strict_goal; auto]).
    - unfold default_dvalue_of_dtyp_i, IS1.LP.Events.DV.default_dvalue_of_dtyp_i in *.
      assert (sz <> 1)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 8)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 32)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 64)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).

      apply N.eqb_neq in H, H0, H1, H2.
      rewrite H, H0, H1, H2 in V1.
      inv V1.
  Qed.

  (* TODO: Move this *)
  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv' :
    forall sz v2,
      IS2.LP.Events.DV.default_dvalue_of_dtyp_i sz = inr v2 ->
      exists v1,
        IS1.LP.Events.DV.default_dvalue_of_dtyp_i sz = inr v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v2 V2.
    pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
    - inv SUPPORTED; cbn in *; inv V2;
        (eexists; split; [eauto | unfold_dvalue_refine_strict_goal; auto]).
    - unfold default_dvalue_of_dtyp_i, IS1.LP.Events.DV.default_dvalue_of_dtyp_i in *.
      assert (sz <> 1)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 8)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 32)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 64)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).

      apply N.eqb_neq in H, H0, H1, H2.
      rewrite H, H0, H1, H2 in V2.
      inv V2.
  Qed.

  (* TODO: Move this? *)
  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv :
    forall dt v1,
      IS1.LP.Events.DV.default_dvalue_of_dtyp dt = inr v1 ->
      exists v2, IS2.LP.Events.DV.default_dvalue_of_dtyp dt = inr v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    induction dt; intros v1 V1;
      try solve
        [
          cbn in *; inv V1;
          eexists; split; eauto;
          unfold_dvalue_refine_strict_goal; cbn;
          auto
        ].
    - apply default_dvalue_of_dtyp_i_dv1_dv2_equiv; auto.
    - cbn in *; inv V1;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite IS1.LP.IP.to_Z_0.
      rewrite IP.from_Z_0.
      auto.
    - cbn in *; inv V1;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite AC1.addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp; inv V1.
      specialize (IHdt d eq_refl) as [v2 [DEFv2 REFv2]].
      eexists.
      rewrite DEFv2; split; eauto.
      unfold_dvalue_refine_strict_goal.
      cbn.
      break_match.
      2: {
        apply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [IN CONVa]].
        apply repeat_spec in IN; subst.
        rewrite REFv2 in CONVa.
        inv CONVa.
      }

      (* Something about map_monad and repeat? *)
      (* TODO: move this *)
      Lemma repeat_S :
        forall X (x : X) n,
          repeat x (S n) = x :: repeat x n.
      Proof.
        intros X x n.
        reflexivity.
      Qed.

      (* TODO: move this *)
      Lemma map_monad_In_OOM_repeat_success :
        forall {A B} sz x (f : forall (a : A), In a (repeat x sz) -> OOM B) res y
          (INx : In x (repeat x sz)),
          map_monad_In (repeat x sz) f = ret res ->
          f x INx = NoOom y ->
          res = repeat y sz.
      Proof.
        intros A B sz.
        induction sz; intros x f res y INx MAP F.
        - inv INx.
        - cbn.
          unfold repeat in MAP.
          rewrite map_monad_In_cons in MAP.
          cbn in MAP.
          assert (INx = or_introl eq_refl) by apply proof_irrelevance.
          subst.
          rewrite F in MAP.
          break_match_hyp; inv MAP.
          specialize (IHsz x).
          destruct sz.
          + cbn in *. inv Heqo.
            reflexivity.
          + eapply IHsz in Heqo.
            rewrite Heqo; eauto.
            erewrite (proof_irrelevance _ (or_introl eq_refl)) in F; eauto.

            Unshelve.
            cbn; auto.
      Qed.

      destruct (N.to_nat sz).
      + cbn in *.
        inv Heqo; auto.
      + apply map_monad_In_OOM_repeat_success with (y:=v2) in Heqo; cbn; auto.
        cbn in *.
        subst.
        auto.

    - (* Structs *)
      cbn in *.
      break_match_hyp; inv V1.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v2 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v2 [DEFv2 REFv2]].
      rewrite DEFv2.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite REFv2.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Packed Structs *)
      cbn in *.
      break_match_hyp; inv V1.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v2 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v2 [DEFv2 REFv2]].
      rewrite DEFv2.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite REFv2.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Vectors *)
      cbn in *.
      break_match_hyp; inv V1.
      { break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs as [v2 [DEFv2 REFv2]].
        eexists; rewrite DEFv2; split; auto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite REFv2 in CONVa.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=v2) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          rewrite AC1.addr_convert_null in CONVa; inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Addr null) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
          rewrite dvalue_convert_strict_equation; cbn.
          rewrite AC1.addr_convert_null. auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Float Floats.Float32.zero) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }
  Qed.

  (* TODO: Move this? *)
  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv' :
    forall dt v2,
      IS2.LP.Events.DV.default_dvalue_of_dtyp dt = inr v2 ->
      exists v1, IS1.LP.Events.DV.default_dvalue_of_dtyp dt = inr v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    induction dt; intros v2 V2;
      try solve
        [
          cbn in *; inv V2;
          eexists; split; eauto;
          unfold_dvalue_refine_strict_goal; cbn;
          auto
        ].
    - apply default_dvalue_of_dtyp_i_dv1_dv2_equiv'; auto.
    - cbn in *; inv V2;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite IS1.LP.IP.to_Z_0.
      rewrite IP.from_Z_0.
      auto.
    - cbn in *; inv V2;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite AC1.addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp; inv V2.
      specialize (IHdt d eq_refl) as [v1 [DEFv1 REFv1]].
      eexists.
      rewrite DEFv1; split; eauto.
      unfold_dvalue_refine_strict_goal.
      cbn.
      break_match.
      2: {
        apply map_monad_In_OOM_fail in Heqo.
        destruct Heqo as [a [IN CONVa]].
        apply repeat_spec in IN; subst.
        rewrite REFv1 in CONVa.
        inv CONVa.
      }

      destruct (N.to_nat sz).
      + cbn in *.
        inv Heqo; auto.
      + eapply map_monad_In_OOM_repeat_success with (y:=d) in Heqo; cbn; auto.
        cbn in *.
        subst.
        auto.

    - (* Structs *)
      cbn in *.
      break_match_hyp; inv V2.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v1 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v1 [DEFv1 REFv1]].
      rewrite DEFv1.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite REFv1.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Packed Structs *)
      cbn in *.
      break_match_hyp; inv V2.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v1 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v1 [DEFv1 REFv1]].
      rewrite DEFv1.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_In_cons.
      cbn.
      rewrite REFv1.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Vectors *)
      cbn in *.
      break_match_hyp; inv V2.
      { break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_equiv' in Heqs as [v1 [DEFv1 REFv1]].
        eexists; rewrite DEFv1; split; auto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite REFv1 in CONVa.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=d) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          rewrite AC1.addr_convert_null in CONVa; inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Addr null) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
          rewrite dvalue_convert_strict_equation; cbn.
          rewrite AC1.addr_convert_null. auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Float Floats.Float32.zero) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_In_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_In_OOM_repeat_success with (y:=DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }
  Qed.

  (* TODO: Move this? *)
  Lemma default_dvalue_of_dtyp_dv1_dv2_same_error :
    forall dt s,
      IS1.LP.Events.DV.default_dvalue_of_dtyp dt = inl s <->
        IS2.LP.Events.DV.default_dvalue_of_dtyp dt = inl s.
  Proof.
    intros dt s.
    split; intros S.
    { induction dt; cbn in *;
        try solve [inv S; auto].
      - apply default_dvalue_of_dtyp_i_dv1_dv2_same_error; auto.
      - rewrite IHdt; auto.
        break_match_hyp; inv S; auto.
      - (* Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Packed Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Vectors *)
        destruct dt; inv S; auto.
        break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs0.
        rewrite Heqs0.
        auto.
    }

    { induction dt; cbn in *;
        try solve [inv S; auto].
      - apply default_dvalue_of_dtyp_i_dv1_dv2_same_error; auto.
      - rewrite IHdt; auto.
        break_match_hyp; inv S; auto.
      - (* Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv' in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Packed Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv' in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Vectors *)
        destruct dt; inv S; auto.
        break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs0.
        rewrite Heqs0.
        auto.
    }
  Qed.

  (* TODO: Move this *)
  Lemma map_repeat :
    forall {A B} (f : A -> B) a sz,
      map f (repeat a sz) = repeat (f a) sz.
  Proof.
    intros A B f a sz.
    induction sz.
    - cbn; auto.
    - cbn. rewrite IHsz; auto.
  Qed.

  (* TODO: move this *)
  Lemma map_monad_In_map :
    forall {M : Type -> Type} {HM : Monad M} {EQM : Monad.Eq1 M},
      Monad.Eq1Equivalence M ->
      Monad.MonadLawsE M ->
      forall (A B C : Type) (xs : list A) (g : A -> B) (f : forall (b : B) (HIn : In b (map g xs)), M C),
        Monad.eq1 (map_monad_In (map g xs) f) (map_monad_In xs (fun (x : A) IN => f (g x) (in_map g xs x IN))).
  Proof.
    intros. induction xs.
    - simpl. reflexivity.
    - simpl.
      setoid_rewrite IHxs.
      cbn.
      assert (f (g a) (or_introl eq_refl) = f (g a) (in_map g (a :: xs) a (or_introl eq_refl))).
      { apply f_equal.
        apply proof_irrelevance.
      }
  Abort.

  (* TODO: Move this!!! *)
  Lemma map_monad_map_monad_In :
    forall {M A B} `{HM : Monad M} xs (f : A -> M B),
      map_monad f xs = map_monad_In xs (fun x _ => f x).
  Proof.
    intros M A B HM xs.
    induction xs; intros f.
    - cbn. reflexivity.
    - rewrite map_monad_unfold, map_monad_In_cons.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma map_monad_map_err :
    forall (A B C : Type) (xs : list A) (g : A -> B) (f : B -> err C),
      map_monad f (map g xs) = map_monad (fun (x : A) => f (g x)) xs.
  Proof.
    intros. induction xs.
    - simpl. reflexivity.
    - simpl.
      break_match; auto.
      setoid_rewrite IHxs.
      reflexivity.
  Qed.

  Lemma map_monad_map_oom :
    forall (A B C : Type) (xs : list A) (g : A -> B) (f : B -> OOM C),
      map_monad f (map g xs) = map_monad (fun (x : A) => f (g x)) xs.
  Proof.
    intros. induction xs.
    - simpl. reflexivity.
    - simpl.
      break_match; auto.
      setoid_rewrite IHxs.
      reflexivity.
  Qed.

  (* TODO: move this ltac, and probably use more *)
  Ltac rewrite_uvalue_convert_strict :=
    repeat
      match goal with
      | H: uvalue_convert_strict _ = _ |- _ =>
          rewrite H
      end.

  Ltac solve_pick_uvalue_orutt :=
    apply orutt_trigger; cbn;
    [ split;
      [ tauto
      | unfold_uvalue_refine_strict_goal;
        rewrite_uvalue_convert_strict;
        cbn;
        reflexivity
      ]
    | intros [t1] [t2] [_ [REF1 REF2]];
      cbn; auto
    | intros o CONTRA;
      inv CONTRA
    ].

  Lemma pick_your_poison_orutt :
    forall r1 r2,
      uvalue_refine_strict r1 r2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict
        dvalue_refine_strict (IS1.LLVM.D.pick_your_poison r1)
        (pick_your_poison r2)
        (OOM:=OOME).
  Proof.
    intros r1 r2 H.

    unfold pick_your_poison, IS1.LLVM.D.pick_your_poison.
    rewrite uvalue_refine_strict_equation in H.
    destruct r1; rewrite uvalue_convert_strict_equation in H; cbn in *;
      try solve
        [
          inv H; cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation; auto
        | break_match_hyp; inv H;
          try (break_match_hyp; inv H1);
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
          cbn;

          eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2));
          [ solve_pick_uvalue_orutt
          | intros [?r1] [?r2] ?H0;
            cbn in *;
            apply orutt_Ret; auto
          ]
        ].
    - break_match_hyp; inv H; cbn.
      apply orutt_Ret.
      rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* iptr *)
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* undef *)
      inv H.
      cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        (* TODO: make this a lemma? *)
        apply orutt_trigger; cbn.
        split; [tauto | solve_uvalue_refine_strict].
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Poison *)
      inv H; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | solve_uvalue_refine_strict].
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Structs *)
      break_match_hyp; inv H; cbn.
      generalize dependent l.
      induction fields; intros l Heqo.
      + cbn in *. inv Heqo.
        cbn.
        apply orutt_Ret; auto.
        solve_dvalue_refine_strict.
      + rewrite map_monad_In_cons in Heqo.
        cbn in Heqo.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHfields l0 eq_refl).
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        cbn.

        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete fields = forallb is_concrete l0).
        { (* Should follow from Heqo *)
          clear IHfields.
          generalize dependent l0.
          induction fields; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_In_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHfields l eq_refl).
            rewrite IHfields.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_In_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_In_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_In with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].


            (* TODO: Move this *)
            Lemma map_monad_In_err_fail :
              forall {A B} l (f : forall (a : A), In a l -> err B) b,
                map_monad_In l f = inl b ->
                exists a (HIn : In a l), f a HIn = inl b.
            Proof.
              intros A B l f b MAP.
              generalize dependent b.
              generalize dependent l.
              induction l; intros f b MAP.
              - cbn in MAP.
                inv MAP.
              - rewrite map_monad_In_cons in MAP.
                cbn in *.
                destruct (f a (or_introl eq_refl)) eqn:Hfa; inv MAP;
                  setoid_rewrite Hfa in H0; inv H0.
                + exists a. exists (or_introl eq_refl). auto.
                + rename H1 into MAP.
                  destruct (map_monad_In l (fun (x : A) (HIn : In x l) => f x (or_intror HIn))) eqn:HMAP; inv MAP.
                  specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) b HMAP) as [a' [IN FA]].
                  exists a'. exists (or_intror IN). auto.
            Qed.

            (* TODO: Move this *)
            Lemma map_monad_In_err_fail' :
              forall {A B} l (f : forall (a : A), In a l -> err B),
                (exists a b (HIn : In a l), f a HIn = inl b) ->
                (exists s, map_monad_In l f = inl s).
            Proof.
              intros A B l f FAIL.
              generalize dependent l.
              induction l; intros f FAIL.
              - cbn in FAIL.
                destruct FAIL as [_ [_ [CONTRA _]]].
                contradiction.
              - destruct FAIL as [a0 [b [HIn FAIL]]].
                destruct HIn.
                + subst.
                  rewrite map_monad_In_cons.
                  cbn.
                  setoid_rewrite FAIL.
                  eauto.
                + rewrite map_monad_In_cons.
                  cbn.
                  break_match_goal.
                  * exists s; auto.
                  * specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn))).
                    forward IHl; eauto.
                    destruct IHl as [s IHl].
                    exists s.
                    rewrite IHl.
                    auto.
            Qed.

            (* TODO: move / generalize these *)
            Lemma map_monad_In_err_forall2 :
              forall {A B} l (f : forall (a : A), In a l -> err B) res,
                map_monad_In l f = inr res <->
                  Forall2_HIn l res (fun a b INA INB => f a INA = inr b).
            Proof.
              intros A B.
              induction l; intros f res.
              - split; intros MAP.
                + cbn in *.
                  inv MAP.
                  auto.
                + cbn in *.
                  break_match_hyp; tauto.
              - split; intros MAP.
                + rewrite map_monad_In_unfold in MAP.
                  cbn in *.
                  break_match_hyp; inv MAP.
                  break_match_hyp; inv H0.

                  pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
                  constructor; auto.
                  eapply FORALL. eauto.
                + rewrite map_monad_In_cons.
                  cbn in *.
                  break_match_hyp; try contradiction.
                  cbn in *.
                  destruct MAP as [FA MAP].
                  rewrite FA.

                  pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
                  apply FORALL in MAP.
                  rewrite MAP.
                  auto.
            Qed.

            Lemma map_monad_In_err_succeeds' :
              forall {A B} l (f : forall (a : A), In a l -> err B) res,
                map_monad_In l f = ret res ->
                (forall a (HIn : In a l), exists b, f a HIn = ret b).
            Proof.
              intros A B.
              induction l; intros f res MAP.
              - intros _ [].
              - rewrite map_monad_In_cons in MAP.
                cbn in *.
                break_match_hyp; inv MAP.
                rename H0 into MAP.
                break_match_hyp; inv MAP.

                intros a0 [HIn | HIn]; subst.
                + exists b; auto.
                + apply IHl with (a:=a0) (HIn:=HIn) in Heqs0.
                  auto.
            Qed.

            eapply map_monad_In_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in IHfields.
          cbn in IHfields.
          setoid_rewrite CONCl0 in IHfields.
          setoid_rewrite H in IHfields.
          rewrite Heqs in IHfields.
          rewrite Heqs0 in IHfields.
          cbn in IHfields.
          apply orutt_inv_Ret in IHfields.
          unfold_dvalue_refine_strict_in IHfields.
          rewrite Heqo1 in IHfields.
          cbn in IHfields.
          inv IHfields.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_In_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Packed structs *)
      break_match_hyp; inv H; cbn.
      generalize dependent l.
      induction fields; intros l Heqo.
      + cbn in *. inv Heqo.
        cbn.
        apply orutt_Ret; auto.
        solve_dvalue_refine_strict.
      + rewrite map_monad_In_cons in Heqo.
        cbn in Heqo.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHfields l0 eq_refl).
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        cbn.

        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete fields = forallb is_concrete l0).
        { (* Should follow from Heqo *)
          clear IHfields.
          generalize dependent l0.
          induction fields; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_In_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHfields l eq_refl).
            rewrite IHfields.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_In_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_In_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_In with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_In_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in IHfields.
          cbn in IHfields.
          setoid_rewrite CONCl0 in IHfields.
          setoid_rewrite H in IHfields.
          rewrite Heqs in IHfields.
          rewrite Heqs0 in IHfields.
          cbn in IHfields.
          apply orutt_inv_Ret in IHfields.
          unfold_dvalue_refine_strict_in IHfields.
          rewrite Heqo1 in IHfields.
          cbn in IHfields.
          inv IHfields.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_In_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Arrays *)
      break_match_hyp; inv H.
      generalize dependent l.
      induction elts; intros l Heqo.
      + cbn in *; inv Heqo.
        cbn.
        apply orutt_Ret.
        solve_dvalue_refine_strict.
      + rewrite map_monad_In_cons in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
        cbn.

        specialize (IHelts l0 eq_refl).
        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete elts = forallb is_concrete l0).
        { clear IHelts.
          generalize dependent l0.
          induction elts; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_In_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHelts l eq_refl).
            rewrite IHelts.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_In_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_In_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_In with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_In_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          cbn in IHelts.
          setoid_rewrite CONCl0 in IHelts.
          setoid_rewrite H in IHelts.
          rewrite Heqs in IHelts.
          rewrite Heqs0 in IHelts.
          cbn in IHelts.
          apply orutt_inv_Ret in IHelts.
          unfold_dvalue_refine_strict_in IHelts.
          rewrite Heqo1 in IHelts.
          cbn in IHelts.
          inv IHelts.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_In_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Vectors *)
      break_match_hyp; inv H.
      generalize dependent l.
      induction elts; intros l Heqo.
      + cbn in *; inv Heqo.
        cbn.
        apply orutt_Ret.
        solve_dvalue_refine_strict.
      + rewrite map_monad_In_cons in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
        cbn.

        specialize (IHelts l0 eq_refl).
        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete elts = forallb is_concrete l0).
        { clear IHelts.
          generalize dependent l0.
          induction elts; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_In_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHelts l eq_refl).
            rewrite IHelts.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_In_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_In_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_In with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_In_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          cbn in IHelts.
          setoid_rewrite CONCl0 in IHelts.
          setoid_rewrite H in IHelts.
          rewrite Heqs in IHelts.
          rewrite Heqs0 in IHelts.
          cbn in IHelts.
          apply orutt_inv_Ret in IHelts.
          unfold_dvalue_refine_strict_in IHelts.
          rewrite Heqo1 in IHelts.
          cbn in IHelts.
          inv IHelts.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_In_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* GEP *)
      break_match_hyp; inv H;
        break_match_hyp; inv H1;
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
        cbn;

        eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      {
        apply orutt_trigger; cbn;
          [ split;
            [ tauto
            | unfold_uvalue_refine_strict_goal;
              rewrite_uvalue_convert_strict;
              cbn; rewrite Heqo0;
              auto
            ]
          | intros [t1] [t2] [_ [REF1 REF2]];
            cbn; auto
          | intros o CONTRA;
            inv CONTRA
          ].
      }

      intros [?r1] [?r2] H0;
        cbn in *;
        apply orutt_Ret; auto.
    - (* InsertElement *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* ShuffleVector *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Select *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* ConcatBytes *)
      break_match_hyp; inv H.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
  Qed.

  Lemma denote_exp_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt e)
        (IS2.LLVM.D.denote_exp odt e)
        (OOM:=OOME).
  Proof.
    intros e.
    induction e using AstLib.exp_ind; intros odt;
      try solve
        [ destruct odt as [dt | ];
          [
            cbn;
            destruct dt; cbn;
            try solve [
                apply orutt_raise;
                [intros * CONTRA; dependent destruction CONTRA | cbn; auto]
              | apply orutt_Ret; solve_uvalue_refine_strict
              ]
          | cbn;
            solve_orutt_raise
          ]
        ].

    - apply translate_LU_to_exp_lookup_id_orutt.
    - destruct odt as [dt | ].
      { destruct dt; cbn;
          try solve [
              apply orutt_raise;
              [intros * CONTRA; dependent destruction CONTRA | cbn; auto]
            ].

        { (* Normal integers *)
          pose proof (@IX_supported_dec sz)
            as [SUPPORTED | UNSUPPORTED].
          - inv SUPPORTED;
              repeat rewrite map_ret;
              apply orutt_Ret;
              rewrite uvalue_refine_strict_equation;
              rewrite uvalue_convert_strict_equation;
              cbn;
              reflexivity.
          - repeat rewrite unsupported_cases_match; auto;
              repeat rewrite Raise.raise_map_itree;
              apply orutt_raise;
              [intros * CONTRA; dependent destruction CONTRA | cbn; auto].
        }

        { (* Intptrs *)
          repeat rewrite map_bind.
          eapply orutt_bind with
            (RR:=(fun (ip1 : IS1.LP.IP.intptr) (ip2 : IS2.LP.IP.intptr) => IS1.LP.IP.to_Z ip1 = IS2.LP.IP.to_Z ip2)).
          unfold lift_OOM.
          { break_match; break_match.
            - apply orutt_Ret.
              rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
              erewrite IP.from_Z_to_Z; eauto.
              erewrite IS1.LP.IP.from_Z_to_Z; eauto.
            - apply orutt_raise_oom.
            - (* TODO: Maybe this should be a lemma *)
              rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.

              pose proof intptr_convert_succeeds i as [i2 CONV].
              rewrite IP.from_Z_to_Z with (i:=i) (z:=x) in CONV; eauto.
              rewrite Heqo in CONV. inv CONV.
            - apply orutt_raise_oom.
          }

          intros r1 r2 H.
          do 2 rewrite map_ret.
          apply orutt_Ret.
          cbn.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          cbn.
          rewrite H.
          rewrite IP.to_Z_from_Z; auto.
        }
      }

      cbn.
      solve_orutt_raise.
    - destruct b; cbn;
        apply orutt_Ret; solve_uvalue_refine_strict.
    - cbn; apply orutt_Ret.
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      cbn.
      rewrite AC1.addr_convert_null.
      reflexivity.
    - destruct odt as [dt | ];
          [
          | solve_orutt_raise
          ].

      destruct dt; cbn;
        try solve [ apply orutt_Ret; solve_uvalue_refine_strict
                  | cbn; solve_orutt_raise
          ].

      + unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        break_match.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs.
          rewrite Heqs.
          solve_orutt_raise.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs as [v2 [V2 REF]].
          rewrite V2.
          cbn; apply orutt_Ret.
          apply dvalue_refine_strict_dvalue_to_uvalue; auto.

      + apply orutt_Ret.
        unfold_uvalue_refine_strict.
        cbn.

        rewrite IS1.LP.IP.to_Z_0.
        rewrite IP.from_Z_0.
        reflexivity.
      + unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs.
        * assert (s = s0).
          {
            apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
            rewrite Heqs1 in Heqs2; inv Heqs2.
            auto.
          }
          subst.
          solve_orutt_raise.

        * apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs2 as [dv2 [DEFdv2 REFdv2]].
          rewrite DEFdv2 in Heqs1; inv Heqs1.

          apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_In_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec in IN; subst.
          apply dvalue_refine_strict_dvalue_to_uvalue in REFdv2.
          rewrite REFdv2 in FAIL.
          inv FAIL.
      + (* Struct zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply map_monad_err_fail in Heqs2.
          destruct Heqs2 as [a [IN Heqs2]].
          apply map_monad_err_forall2 in Heqs1.
          apply Util.Forall2_forall in Heqs1 as [LEN Heqs1].
          apply In_Nth in IN as [i NTH].
          pose proof IS1.LLVM.MEM.CP.CONC.MemHelpers.Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs1 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply map_monad_err_fail in Heqs1.
          destruct Heqs1 as [a [IN Heqs1]].
          apply map_monad_err_forall2 in Heqs2.
          apply Util.Forall2_forall in Heqs2 as [LEN Heqs2].
          apply In_Nth in IN as [i NTH].
          pose proof IS1.LLVM.MEM.CP.CONC.MemHelpers.Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs2 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.

          break_match.
          { generalize dependent l0.
            generalize dependent l1.
            generalize dependent l.
            induction fields; intros defs2 DEFS2 conv defs1 DEFS1 CONV.
            - cbn in *.
              inv DEFS1; inv DEFS2.
              cbn in *.
              inv CONV; auto.
            - cbn in *.
              break_match_hyp; inv DEFS1.
              break_match_hyp; inv H0.
              break_match_hyp; inv DEFS2.
              break_match_hyp; inv H0.

              apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs as [dv2 [DEFdv2 REFdv2]].
              rewrite DEFdv2 in Heqs1. inv Heqs1.
              rewrite map_cons in CONV.
              rewrite map_monad_In_cons in CONV.
              cbn in *.
              break_match_hyp; inv CONV.
              break_match_hyp; inv H0.
              specialize (IHfields l0 eq_refl l1 l eq_refl Heqo0).
              inv IHfields.
              pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
              rewrite uvalue_refine_strict_equation in H.
              rewrite Heqo in H.
              inv H.
              reflexivity.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          apply in_map_iff in IN.
          destruct IN as [a' [EQ IN]].
          subst.

          pose proof Heqs2.
          eapply map_monad_err_In in H; eauto.
          destruct H as [y [DEFy INy]].
          pose proof DEFy as A'.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in DEFy as [dv2 [DEFdv2 REFdv2]].
          pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
          rewrite H in FAIL.
          inv FAIL.
      + (* Packed struct zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply map_monad_err_fail in Heqs2.
          destruct Heqs2 as [a [IN Heqs2]].
          apply map_monad_err_forall2 in Heqs1.
          apply Util.Forall2_forall in Heqs1 as [LEN Heqs1].
          apply In_Nth in IN as [i NTH].
          pose proof IS1.LLVM.MEM.CP.CONC.MemHelpers.Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs1 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply map_monad_err_fail in Heqs1.
          destruct Heqs1 as [a [IN Heqs1]].
          apply map_monad_err_forall2 in Heqs2.
          apply Util.Forall2_forall in Heqs2 as [LEN Heqs2].
          apply In_Nth in IN as [i NTH].
          pose proof IS1.LLVM.MEM.CP.CONC.MemHelpers.Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs2 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.

          break_match.
          { generalize dependent l0.
            generalize dependent l1.
            generalize dependent l.
            induction fields; intros defs2 DEFS2 conv defs1 DEFS1 CONV.
            - cbn in *.
              inv DEFS1; inv DEFS2.
              cbn in *.
              inv CONV; auto.
            - cbn in *.
              break_match_hyp; inv DEFS1.
              break_match_hyp; inv H0.
              break_match_hyp; inv DEFS2.
              break_match_hyp; inv H0.

              apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs as [dv2 [DEFdv2 REFdv2]].
              rewrite DEFdv2 in Heqs1. inv Heqs1.
              rewrite map_cons in CONV.
              rewrite map_monad_In_cons in CONV.
              cbn in *.
              break_match_hyp; inv CONV.
              break_match_hyp; inv H0.
              specialize (IHfields l0 eq_refl l1 l eq_refl Heqo0).
              inv IHfields.
              pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
              rewrite uvalue_refine_strict_equation in H.
              rewrite Heqo in H.
              inv H.
              reflexivity.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          apply in_map_iff in IN.
          destruct IN as [a' [EQ IN]].
          subst.

          pose proof Heqs2.
          eapply map_monad_err_In in H; eauto.
          destruct H as [y [DEFy INy]].
          pose proof DEFy as A'.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in DEFy as [dv2 [DEFdv2 REFdv2]].
          pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
          rewrite H in FAIL.
          inv FAIL.
      + (* Vector zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs2 as [dv2 [DEFdv2 REFdv2]].
          rewrite DEFdv2 in Heqs1; inv Heqs1.

          apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_In_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec in IN; subst.
          apply dvalue_refine_strict_dvalue_to_uvalue in REFdv2.
          rewrite REFdv2 in FAIL.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_In_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          rewrite AC1.addr_convert_null in FAIL.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_In_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_In_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_In_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          inv FAIL.
    - (* Cstrings *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Structs *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Struct uvs1) (UVALUE_Struct uvs2))).
      { induction fields.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHfields.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Packed Structs *)
      destruct odt as [dt | ];
        [
        | cbn;
          apply orutt_raise; cbn; auto;
          intros msg o CONTRA;
          inv CONTRA
        ].

      destruct dt; cbn;
        try solve [ apply orutt_Ret; solve_uvalue_refine_strict
                  | cbn;
                    apply orutt_raise; cbn; auto;
                    intros msg o CONTRA;
                    inv CONTRA
          ].

      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Packed_struct uvs1) (UVALUE_Packed_struct uvs2))).
      { induction fields.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHfields.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Arrays *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Vectors *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Vector uvs1) (UVALUE_Vector uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* IBinops *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* ICmps *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* FBinops *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* FCmp *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* Conversion *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      apply orutt_Ret.
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H.
      rewrite H.
      cbn.
      reflexivity.
    - (* GetElementPtr *)
      destruct ptrval as [ptr_t ptrval].
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction idxs.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r0 r3 H1.
          forward IHidxs.
          { intros p H2 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r4 r5 H2.
          cbn in H2.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H2.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_In_cons.
          cbn.
          cbn in H2.
          break_match_hyp; inv H2.
          rewrite uvalue_refine_strict_equation in H1.
          rewrite H1.
          reflexivity.
      }

      intros r0 r3 H1.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H0, H1.
      cbn.
      rewrite H0.
      rewrite uvalue_convert_strict_equation in H1.
      cbn in H1.
      break_match_hyp; inv H1.
      reflexivity.
    - (* ExtractElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H0, H.
      cbn.

      rewrite H, H0.
      reflexivity.
    - (* InsertElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* ShuffleVector *)
      destruct vec1 as [vec1_t vec1].
      destruct vec2 as [vec2_t vec2].
      destruct idxmask as [idxmask_t idxmask].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* ExtractValue *)
      destruct vec as [vec_t vec].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H.
      cbn.

      rewrite H.
      reflexivity.
    - (* InsertValue *)
      destruct vec as [vec_t vec].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      cbn.

      rewrite H, H0.
      reflexivity.
    - (* Select *)
      destruct cnd, v1, v2.
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* Freeze *)
      destruct v; cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind with (RR:=dvalue_refine_strict); eauto.
      apply pick_your_poison_orutt; auto.
      intros r0 r3 H0.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  Lemma GlobalRead_exp_E_E1E2_rutt :
    forall g,
      rutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma GlobalRead_L0_E1E2_rutt :
    forall g,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma Store_E1E2_rutt :
    forall dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      rutt exp_E_refine_strict exp_E_res_refine_strict eq
        (trigger (IS1.LP.Events.Store dt r1 r3))
        (trigger (IS2.LP.Events.Store dt r2 r4)).
  Proof.
    intros dt r1 r2 r3 r4 R1R2 R3R4.
    apply rutt_trigger.
    cbn. tauto.

    intros [] [] _.
    reflexivity.
  Qed.

  Lemma initialize_global_E1E2_orutt :
    forall g,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (LLVM1.initialize_global g)
        (LLVM2.initialize_global g)
        (OOM:=OOME).
  Proof.
    intros g.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { apply rutt_orutt.
      apply GlobalRead_exp_E_E1E2_rutt.
      intros A e2.

      (* TODO: move this! *)
      Lemma exp_E_dec_oom :
        forall A (e : exp_E A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
      Proof.
        intros A s.
        repeat destruct s;
          try solve
            [
              left;
              intros o CONTRA;
              inv CONTRA
            ].

        right.
        exists o.
        reflexivity.
      Qed.

      apply exp_E_dec_oom.
    }

    intros r1 r2 R1R2.
    apply orutt_bind with (RR:=uvalue_refine_strict).
    { break_match.
      apply denote_exp_E1E2_orutt.
      eapply orutt_Ret.
      solve_uvalue_refine_strict.
    }

    intros r3 r4 R3R4.
    apply rutt_orutt; [| apply exp_E_dec_oom].
    apply Store_E1E2_rutt; auto.
  Qed.

  Lemma initialize_globals_E1E2_orutt :
    forall m_globals,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (map_monad LLVM1.initialize_global m_globals)
        (map_monad initialize_global m_globals)
        (OOM:=OOME).
  Proof.
    cbn.

    induction m_globals.
    { cbn.
      apply orutt_Ret.
      reflexivity.
    }
    { rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      apply orutt_bind with (RR:=eq).
      apply initialize_global_E1E2_orutt.

      intros [] [] _.
      apply orutt_bind with (RR:=eq).
      apply IHm_globals.

      intros r1 r2 R1R2; subst.
      apply orutt_Ret.
      reflexivity.
    }
  Qed.

  Lemma build_global_environment_E1E2_orutt_strict_sound :
    forall (m : mcfg dtyp),
      orutt
        event_refine_strict
        event_res_refine_strict
        eq
        (LLVM1.build_global_environment m)
        (LLVM2.build_global_environment m)
        (OOM:=OOME).
  Proof.
    destruct m.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).

      (* TODO: move this! *)
      Lemma L0_dec_oom :
        forall A (e : L0 A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
      Proof.
        intros A s.
        repeat destruct s;
          try solve
            [
              left;
              intros o CONTRA;
              inv CONTRA
            ].

        right.
        exists o.
        reflexivity.
      Qed.

      (* In the future this allocate_one_E1E2_rutt_strict_sound lemma may be orutt *)
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_one_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_global_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    eapply translate_exp_to_L0_E1E2_orutt.
    apply orutt_bind with (RR:=eq).
    apply initialize_globals_E1E2_orutt.

    intros r1 r2 R1R2; subst.
    apply orutt_Ret.
    reflexivity.
  Qed.

  Definition function_denotation_refine_strict : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_refine_strict args1 args2 ->
               rutt L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
                 (d1 args1)
                 (d2 args2)
           ).
  Defined.

  Definition function_denotation_converted_lazy : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_converted_lazy args1 args2 ->
               rutt L0'_refine_lazy L0'_res_refine_lazy uvalue_converted_lazy
                 (d1 args1)
                 (d2 args2)
           ).
  Defined.

  Lemma denote_ocfg_rutt :
    forall cfg bids,
      rutt L0'_refine_strict L0'_res_refine_strict (sum_rel (eq × eq) uvalue_refine_strict)
        (translate IS1.LP.Events.instr_to_L0'
           (IS1.LLVM.D.denote_ocfg cfg bids))
        (translate instr_to_L0'
           (denote_ocfg cfg bids)).
  Proof.
    intros cfg [bid_from bid_src].
    induction cfg.
    - unfold denote_ocfg, IS1.LLVM.D.denote_ocfg.
  Admitted.

  (* TODO: Move these combine_lists lemmas *)
  Lemma combine_lists_err_inl_contra :
    forall {X Y} (xs : list X) (ys : list Y) msg,
      ~ (combine_lists_err xs ys = inl msg).
  Proof.
    intros X Y.
    induction xs, ys; intros msg CONTRA;
      inv CONTRA.
    destruct (combine_lists_err xs ys) eqn:COMB.
    apply IHxs in COMB; auto.
    inv H0.
  Qed.

  Lemma combine_lists_err_length_eq :
    forall {A B C D} xs1 ys1 xs2 ys2 zs1 zs2,
      @combine_lists_err A B xs1 ys1 = inr zs1 ->
      @combine_lists_err C D xs2 ys2 = inr zs2 ->
      length ys1 = length ys2 ->
      length xs1 = length xs2 ->
      length zs1 = length zs2.
  Proof.
    intros A B C D.
    induction xs1, ys1, xs2, ys2;
      intros zs1 zs2
        COMB1 COMB2 LEN1 LEN2;
      try solve [cbn in *;
                 inv COMB1; inv COMB2;
                 auto
                | inv LEN1; inv LEN2
        ].
    cbn in *.

    destruct (combine_lists_err xs1 ys1) eqn:COMB1';
      inv COMB1.

    destruct (combine_lists_err xs2 ys2) eqn:COMB2';
      inv COMB2.
    cbn.
    apply Nat.succ_inj_wd.
    eapply IHxs1; eauto.
  Qed.

  Import Util.
  Lemma combine_lists_err_Nth :
    forall {X Y} xs ys (x : X) (y : Y) zs i,
      Nth xs i x ->
      Nth ys i y ->
      combine_lists_err xs ys = inr zs ->
      Nth zs i (x, y).
  Proof.
    intros X Y.
    induction xs, ys;
      intros x' y' zs i NTH_xs NTH_ys COMB;
      cbn in *;
      try
        solve [ apply not_Nth_nil in NTH_xs; contradiction
              | apply not_Nth_nil in NTH_ys; contradiction
        ].

    destruct (combine_lists_err xs ys) eqn:COMB';
      inv COMB.

    destruct i.
    - cbn in *.
      inv NTH_xs; inv NTH_ys.
      reflexivity.
    - cbn in *.
      eauto.
  Qed.

  Lemma combine_lists_err_Nth_inv :
    forall {X Y} xs ys (x : X) (y : Y) zs i,
      Nth zs i (x, y) ->
      combine_lists_err xs ys = inr zs ->
      Nth xs i x /\ Nth ys i y.
  Proof.
    intros X Y.
    induction xs, ys;
      intros x' y' zs i NTH COMB;
      try
        solve [ cbn in COMB; inv COMB;
                apply not_Nth_nil in NTH; contradiction
        ].

    cbn in *.
    destruct (combine_lists_err xs ys) eqn:COMB';
      inv COMB.

    destruct i.
    - cbn in *.
      inv NTH.
      auto.
    - cbn in *.
      eauto.
  Qed.

  Lemma address_one_function_E1E2_rutt :
    forall dfn,
      rutt event_refine_strict event_res_refine_strict (dvalue_refine_strict × function_denotation_refine_strict)
        (LLVM1.address_one_function dfn)
        (LLVM2.address_one_function dfn).
  Proof.
    intros dfn.
    cbn.
    eapply rutt_bind with (RR:=dvalue_refine_strict).
    apply GlobalRead_L0_E1E2_rutt.

    intros r1 r2 R1R2.
    apply rutt_Ret.

    constructor.
    - cbn; auto.
    - cbn.
      red.
      intros args1 args2 ARGS.
      cbn.
      eapply rutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)).
      { cbn.
        pose proof (Util.Forall2_length ARGS) as LEN.
        destruct (IS1.LLVM.D.combine_lists_err (LLVMAst.df_args dfn) args1) eqn:HARGS1.
        { (* Error, means args1 differs in length *)
          (* Currently combine_lists_err does not ever error... This
             may change in the future.*)
          apply combine_lists_err_inl_contra in HARGS1.
          contradiction.
        }

        { assert (length args1 = length args2) as ARGSLEN by eauto using Util.Forall2_length.
          cbn.
          destruct (combine_lists_err (LLVMAst.df_args dfn) args2) eqn:HARGS2.
          apply combine_lists_err_inl_contra in HARGS2; contradiction.

          (* I know args2 is a uvalue refinement of args1.

             I also know that in HARGS1 and HARGS2, args1 and args2
             are being combined with the same list.

             This should mean that `l` and `l0` have the same length...

             And also something like...

             Forall2 (eq × uvalue_refine) l l0
           *)

          assert (Forall2 (eq × uvalue_refine_strict) l l0) as LL0.
          { assert (length l = length l0) as LENLL0.
            { eapply combine_lists_err_length_eq; eauto.
            }

            cbn.
            apply Util.Forall2_forall.
            split; auto.

            intros i a b NTHl NTHl0.
            destruct a as [a1 a2].
            destruct b as [b1 b2].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl HARGS1) as [AARGS AARGS1].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl0 HARGS2) as [BARGS BARGS1].

            constructor; cbn.
            - cbn in *.
              rewrite AARGS in BARGS.
              inv BARGS.
              reflexivity.
            - eapply Forall2_Nth; eauto.
          }

          cbn.
          apply rutt_Ret; auto.
        }
      }


      intros params1 params2 PARAMS.
      eapply rutt_bind with (RR:=eq).
      { apply rutt_trigger.
        cbn; auto.

        intros [] [] _.
        reflexivity.
      }

      intros [] [] _.

      eapply rutt_bind with (RR:=eq).
      { apply rutt_trigger.
        - cbn.
          induction PARAMS.
          + apply local_refine_strict_empty.
          + destruct x as [xid xuv].
            destruct y as [yid yuv].
            inv H.
            cbn in fst_rel, snd_rel. subst.
            apply alist_refine_cons; auto.
        - intros [] [] _.
          reflexivity.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=uvalue_refine_strict).
      { rewrite translate_bind.
        rewrite translate_bind.

        eapply rutt_bind with (RR:=sum_rel (eq × eq) uvalue_refine_strict).
        { (* ocfg stuff *)
          apply denote_ocfg_rutt.
        }

        intros r0 r3 H.
        inv H.
        - inv H0.
          destruct a1, a2.
          cbn in *.
          subst.
          unfold LLVMEvents.raise.
          rewrite bind_trigger.
          rewrite bind_trigger.
          rewrite translate_vis.
          rewrite translate_vis.
          cbn.
          apply rutt_Vis; cbn; auto.
          tauto.
        - do 2 rewrite translate_ret.
          apply rutt_Ret.
          auto.
      }

      intros r0 r3 R0R3.
      eapply rutt_bind with (RR:=eq).
      { eapply rutt_trigger.
        cbn; auto.
        intros [] [] _.
        reflexivity.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq).
      { eapply rutt_trigger.
        cbn; auto.
        intros [] [] _.
        reflexivity.
      }

      intros [] [] _.
      eapply rutt_Ret.
      auto.
  Qed.

  Lemma address_one_functions_E1E2_rutt :
    forall dfns,
      rutt event_refine_strict event_res_refine_strict
        (Forall2 (dvalue_refine_strict × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_function dfns)
        (map_monad address_one_function dfns).
  Proof.
    induction dfns.
    { cbn.
      apply rutt_Ret.
      constructor.
    }
    { do 2 rewrite map_monad_unfold.
      eapply rutt_bind.
      apply address_one_function_E1E2_rutt.

      intros r1 r2 R1R2.
      eapply rutt_bind.
      eapply IHdfns.

      intros r0 r3 R0R3.

      apply rutt_Ret.
      constructor; auto.
    }
  Qed.

  (* Typeclass? *)
  (* Deterministic...? *)
  (* Inversion? *)
  Definition R2_injective
    {R1 R2} (RR : R1 -> R2 -> Prop) : Prop :=
    forall (r1 : R1) (r2 : R2) a b,
      RR r1 r2 ->
      RR a b ->
      a = r1 <-> b = r2.

  Definition R2_deterministic
    {R1 R2} (RR : R1 -> R2 -> Prop) : Prop :=
    forall (r1 : R1) (r2 : R2) a b,
      RR r1 r2 ->
      RR a b ->
      a = r1 -> b = r2.

  Lemma dvalue_converted_lazy_R2_deterministic :
    R2_deterministic dvalue_converted_lazy.
  Proof.
    red.
    intros r1 r2 a b R1R2 AB.
    unfold dvalue_converted_lazy in *.
    intros EQ; subst; auto.
  Qed.

  Lemma assoc_similar_lookup :
    forall {A B C D}
      `{RDA : @RelDec.RelDec A eq}
      `{RDC : @RelDec.RelDec C eq}
      `{RDCA : @RelDec.RelDec_Correct _ _ RDA}
      `{RDCC : @RelDec.RelDec_Correct _ _ RDC}
      (RAC : A -> C -> Prop)
      (RBD : B -> D -> Prop)
      (xs : list (A * B)%type)
      (ys : list (C * D)%type)
      a b,
      R2_injective RAC ->
      Forall2 (RAC × RBD) xs ys ->
      assoc a xs = Some b ->
      exists c d i,
        assoc c ys = Some d /\
          Nth xs i (a, b) /\
          Nth ys i (c, d).
  Proof.
    intros A B C D RDA RDC RDCA RDCC RAC RBD xs.
    induction xs, ys; intros a' b' RINJ ALL ASSOC.
    - cbn in *; inv ASSOC.
    - cbn in *; inv ASSOC.
    - inv ALL.
    - inv ALL.
      cbn in ASSOC.
      destruct a.
      break_match_hyp.
      + assert (a' = a) as AA by
            (eapply RelDec.rel_dec_correct; eauto);
          subst.

        inv ASSOC.
        destruct p.
        inv H2.
        cbn in *.

        red in RINJ.
        exists c. exists d. exists 0%nat.
        rewrite RelDec.rel_dec_eq_true; auto.
      + specialize (IHxs _ _ _ RINJ H4 ASSOC).
        destruct IHxs as [c [d [i [ASSOC' [NTH1 NTH2]]]]].
        exists c. exists d. exists (S i).
        cbn.
        break_inner_match_goal.
        subst.
        cbn in *.
        break_inner_match_goal.
        { (* c = c0 *)
          (* Should be a contradiction using RINJ, Heqb0, and Heqb1 *)
          inv H2.
          cbn in *.

          assert (c = c0) as CC by
              (eapply RelDec.rel_dec_correct; eauto).

          red in RINJ.
          apply Forall2_forall in H4 as [LEN NTH].
          specialize (NTH _ _ _ NTH1 NTH2).
          inv NTH.
          cbn in *.

          assert (a' = a).
          { eapply RINJ; eauto. }
          subst.

          eapply RelDec.neg_rel_dec_correct in Heqb0.
          contradiction.
        }

        tauto.
  Qed.

  (* TODO: move these? *)
  (* Lemma lookup_defn_some_converted : *)
  (*   forall dfns1 dfns2 r1 r2 f_den1, *)
  (*     Forall2 (dvalue_converted × function_denotation_converted) dfns1 dfns2 -> *)
  (*     dvalue_converted r1 r2 -> *)
  (*     IS1.LLVM.D.lookup_defn r1 dfns1 = Some f_den1 -> *)
  (*     exists f_den2, *)
  (*       IS2.LLVM.D.lookup_defn r2 dfns2 = Some f_den2 /\ *)
  (*         function_denotation_converted f_den1 f_den2. *)
  (* Proof. *)
  (*   intros dfns1 dfns2 r1 r2 f_den1 DFNS R1R2 LUP. *)

  (*   pose proof DFNS as NTH. *)
  (*   apply Forall2_forall in NTH as [LEN NTH]. *)

  (*   pose proof LUP as LUP'. *)
  (*   eapply assoc_similar_lookup with *)
  (*     (xs:=dfns1) (ys:=dfns2) (a:=r1) (b:=f_den1) in LUP'; *)
  (*     eauto. *)
  (*   2: { *)
  (*     apply dvalue_refine_R2_injective. *)
  (*   } *)

  (*   destruct LUP' as [c [d [i [ASSOC [NTH1 NTH2]]]]]. *)
  (*   exists d. *)

  (*   pose proof (NTH i (r1, f_den1) (c, d) NTH1 NTH2). *)
  (*   inv H; cbn in *. *)
  (*   split; auto. *)

  (*   assert (c = r2) as CR2. *)
  (*   { eapply dvalue_refine_R2_injective; eauto. *)
  (*   } *)

  (*   subst. *)
  (*   auto. *)
  (* Qed. *)

  Lemma assoc_similar_no_lookup :
    forall {A B C D}
      `{RDA : @RelDec.RelDec A eq}
      `{RDC : @RelDec.RelDec C eq}
      `{RDCA : @RelDec.RelDec_Correct _ _ RDA}
      `{RDCC : @RelDec.RelDec_Correct _ _ RDC}
      (RAC : A -> C -> Prop)
      (RBD : B -> D -> Prop)
      (xs : list (A * B)%type)
      (ys : list (C * D)%type)
      a,
      R2_injective RAC ->
      Forall2 (RAC × RBD) xs ys ->
      assoc a xs = None ->
      forall c,
        RAC a c ->
        assoc c ys = None.
  Proof.
    intros A B C D RDA RDC RDCA RDCC RAC RBD xs.
    induction xs, ys; intros a' RINJ ALL ASSOC.
    - cbn in *; auto.
    - cbn in *; inv ALL.
    - inv ALL.
    - inv ALL.
      cbn in ASSOC.
      destruct a.
      break_match_hyp.
      + inv ASSOC.
      + specialize (IHxs _ _ RINJ H4 ASSOC).
        intros c H.
        specialize (IHxs _ H).
        inv H2.
        cbn in *.
        destruct p; cbn in *.
        break_match.
        { assert (c = c0) as CC by
              (eapply RelDec.rel_dec_correct; eauto).
          subst.
          exfalso.

          red in RINJ.
          pose proof RINJ _ _ _ _ H fst_rel.
          apply RelDec.neg_rel_dec_correct in Heqb0.
          apply Heqb0.
          symmetry; apply H0; auto.
        }
        auto.
  Qed.

  (* (* May not be true with new dvalue_refine *) *)
  (* Lemma lookup_defn_none : *)
  (*   forall dfns1 dfns2 r1 r2, *)
  (*     Forall2 (dvalue_refine × function_denotation_refine) dfns1 dfns2 -> *)
  (*     dvalue_refine r1 r2 -> *)
  (*     IS1.LLVM.D.lookup_defn r1 dfns1 = None -> *)
  (*     IS2.LLVM.D.lookup_defn r2 dfns2 = None. *)
  (* Proof. *)
  (*   intros dfns1 dfns2 r1 r2 ALL. *)
  (*   revert r1. revert r2. *)
  (*   induction ALL; intros r2 r1 REF LUP; *)
  (*     cbn in *; auto. *)

  (*   destruct x, y. *)
  (*   cbn in *. *)

  (*   inv H. *)
  (*   cbn in *. *)

  (*   break_match_hyp; inv LUP. *)
  (*   eapply RelDec.neg_rel_dec_correct in Heqb. *)
  (*   pose proof dvalue_refine_R2_injective _ _ _ _ REF fst_rel. *)
  (*   assert (d0 <> r2). *)
  (*   { intros D0R2. *)
  (*     apply H in D0R2; auto. *)
  (*   } *)
  (*   { assert (r2 <> d0) by auto. *)
  (*     apply RelDec.neg_rel_dec_correct in H2. *)
  (*     rewrite H2. *)
  (*     eapply assoc_similar_no_lookup with (xs:=l) (RAC:=dvalue_refine); eauto. *)
  (*     apply dvalue_refine_R2_injective. *)
  (*   } *)
  (* Qed. *)

  (* TODO: Move? *)
  Lemma dvalue_refine_lazy_oom :
    forall dv dt,
      DV1.dvalue_has_dtyp dv dt ->
      dvalue_refine_lazy dv (DV2.DVALUE_Oom dt).
  Proof.
    intros dv dt H.
    destruct dv;
    rewrite dvalue_refine_lazy_equation; right; auto.
  Qed.

  (* TODO: Move? *)
  Lemma uvalue_refine_lazy_oom :
    forall uv dt,
      DV1.uvalue_has_dtyp uv dt ->
      uvalue_refine_lazy uv (DV2.UVALUE_Oom dt).
  Proof.
    intros uv dt H.
    destruct uv;
    rewrite uvalue_refine_lazy_equation; right; auto.
  Qed.

  (* TODO: move to ListUtils *)
  Lemma map_In_length :
    forall {X Y} (l : list X) (f : forall (x : X), In x l -> Y),
      length (map_In l f) = length l.
  Proof.
    induction l; intros f.
    - cbn. auto.
    - rewrite map_In_cons.
      cbn.
      congruence.
  Qed.

  (* TODO: move to ListUtils *)
  Lemma Nth_map_In_iff:
    forall {X Y : Type} (xs : list X) (f : forall x : X, In x xs -> Y) (i : nat) (y : Y),
      Nth (map_In xs f) i y <-> (exists (x : X) IN, f x IN = y /\ Nth xs i x).
  Proof.
  Admitted.

  (* TODO: Move this *)
  Lemma map_monad_err_forall2_HIn:
    forall {A B : Type} (f : A -> err B) (l : list A) (res : list B),
      map_monad f l = inr res <->
        Forall2_HIn l res (fun (a : A) (b : B) (INA : In a l) (INB : In b res) => f a = inr b).
  Proof.
  Admitted.

  Lemma map_monad_err_length :
    forall {A B} l (f : A -> err B) res,
      map_monad f l = inr res ->
      length l = length res.
  Proof.
    intros A B l.
    induction l; intros f res H.
    - rewrite map_monad_err_nil in H; subst; auto.
    - rewrite map_monad_unfold in H.
      cbn in *.
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      apply IHl in Heqs0.
      cbn.
      auto.
  Qed.

  (* TODO: Move to list utils *)
  Lemma in_map_In :
    forall {A B} l x (f : forall (a : A) (INA : In a l), B) (INX : In x l),
      In (f x INX) (map_In l f).
  Proof.
    intros A B l; induction l; firstorder (subst; auto).
    rewrite map_In_cons.
    cbn.
    destruct INX; subst; auto.
    right.
    specialize (IHl x (fun (x0 : A) (IN : In x0 l) => f x0 (or_intror IN)) i).
    cbn in IHl.
    auto.
  Qed.

  Lemma in_map_In' :
    forall {A B} l x (f : forall (a : A), B) (INX : In x l),
      In (f x) (map_In l (fun x (INX : In x l) => f x)).
  Proof.
    intros A B l; induction l; firstorder (subst; auto).
  Qed.

  (* TODO: Should go in the library *)
  Lemma rutt_weaken :
    forall {E1 E2} {R1 R2}
      (PRE1 PRE2 : prerel E1 E2)
      (POST1 POST2 : postrel E1 E2)
      (ResR1 ResR2 : R1 -> R2 -> Prop)
      t1 t2,
      rutt PRE1 POST1 ResR1 t1 t2 ->
      (forall {A B} e1 e2, (PRE1 A B e1 e2 -> PRE2 _ _ e1 e2)) ->
      (forall {A B} e1 r1 e2 r2, (POST2 A B e1 r1 e2 r2 -> POST1 _ _ e1 r1 e2 r2)) ->
      (forall r1 r2, (ResR1 r1 r2 -> ResR2 r1 r2)) ->
      rutt PRE2 POST2 ResR2 t1 t2.
  Proof.
    intros E1 E2 R1 R2 PRE1 PRE2 POST1 POST2 ResR1 ResR2.

    Hint Resolve rutt_monot : paco.
    Hint Constructors ruttF : itree.
    Hint Unfold rutt_ : itree.
    Hint Unfold rutt : itree.

    pcofix CIH. pstep. intros t1 t2 RUTT. punfold RUTT.
    red in RUTT |- *. induction RUTT; pclearbot; eauto 7 with paco itree.

    intros H2 H3 H4.
    constructor; auto.
    intros a b H1.
    apply H3 in H1.
    apply H0 in H1.
    pclearbot.
    eauto with paco itree.
  Qed.

  (* TODO: Should go in the library *)
  (* TODO: MOVE INTO ORUTT STUFF *)
  Lemma orutt_weaken :
    forall {E1 E2 OOM} `{OOME : OOM -< E2} {R1 R2}
      (PRE1 PRE2 : prerel E1 E2)
      (POST1 POST2 : postrel E1 E2)
      (ResR1 ResR2 : R1 -> R2 -> Prop)
      t1 t2,
      orutt PRE1 POST1 ResR1 t1 t2 (OOM:=OOM) ->
      (forall {A B} e1 e2, (PRE1 A B e1 e2 -> PRE2 _ _ e1 e2)) ->
      (forall {A B} e1 r1 e2 r2, (POST2 A B e1 r1 e2 r2 -> POST1 _ _ e1 r1 e2 r2)) ->
      (forall r1 r2, (ResR1 r1 r2 -> ResR2 r1 r2)) ->
      orutt PRE2 POST2 ResR2 t1 t2 (OOM:=OOM).
  Proof.
    intros E1 E2 OOM OOME R1 R2 PRE1 PRE2 POST1 POST2 ResR1 ResR2.

    Hint Resolve orutt_monot : paco.
    Hint Constructors oruttF : itree.
    Hint Unfold orutt_ : itree.
    Hint Unfold orutt : itree.

    pcofix CIH. pstep. intros t1 t2 RUTT. punfold RUTT.
    red in RUTT |- *. induction RUTT; pclearbot; eauto 7 with paco itree.

    intros H2 H3 H4.
    apply OOMRutt.EqVis; auto.
    intros a b H5.
    apply H3 in H5.
    apply H0 in H5.
    pclearbot.
    eauto with paco itree.
  Qed.

  (* TODO: Move this *)
  (* TODO: May not hold for addresses / iptr depending on their size *)
  (* May be weird for integer sizes as well... *)
  Lemma undef_not_unique_prop :
    forall dt,
      dt <> DTYPE_Void ->
      ~ unique_prop (UVALUE_Undef dt).
  Proof.
    induction dt;
      intros NVOID;
      try contradiction.

  (*   { intros [dv UNIQUE]. *)
  (*     setoid_rewrite concretize_equation in UNIQUE. *)
  (*     unfold concretize_u in UNIQUE. *)
  (*     cbn in UNIQUE. *)

  (*     induction (dvalue_has_dtyp dv (DTYPE_I a)). *)
  (*   } *)
  (*   red in UNIQUE. *)
  (*   assert (dt = DTYPE_Void). *)
  (*   admit. *)
  (*   subst. *)
  (*   destruct UNIQUE as [dv UNIQUE]. *)
  (*   specialize (UNIQUE DVALUE_None). *)
  (*   unfold concretize, concretize_u in UNIQUE. *)
  (*   rewrite concretize_uvalueM_equation in UNIQUE. *)
  (*   cbn in *. *)
  (*   forward UNIQUE. *)
  (*   constructor. *)
  (*   subst. *)
  (* Qed. *)
  Admitted.


  (* (* Maybe I can use something like this for uvalue_refine_unique_prop *) *)
  (* Lemma convert_concretize : *)
  (*   uvalue_convert uv1 = uv2 -> *)
  (*   concretize uv2 dv2 -> *)
  (*   (exists t, dv2 = DVALUE_Oom t) (* May need to be a contains OOM predicate *) \/ *)
  (*     (exists dv1, concretize uv1 dv1 /\ *)
  (*               dvalue_convert dv1 = dv2). *)
  (* Qed. *)

  (* Lemma blah : *)
  (*   forall uv1 dv1, *)
  (*     concretize uv1 dv1 -> *)
  (*     concretize (uvalue_convert uv1) (dvalue_convert dv1). *)
  (* Qed. *)

  (* Lemma blah2  : *)
  (*   IS1.LLVM.D.unique_prop uv1 -> unique_prop (uvalue_convert uv1) *)

  (* (* Change unique_prop to be a specific dvalue instead of existential? *) *)

  Lemma uvalue_refine_strict_unique_prop :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      IS1.LLVM.D.unique_prop uv1 -> unique_prop uv2.
  Proof.
    intros uv1 uv2 REF UNIQUE.

    unfold unique_prop.
    unfold IS1.LLVM.D.unique_prop in UNIQUE.
    destruct UNIQUE as [dv1 UNIQUE].

  (*   split. *)
  (*   { revert uv2 H. *)
  (*     induction uv1 using IS1.LP.Events.DV.uvalue_ind'; intros uv2 REF [dv UNIQUE]; *)
  (*       try *)
  (*         solve *)
  (*         [ *)
  (*           red in REF; *)
  (*           rewrite uvalue_convert_strict_equation in REF; *)
  (*           cbn in REF; *)
  (*           first [break_match_hyp; inv REF | inv REF]; *)
  (*           eexists; *)
  (*           intros dv0 CONC; *)
  (*           do 2 red in CONC; *)
  (*           rewrite concretize_uvalueM_equation in CONC; *)
  (*           inv CONC; *)
  (*           auto *)
  (*         ]. *)

  (*     { (* Undef will be a contradiction in most cases... *) *)
  (* (*          Though not all *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Struct nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Structs *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Packed struct nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Packed structs *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Array nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Arrays *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Vector nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Vectors *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* IBinop *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF. *)
  (*       first [ *)
  (*           break_match_hyp; inv REF; *)
  (*           break_match_hyp; inv H0 *)
  (*         | *)
  (*           break_match_hyp; inv REF | inv REF]. *)

  (*       red. *)
  (*       eexists. *)
  (*       intros dv0 CONC. *)

  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       destruct CONC as [ma [k' [MA [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; subst; cbn in CONC1, CONC2. *)
  (*       - (* OOM *) *)
  (*         inv CONC1. *)
  (*       - (* UB *) *)
  (*         (* May be a contradiction with UNIQUE? *) *)
  (*         rename dv into BLAH. *)
  (*         admit. *)
  (*       - (* Error *) *)
  (*         admit. *)
  (*       - (* Success *) *)
  (*         destruct CONC2 as [[] | CONC2]. *)
  (*         specialize (CONC2 ma0 eq_refl). *)
  (*         red in CONC2. *)
  (*         destruct CONC2 as [ma [k'0 CONC2]]. *)
  (*         destruct CONC2 as [CONC2 [CONC2_EQV CONC2_RET]]. *)

  (*         rewrite concretize_uvalueM_equation in CONC2. *)

  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       (* specialize (CONC2 [] eq_refl). *) *)
  (*       (* set (k'_nil := k' []). *) *)
  (*       (* destruct_err_ub_oom k'_nil; subst k'_nil; *) *)
  (*       (*   rewrite Hx in CONC2, CONC1; *) *)
  (*       (*   try contradiction. *) *)

  (*       (* cbn in CONC1. *) *)
  (*       (* inv CONC1. *) *)
  (*       (* reflexivity. *) *)
  (*       admit. *)
  (*     } *)
  Admitted.

  (* Lemma pickUnique_lazy_rutt : *)
  (*   forall uv1 uv2, *)
  (*     uvalue_refine_lazy uv1 uv2 -> *)
  (*     rutt (sum_prerel call_refine_lazy event_refine_lazy) *)
  (*       (sum_postrel call_res_refine_lazy event_res_refine_lazy) dvalue_refine_lazy *)
  (*       (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2). *)
  (* Proof. *)
  (*   (* intros uv1 uv2 REF. *) *)
  (*   (* unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick. *) *)
  (*   (* unfold pickUnique, concretize_or_pick. *) *)
  (*   (* cbn. *) *)
  (*   (* break_match; *) *)
  (*   (*   eapply uvalue_convert_lazy_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto; *) *)
  (*   (*   rewrite Heqb. *) *)

  (*   (* apply lift_err_uvalue_to_dvalue_rutt; auto. *) *)

  (*   (* repeat rewrite bind_trigger. *) *)
  (*   (* apply rutt_Vis. *) *)

  (*   (* { constructor. *) *)
  (*   (*   cbn. *) *)
  (*   (*   split; auto. *) *)
  (*   (*   apply uvalue_refine_lazy_unique_prop; *) *)
  (*   (*     eauto. *) *)
  (*   (* } *) *)

  (*   (* intros t1 t2 H. *) *)
  (*   (* apply rutt_Ret. *) *)
  (*   (* destruct t1, t2. *) *)
  (*   (* cbn in *. *) *)
  (*   (* destruct H; cbn in *. *) *)
  (*   (* { red in H. *) *)
  (*   (*   destruct e1; cbn in *. *) *)
  (*   (*   destruct d1; cbn in *. *) *)
  (*   (*   admit. (* ???? *) *) *)
  (*   (* } *) *)
  (*   (* { destruct e2; cbn in *. *) *)
  (*   (*   admit. *) *)
  (*   (*   cbn in *. *) *)
  (*   (*   destruct d2; cbn in *. *) *)
  (*   (*   repeat (destruct s; try inv H). *) *)
  (*   (*   admit. *) *)
  (*   (* } *) *)
  (* Admitted. *)

  Lemma lift_err_uvalue_to_dvalue_rutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      rutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2)).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply rutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply rutt_raise; constructor; cbn; auto
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply rutt_raise;
          constructor;
          constructor
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply rutt_raise; constructor; constructor
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply rutt_raise; constructor; constructor
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  (* Lemma pickUnique_rutt_strict : *)
  (*   forall uv1 uv2, *)
  (*     uvalue_refine_strict uv1 uv2 -> *)
  (*     rutt (sum_prerel call_refine_strict event_refine_strict) *)
  (*       (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict *)
  (*       (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2). *)
  (* Proof. *)
  (*   intros uv1 uv2 REF. *)
  (*   unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick. *)
  (*   unfold pickUnique, concretize_or_pick. *)
  (*   cbn. *)
  (*   break_match; *)
  (*     eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto; *)
  (*     rewrite Heqb. *)

  (*   apply lift_err_uvalue_to_dvalue_rutt; auto. *)

  (*   repeat rewrite bind_trigger. *)
  (*   apply rutt_Vis. *)

  (*   { constructor. *)
  (*     cbn. *)
  (*     split; auto. *)
  (*     apply uvalue_refine_strict_unique_prop; *)
  (*       eauto. *)
  (*   } *)

  (*   intros t1 t2 H. *)
  (*   apply rutt_Ret. *)
  (*   destruct t1, t2. *)
  (*   cbn in *. *)
  (*   destruct H; cbn in *. *)
  (*   { red in H. *)
  (*     destruct e1; cbn in *. *)
  (*     destruct d1; cbn in *. *)
  (*     admit. (* ???? *) *)
  (*   } *)
  (*   { destruct e2; cbn in *. *)
  (*     admit. *)
  (*     cbn in *. *)
  (*     destruct d2; cbn in *. *)
  (*     repeat (destruct s; try inv H). *)
  (*     admit. *)
  (*   } *)
  (* Admitted. *)

  (* Lemma uvalue_refine_concretize_poison : *)
  (*   forall uv1 uv2, *)
  (*     uvalue_refine uv1 uv2 -> *)
  (*     (forall dt : dtyp, ~ IS1.LLVM.MEM.CP.CONC.concretize uv1 (IS1.LP.Events.DV.DVALUE_Poison dt)) <-> *)
  (*       (forall dt : dtyp, ~ concretize uv2 (DVALUE_Poison dt)). *)
  (* Proof. *)
  (*   (* This may not be true if uv2 can OOM... *) *)
  (* Admitted. *)

  Lemma denote_mcfg_E1E2_orutt' :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      (Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2) ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      call_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) (Call dt f2 args2) ->
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 DFNS F1F2 ARGS PRE12.
    unfold IS1.LLVM.D.denote_mcfg.
    unfold denote_mcfg.
    cbn in PRE12.
    destruct PRE12 as [DT [CONVf1f2 MAPM12]]; subst.

    eapply mrec_orutt with (RPreInv:=call_refine_strict).
    { intros A B d1 d2 PRE.

      cbn.
      destruct d1.
      destruct d2.

      cbn in PRE.

      eapply orutt_bind with (RR:=(fun r1 r2 => dvalue_refine_strict r1 r2)).
      { (* This may be tricky... *)
        (* Hopefully follows from uvalue_convert f = NoOom f0 in PRE *)
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        destruct PRE as [T [UV ARGS_CONV]]; subst.

        break_match;
          eapply uvalue_refine_strict_preserves_is_concrete in Heqb;
          eauto; rewrite Heqb.
        - (* Concrete so just use uvalue_to_dvalue (simple) conversion *)
          apply lift_err_uvalue_to_dvalue_rutt_ref; auto.
        - (* Not concrete, trigger pick events *)
          eapply rutt_bind with (RR:= fun (t1 : {_ : IS1.LP.Events.DV.dvalue | True}) (t2 : {_ : dvalue | True}) => dvalue_convert (proj1_sig t1) = (proj1_sig t2)) .
          { apply rutt_trigger.
            { constructor.
              cbn.
              tauto.
            }

            { intros t1 t2 H.
              inv H.
              cbn in *.
              apply inj_pair2 in H0, H3, H4, H5.
              subst.

              destruct t1 as [dv1 P1].
              destruct t2 as [dv2 P2].
              cbn in H6.
              cbn.
              tauto.
            }
          }

          intros r1 r2 R1R2.
          apply rutt_Ret.
          destruct r1, r2.
          cbn in *.
          auto.
      }

      intros r1 r2 R1R2.
      (* Should be able to determine that the lookups
         are equivalent using DFNS *)
      cbn.
      break_match.
      { eapply lookup_defn_some_refine in Heqo; eauto.
        destruct Heqo as (f_den2 & LUP2 & FDEN2).

        rewrite LUP2.
        red in FDEN2.
        specialize (FDEN2 args args0).
        forward FDEN2.
        { apply map_monad_oom_forall2; tauto.
        }

        destruct PRE as [T [CONV MAPM]]; subst.

        eapply rutt_weaken; eauto.
        - intros A B e1 e2 H.
          red in H.
          destruct e1.
          { destruct c.
            destruct e2; [| tauto].
            destruct c.
            constructor.
            cbn.
            destruct H as [T1T2 [CONV' MAPM']]; subst.
            auto.
          }
          destruct e2; [contradiction|].

          constructor.
          auto.
        - intros A B e1 r0 e2 r3 H.
          inv H.
          apply inj_pair2 in H0, H3, H4, H5; subst.
          red in H6.
          red.
          auto.
          destruct e0.
          destruct d1.
          auto.

          apply inj_pair2 in H0, H3, H4, H5; subst.
          red in H6.
          red.
          auto.
      }

      eapply lookup_defn_none in Heqo; eauto.
      rewrite Heqo.

      eapply rutt_bind with (RR:=Forall2 dvalue_refine).
      { (* Pick *)
        destruct PRE as [T [CONV MAPM]].
        apply map_monad_oom_forall2 in MAPM.
        induction MAPM.
        - cbn.
          apply rutt_Ret; auto.
        - do 2 rewrite map_monad_unfold.
          cbn.
          eapply rutt_bind with (RR:=dvalue_refine).
          {
            apply pickUnique_rutt; auto.
          }

          intros r0 r3 R0R3.
          eapply rutt_bind with (RR:=Forall2 dvalue_refine);
            eauto.

          intros r4 r5 R4R5.
          eapply rutt_Ret.
          constructor; eauto.
      }

      intros r3 r4 R3R4.
      cbn.

      destruct PRE as [T [UV ARGS_CONV]]; subst.

      unfold ITree.map.
      eapply rutt_bind with (RR:=dvalue_refine).
      {
        apply rutt_trigger.
        { constructor.
          cbn.
          split; split; auto.

          apply map_monad_oom_forall2.
          auto.
        }

        intros t1 t2 H.
        inv H.
        cbn in *.
        apply inj_pair2 in H0, H3, H4, H5.
        subst.

        cbn in H6.
        tauto.
      }

      intros r0 r5 R0R5.
      apply rutt_Ret.

      split; split; auto.
      split; auto.

      red in R0R5.
      apply dvalue_refine_dvalue_to_uvalue; auto.
    }

    cbn. auto.
  Qed.

  Lemma denote_mcfg_E1E2_rutt'_rutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      rutt event_refine event_res_refine (fun res1 res2 => call_res_refine IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2) ->
      rutt event_refine event_res_refine uvalue_refine
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H.
    eapply rutt_weaken; eauto.
    intros r1 r2 H0.
    cbn in H0.
    red. tauto.
  Qed.

  Lemma denote_mcfg_E1E2_rutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      (Forall2 (dvalue_refine × function_denotation_refine) dfns1 dfns2) ->
      (uvalue_refine f1 f2) ->
      (Forall2 uvalue_refine args1 args2) ->
      rutt event_refine event_res_refine uvalue_refine
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H H0 H1.
    eapply denote_mcfg_E1E2_rutt'_rutt.
    eapply denote_mcfg_E1E2_rutt'; auto.
    cbn.
    split; auto.
    split; auto.
    apply map_monad_oom_forall2; auto.
  Qed.

  Lemma model_E1E2_rutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_rutt p p.
  Proof.
    red.

    unfold denote_vellvm.
    unfold LLVM1.denote_vellvm.
    eapply rutt_bind; [apply build_global_environment_E1E2_rutt_strict_sound|].

    intros [] [] _.
    eapply rutt_bind; [apply address_one_functions_E1E2_rutt|].

    intros r1 r2 R1R2.
    eapply rutt_bind; [apply GlobalRead_L0_E1E2_rutt|].

    intros r3 r4 R3R4.
    eapply rutt_bind.

    { apply denote_mcfg_E1E2_rutt; auto.
      - apply dvalue_refine_dvalue_to_uvalue; auto.
      - (* TODO: fold into main_args lemma probably *)
        unfold main_args.
        unfold LLVM1.main_args.
        constructor.
        + red.
          rewrite uvalue_convert_equation.
          reflexivity.
        + constructor; [|constructor].
          red.
          rewrite uvalue_convert_equation.
          cbn.
          rewrite AC1.addr_convert_null.
          reflexivity.
    }

    intros r0 r5 H.
    eapply rutt_bind with (RR:=fun x y => dvalue_refine (proj1_sig x) (proj1_sig y)).
    { (* Pick *)
      apply rutt_trigger.
      { cbn.
        split; auto.
        (* TODO: this lemma may not even be true *)
        apply uvalue_refine_concretize_poison; auto.
      }

      intros t1 t2 H0.
      cbn in *.
      destruct t1, t2; tauto.
    }

    intros r6 r7 H0.
    cbn.
    apply rutt_Ret; auto.
  Qed.

  (* TODO: not sure about name... *)
  Definition model_E1E2_L0
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L0
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L1
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L1
      (LLVM1.model_oom_L1 p1)
      (LLVM2.model_oom_L1 p2).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L2
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L2
      (LLVM1.model_oom_L2 p1)
      (LLVM2.model_oom_L2 p2).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L3
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L3
      (LLVM1.model_oom_L3 p1)
      (LLVM2.model_oom_L3 p2).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L4
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L4 (LLVM1.model_oom_L4 p1) (LLVM2.model_oom_L4 p2).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L5
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L5 (LLVM1.model_oom_L5 p1) (LLVM2.model_oom_L5 p2).

  (* TODO: not sure about name... *)
  Definition model_E1E2_L6
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L6 (LLVM1.model_oom_L6 p1) (LLVM2.model_oom_L6 p2).

End LangRefine.

Module MakeLangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) : LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR.
  Include LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR.
End MakeLangRefine.

Module InfFinLangRefine := MakeLangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinements64BitIntptr.

(* Just planning on using this for L4_convert from finite to infinite events. *)
Module FinInfLangRefine := MakeLangRefine InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert TopLevel64BitIntptr TopLevelBigIntptr TopLevelRefinementsBigIntptr.

Module InfiniteToFinite.
  Import FinInfLangRefine. (* Just planning on using this for L4_convert from finite to infinite events. *)
  Import InfFinLangRefine.

  From Vellvm Require Import InterpreterMCFG.

  Import MCFGTheoryBigIntptr.
  Import MCFGTheory64BitIntptr.

  Module TLR_INF := TopLevelRefinementsBigIntptr.
  Module TLR_FIN := TopLevelRefinements64BitIntptr.

  Hint Resolve interp_PropT__mono : paco.

  (* TODO: Move these refine_OOM_h lemmas? *)
  Import Morphisms.

  Import TC1.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler).

  Module InfLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStackBigIntptr.LLVM.
  Module FinLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.
  Module InfFinTC := Vellvm.Semantics.InfiniteToFinite.InfFinLangRefine.TC1.
  Module FinInfTC := Vellvm.Semantics.InfiniteToFinite.FinInfLangRefine.TC1.

  Module EC1 := InfFinTC.EC.
  Module EC2 := FinInfTC.EC.

  Module InfMem := MemoryBigIntptr.
  Module FinMem := Memory64BitIntptr.

  Module InfMemMMSP := MemoryBigIntptr.MMEP.MMSP.
  Module FinMemMMSP := Memory64BitIntptr.MMEP.MMSP.

  Module InfMemInterp := MemoryBigIntptr.MEM_SPEC_INTERP.
  Module FinMemInterp := Memory64BitIntptr.MEM_SPEC_INTERP.

  (* Could not put with the other conversions, need to know what memory structures like MemState are *)
  Definition convert_SByte (sb1 : MemoryBigIntptr.MP.BYTE_IMPL.SByte) : OOM (Memory64BitIntptr.MP.BYTE_IMPL.SByte).
    destruct sb1.
    refine (uv' <- EC.DVC.uvalue_convert uv;;
            idx' <- EC.DVC.uvalue_convert idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition convert_mem_byte (mb1 : InfMemMMSP.mem_byte) : OOM (FinMemMMSP.mem_byte).
    destruct mb1.
    refine (s' <- convert_SByte s;;
            ret _).

    constructor.
    apply s'.
    apply a.
  Defined.

  (* Slightly tricky.

     Both the infinite and finite memory have the same underlying
     structure --- a map from Z to mem_bytes.

     The Z indexes in the finite memory may need to be limited to the
     range of the address type, but it may not matter because trying
     to look these up in a program should cause OOM anyway.
   *)
  Definition convert_memory (mem : InfMemMMSP.memory) : OOM (FinMemMMSP.memory).
    refine (elems <- map_monad _ (IntMaps.IM.elements mem);;
            ret (IntMaps.IP.of_list elems)).

    refine (fun '(ix, mb) =>
              mb' <- convert_mem_byte mb;;
              ret (ix, mb')).
  Defined.

  Definition convert_Frame (f : InfMemMMSP.Frame) : OOM (FinMemMMSP.Frame).
    induction f.
    - exact (ret []).
    - refine (a' <- InfToFinAddrConvert.addr_convert a;;
              f' <- IHf;;
              ret (a' :: f')).
  Defined.

  Definition convert_FrameStack (fs : InfMemMMSP.FrameStack) : OOM (FinMemMMSP.FrameStack).
    induction fs.
    - refine (f' <- convert_Frame f;;
              ret (FinMemMMSP.Singleton f')).
    - refine (f' <- convert_Frame f;;
              fs' <- IHfs;;
              ret (FinMemMMSP.Snoc fs' f')).
  Defined.

  Definition convert_Block (b : InfMemMMSP.Block) : OOM (FinMemMMSP.Block)
    := map_monad InfToFinAddrConvert.addr_convert b.

  Definition convert_Heap (h : InfMemMMSP.Heap) : OOM (FinMemMMSP.Heap).
    refine (blocks <- map_monad _ (IntMaps.IM.elements h);;
            ret (IntMaps.IP.of_list blocks)).

    refine (fun '(ix, b) =>
              b' <- convert_Block b;;
              ret (ix, b')).
  Defined.

  Definition convert_memory_stack (ms1 : InfMemMMSP.memory_stack) : OOM (FinMemMMSP.memory_stack).
    destruct ms1 as [mem fs h].
    refine (mem' <- convert_memory mem;;
            fs' <- convert_FrameStack fs;;
            h' <- convert_Heap h;;
            ret _).

    constructor; auto.
  Defined.

  Definition convert_MemState (m1 : InfMem.MMEP.MMSP.MemState) : OOM (FinMem.MMEP.MMSP.MemState).
    destruct m1 as [ms pr].
    refine (ms' <- convert_memory_stack ms;;
            ret _).

    constructor; auto.
  Defined.

  Definition MemState_refine (m1 : InfMem.MMEP.MMSP.MemState) (m2 : FinMem.MMEP.MMSP.MemState) : Prop
    := convert_MemState m1 = NoOom m2.

  Lemma MemState_refine_initial :
    MemState_refine InfMemMMSP.initial_memory_state FinMemMMSP.initial_memory_state.
  Proof.
    reflexivity.
  Qed.

  Instance refine_OOM_h_eq_itree {E F T RR} : Proper (eq_itree eq ==> eq_itree eq ==> iff) (@refine_OOM_h E F T RR).
  repeat intro. rewrite H, H0.
  reflexivity.
  Qed.

  Lemma refine_OOM_h_bind :
    forall {T R E F} (x y : itree (E +' OOME +' F) T) (RR1 : relation T) (RR2 : relation R) k,
      (forall r1 r2, RR1 r1 r2 -> refine_OOM_h RR2 (k r1) (k r2)) ->
      refine_OOM_h RR1 x y ->
      refine_OOM_h RR2 (a <- x;; k a) (a <- y;; k a).
  Proof.
    intros T R E F.

    unfold refine_OOM_h, refine_OOM_h_flip.
    intros t1 t2 RR1 RR2.

    unfold bind, Monad_itree.
    revert t1 t2. pcofix CIH.
    intros t1 t2 k HK EQT.
    punfold EQT.
    red in EQT.

    assert (a <- t1 ;; k a =
              match observe t1 with
              | RetF r => k r
              | TauF t0 => Tau (ITree.bind t0 k)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
              end).
    { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. }
    setoid_rewrite H; clear H.

    assert (a <- t2 ;; k a =
              match observe t2 with
              | RetF r => k r
              | TauF t0 => Tau (ITree.bind t0 k)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
              end).
    { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. }
    setoid_rewrite H; clear H.

    pstep.
    induction EQT; eauto; pclearbot.
    - specialize (HK _ _ REL).
      punfold HK.
      eapply interp_PropTF_mono. eapply HK.
      intros. pclearbot. left.
      eapply paco2_mon; eauto.
      intros; contradiction.
    - constructor. right.
      eapply CIH; eauto.
    - econstructor; auto.
    - econstructor; auto.
    - eapply Interp_PropT_Vis_OOM with (e := e).
      punfold HT1; red in HT1. remember (observe (vis e k1)).
      hinduction HT1 before k; intros; inv Heqi; try inv CHECK.
      dependent destruction H1. unfold subevent.
      eapply eqit_Vis.
      Unshelve.
      intros. cbn.
      eapply eq_itree_clo_bind; pclearbot; eauto.
      apply REL.
      intros; subst; reflexivity.
    - eapply Interp_PropT_Vis; eauto.
      intros; eauto. right. eapply CIH; eauto.
      specialize (HK0 _ H1). pclearbot. eapply HK0; eauto.
      rewrite <- unfold_bind.
      setoid_rewrite <- Eqit.bind_bind.
      eapply eutt_clo_bind; eauto. intros; eauto.
      subst; reflexivity.
  Qed.

  (* If

    - ti2 is a refinement of ti1 tf2 refines ti2 tf1 refines tf2 at
    - finite level

    Not sure that this is true.

    If ti1 -i> ti2

    and ti2 -if> tf2

    And tf2 -f> tf1...

    Does it really follow that ti1 -if> tf1?

    In theory I can refine ti1 to ti2, and to tf1 through
    tf2... BUT... Does this mean I can refine ti1 directly to tf1?

    In theory ti2 has fewer behaviours than ti1, and so if I can
    refine it to tf2, then I can also refine ti1 to tf2.
   *)
  Lemma refine_E1E2_L6_compose_inf_to_fin :
    forall tx ty tz,
      TLR_INF.R.refine_L6 tx ty ->
      refine_E1E2_L6 ty tz ->
      refine_E1E2_L6 tx tz.
  Proof.
    intros tx ty tz XY_INF YZ_FIN.

    unfold refine_E1E2_L6 in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    unfold L6_convert_PropT in TY_FIN.
    destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

    specialize (XY_INF ry_inf TY_INF).
    destruct XY_INF as (rx_inf & TX_INF & XY_INF).

    set (rx_fin := L4_convert_tree' res_L6_convert_unsafe rx_inf).
    exists rx_fin.
    split.
    - unfold L6_convert_PropT, L4_convert_PropT.
      exists rx_inf; split; auto.
      subst rx_fin.
      reflexivity.
    - rewrite <- YZ.
      rewrite <- ry_fin_inf.
      subst rx_fin.

      (* There's probably a more general lemma hiding here *)
      unfold L4_convert_tree'.

      Unset Universe Checking.
      eapply refine_OOM_h_bind with (RR1:=TopLevelRefinementsBigIntptr.R.refine_res3).
      { intros r1 r2 H.
        unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.
        destruct r1 as [r1a [r1sid [[r1b1 r1b2] [r1c dv1]]]].
        destruct r2 as [r2a [r2sid [[r2b1 r2b2] [r2c dv2]]]].
        cbn.

        inversion H; subst.
        inversion snd_rel; subst.
        inversion snd_rel0; subst.
        inversion snd_rel1; subst.
        cbn in *; subst; reflexivity.
      }
      { apply refine_OOM_h_L6_convert_tree; auto.
      }
  Qed.

  Lemma refine_E1E2_L6_compose_fin_to_inf :
    forall tx ty tz,
      refine_E1E2_L6 tx ty ->
      TLR_FIN.R.refine_L6 ty tz ->
      refine_E1E2_L6 tx tz.
  Proof.
    intros tx ty tz XY_INF_TO_FIN YZ_FIN.

    unfold refine_E1E2_L6 in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    specialize (XY_INF_TO_FIN ry_fin TY_FIN).
    destruct XY_INF_TO_FIN as (rx_fin & TX_FIN & refine_inf_fin_x).

    exists rx_fin.
    split; auto.
    rewrite refine_inf_fin_x; auto.
  Qed.

  Theorem refine_E1E2_L6_transitive :
    forall ti1 ti2 tf1 tf2,
      TLR_INF.R.refine_L6 ti1 ti2 ->
      refine_E1E2_L6 ti2 tf1 ->
      TLR_FIN.R.refine_L6 tf1 tf2 ->
      refine_E1E2_L6 ti1 tf2.
  Proof.
    intros ti1 ti2 tf1 tf2 RINF RITOF RFIN.

    eapply refine_E1E2_L6_compose_fin_to_inf; eauto.
    eapply refine_E1E2_L6_compose_inf_to_fin; eauto.
  Qed.

  (** Safe conversion lemmas *)
  Lemma infinite_to_finite_dvalue_convert_safe :
    forall dv_i,
    exists dv_f,
      EC1.DVC.dvalue_convert dv_i = NoOom dv_f /\
        EC2.DVC.dvalue_convert dv_f = NoOom dv_i.
  Proof.
    intros dv_i.

    rewrite EC1.DVC.dvalue_convert_equation.
    destruct dv_i.
    - (* Addresses *)

    setoid_rewrite EC2.DVC.dvalue_convert_equation.

    (* TODO: Ugh, everything is opaque. Fix and prove. *)
  Admitted.

  Lemma L0_convert_safe :
    forall t,
      InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert
        (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert t) ≈ t.
  Proof.
    intros t.
    unfold InfFinTC.L0_convert_tree', InfFinTC.L0_convert_tree.
    unfold FinInfTC.L0_convert_tree', FinInfTC.L0_convert_tree.
    cbn.
    setoid_rewrite interp_bind.
    rewrite bind_bind.
    rewrite interp_interp.


    cbn.
    red.
  Admitted.

  (** Refinement lemmas *)
  Lemma refine_E1E2_L0_interp_intrinsics :
    forall t1 t2,
      refine_E1E2_L0 t1 t2 ->
      refine_E1E2_L0 (InfLLVM.Intrinsics.interp_intrinsics t1) (FinLLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red in RL0.
    red.
    exists (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)).
    split.
    - assert ((FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)) ≈  (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (LLVM.Intrinsics.interp_intrinsics (InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert t1')))) as EQT2.
      { eapply @FinInfTC.L0_convert_tree'_eutt_proper with (RA:=eq).
        intros u1 u2 H; subst.
        reflexivity.

        rewrite RL0.
        reflexivity.
      }

      rewrite EQT2.

      eapply refine_OOM_h_transitive with (y:=(InfLLVM.Intrinsics.interp_intrinsics t1')); try typeclasses eauto.
      (* May hold... OOM_T1 *)
      admit.

      red.
      red.
      (* This might actually be provable by walking through t1'?

         The conversions may cause early OOM, but otherwise preserves
         the event structure.
       *)
      admit.
    - red.
      (* This can't hold unless I know converting from E2 -> E1 -> E2
         is "safe" and doesn't cause any OOM.

         This should be the case for the particular Inf / Fin case we
         care about, though.
       *)
      rewrite L0_convert_safe.
      reflexivity.
  Admitted.

  Lemma refine_E1E2_interp_global :
    forall t1 t2 g1 g2,
      refine_E1E2_L0 t1 t2 ->
      global_refine g1 g2 ->
      refine_E1E2_L1 (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red.

    (* Perhaps I need a lemma about L1_convert_tree and interp_global here? *)
  Admitted.

  Lemma refine_E1E2_interp_local_stack :
    forall t1 t2 ls1 ls2,
      refine_E1E2_L1 t1 t2 ->
      local_stack_refine ls1 ls2 ->
      refine_E1E2_L2 (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
  Admitted.

  (* Most of these are aliases of the above, but some levels of the interpreter interpret more than one event *)
  Lemma refine_E1E2_01 :
    forall t1 t2 g1 g2,
      refine_E1E2_L0 t1 t2 ->
      global_refine g1 g2 ->
      refine_E1E2_L1 (interp_global (InfLLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (FinLLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply refine_E1E2_interp_global; auto.
    apply refine_E1E2_L0_interp_intrinsics; auto.
  Qed.

  Lemma refine_E1E2_12 :
    forall t1 t2 l1 l2,
      refine_E1E2_L1 t1 t2 ->
      local_stack_refine l1 l2 ->
      refine_E1E2_L2 (interp_local_stack t1 l1) (interp_local_stack t2 l2).
  Proof.
    intros t1 t2 g1 g2 RL1 GENVS.
    red in RL1.
    apply refine_E1E2_interp_local_stack; auto.
  Qed.

  Import InterpMemoryProp.
  Lemma refine_E1E2_23 :
    forall t1 t2 sid m1 m2,
      refine_E1E2_L2 t1 t2 ->
      MemState_refine m1 m2 ->
      refine_E1E2_L3 (InfMemInterp.interp_memory_prop eq t1 sid m1) (FinMemInterp.interp_memory_prop eq t2 sid m2).
  Proof.
    intros t1 t2 sid m1 m2 RL2.

  (*
    h1 and h2 are handlers

    (* h2 refines h1 *)
    (forall e,
    refine_E1E2_L3 (h1 e) (h2 e)) ->
    forall u : itree,
    refine_E1E2_L3 (interp_prop h1 u) (interp_prop h2 u)

    Need something a bit more general like rutt.

    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L3 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    rutt refine_events refine_dvalue eq u1 u2 ->
    refine_E1E2_L3 (interp_prop h1 u1) (interp_prop h2 u2)


    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L4 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    refine_E1E2_L3 u1 u2 ->
    refine_E1E2_L4 (interp_prop h1 u1) (interp_prop h2 u2)

   *)

    (* I'll probably need something about MemMonad_valid_state eventually... *)
  Admitted.

  Lemma refine_E1E2_34 :
    forall t1 t2,
      refine_E1E2_L3 t1 t2 ->
      refine_E1E2_L4 (InfLLVM.Pick.model_undef eq t1) (FinLLVM.Pick.model_undef eq t2).
  Proof.
    intros t1 t2 RL3.
    red.
  Admitted.

  Lemma refine_E1E2_45 :
    forall t1 t2,
      refine_E1E2_L4 t1 t2 ->
      refine_E1E2_L5 (model_UB t1) (model_UB t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.

  Lemma refine_E1E2_56 :
    forall t1 t2,
      refine_E1E2_L5 t1 t2 ->
      refine_E1E2_L6 (refine_OOM eq t1) (refine_OOM eq t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.


  From Vellvm Require Import Tactics.

  From ITree Require Import
        ITree
        Basics.Monad
        Events.StateFacts
        Eq.Eqit.

  Import TranslateFacts.
  Import TopLevelBigIntptr.
  Import TopLevel64BitIntptr.
  Import InterpreterStackBigIntptr.
  Import TopLevelRefinements64BitIntptr.

  Ltac force_rewrite H :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB; clear HB.

  Tactic Notation "force_rewrite" constr(H) "in" hyp(H') :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB in H'; clear HB.


  (* TODO: this is going to be a big one *)
  Theorem model_E1E2_L0_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L0 p p.
  Proof.
    intros p.
    unfold model_E1E2_L0.
    red.
    unfold refine_L0.
    unfold L0_convert_tree'.
    unfold L0_convert_tree.

    exists (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert
         (denote_vellvm (DynamicTypes.DTYPE_I 32) "main" main_args
            (TypToDtyp.convert_types (CFG.mcfg_of_tle p)))).

    split.
    - (* src' may have additional OOM *)
      (* I think this pretty much has to be by induction over the syntax? *)
      admit.
    - (* src' when converted agrees with target *)
      (* Target may just be OOM for all we know *)
      red.
      setoid_rewrite L0_convert_safe.
      reflexivity.
  Admitted.

  Theorem model_E1E2_L1_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L1 p p.
  Proof.
    intros p.
    red.

  (* Maybe I need some lemmas akin to these:

    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).

    But for crossing the infinite / finite boundary...

   *)
    unfold model_oom_L1.
    unfold model_gen_oom_L1.
    unfold interp_mcfg1.

    apply refine_E1E2_01.
    { (* Still need to deal with interp_intrinsics... *)
      apply model_E1E2_L0_sound.
    }

    apply global_refine_empty.
  Qed.

  Theorem model_E1E2_L2_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L2 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_12; [| apply local_stack_refine_empty].
    apply model_E1E2_L1_sound.
  Qed.

  Theorem model_E1E2_L3_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L3 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_23; [| apply MemState_refine_initial].
    apply model_E1E2_L2_sound.
  Qed.

  Theorem model_E1E2_L4_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L4 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_34.
    apply model_E1E2_L3_sound.
  Qed.

  Theorem model_E1E2_L5_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L5 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_45.
    apply model_E1E2_L4_sound.
  Qed.

  Theorem model_E1E2_L6_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L6 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_56.
    apply model_E1E2_L5_sound.
  Qed.

End InfiniteToFinite.
