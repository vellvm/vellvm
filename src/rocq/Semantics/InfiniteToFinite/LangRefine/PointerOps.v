From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  TopLevelRefinements
  Handlers.MemoryModules.FiniteAddresses
  Handlers.MemoryModules.InfiniteAddresses.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  ListUtil
  OOMRutt
  OOMRuttProps.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Vectors.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.


Module Type ItoP_Refine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI).
  Parameter addr_convert_int_to_ptr :
    forall base_addr_fin base_addr_inf res_addr_fin res_addr_inf z
      (CONV_BASE : AC2.addr_convert base_addr_fin = NoOom base_addr_inf)
      (CONV_RES : AC2.addr_convert res_addr_fin = NoOom res_addr_inf)
      (ITP : IS2.LP.ITOP.int_to_ptr z (IS2.LP.PROV.address_provenance base_addr_fin) = NoOom res_addr_fin),
      (IS1.LP.ITOP.int_to_ptr z (IS1.LP.PROV.address_provenance base_addr_inf)) = ret res_addr_inf.

  Parameter int_to_ptr_fin_inf :
    forall z prov prov' a_fin a_inf,
      AC2.addr_convert a_fin = NoOom a_inf ->
      IS1.LP.PROV.address_provenance a_inf = prov' ->
      IS2.LP.ITOP.int_to_ptr z prov = NoOom a_fin ->
      IS1.LP.ITOP.int_to_ptr z prov' = NoOom a_inf.

  Parameter int_to_ptr_fin_inf_wildcard :
    forall z a_fin a_inf,
      AC2.addr_convert a_fin = NoOom a_inf ->
      IS2.LP.ITOP.int_to_ptr z IS2.LP.PROV.wildcard_prov = NoOom a_fin ->
      IS1.LP.ITOP.int_to_ptr z IS1.LP.PROV.wildcard_prov = NoOom a_inf.
End ItoP_Refine.

Module ItoP_Refine_InfFin : ItoP_Refine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert.
  Lemma addr_convert_int_to_ptr :
    forall base_addr_fin base_addr_inf res_addr_fin res_addr_inf z
      (CONV_BASE : FinToInfAddrConvert.addr_convert base_addr_fin = NoOom base_addr_inf)
      (CONV_RES : FinToInfAddrConvert.addr_convert res_addr_fin = NoOom res_addr_inf)
      (ITP : InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z (InterpreterStack64BitIntptr.LP.PROV.address_provenance base_addr_fin) = NoOom res_addr_fin),
      (InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z (InterpreterStackBigIntptr.LP.PROV.address_provenance base_addr_inf)) = ret res_addr_inf.
  Proof.
    intros base_addr_fin base_addr_inf res_addr_fin res_addr_inf z CONV_BASE CONV_RES ITP.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in *.
    break_match_hyp_inv.
    unfold FinToInfAddrConvert.addr_convert in *.
    cbn in *.
    inv CONV_RES.

    unfold InterpreterStackBigIntptr.LP.PROV.address_provenance.
    unfold InterpreterStack64BitIntptr.LP.PROV.address_provenance.
    destruct base_addr_fin; inv CONV_BASE; cbn.

    rewrite Integers.Z_mod_modulus_eq.
    rewrite Rocqlib.Zmod_small; try lia; auto.
  Qed.

  Lemma int_to_ptr_fin_inf :
    forall z prov prov' a_fin a_inf,
      FinToInfAddrConvert.addr_convert a_fin = NoOom a_inf ->
      InterpreterStackBigIntptr.LP.PROV.address_provenance a_inf = prov' ->
      InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z prov = NoOom a_fin ->
      InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z prov' = NoOom a_inf.
  Proof.
    intros z prov prov' a_fin a_inf CONV PROV ITP.
    destruct a_fin.
    cbn in CONV; inv CONV.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in ITP.
    break_match_hyp_inv.
    rewrite Integers.unsigned_repr.
    2: {
      unfold Integers.max_unsigned.
      lia.
    }
    auto.
  Qed.

  Lemma int_to_ptr_fin_inf_wildcard :
    forall z a_fin a_inf,
      FinToInfAddrConvert.addr_convert a_fin = NoOom a_inf ->
      InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z FinPROV.wildcard_prov = NoOom a_fin ->
      InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z InfPROV.wildcard_prov = NoOom a_inf.
  Proof.
    intros z a_fin a_inf CONV ITP.
    destruct a_fin.
    cbn in CONV; inv CONV.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in ITP.
    break_match_hyp_inv.
    rewrite Integers.unsigned_repr.
    2: {
      unfold Integers.max_unsigned.
      lia.
    }
    auto.
  Qed.
End ItoP_Refine_InfFin.
