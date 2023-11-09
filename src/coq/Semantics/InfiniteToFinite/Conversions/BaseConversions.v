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

Module Type AddrConvert (ADDR1 : ADDRESS) (PTOI1 : PTOI ADDR1) (ADDR2 : ADDRESS) (PTOI2 : PTOI ADDR2).
  Parameter addr_convert : ADDR1.addr -> OOM ADDR2.addr.
  Parameter addr_convert_null :
    addr_convert ADDR1.null = NoOom ADDR2.null.

  Parameter addr_convert_injective :
    forall a b c,
      addr_convert a = NoOom c ->
      addr_convert b = NoOom c ->
      a = b.

  Parameter addr_convert_ptoi :
    forall a b,
      addr_convert a = NoOom b ->
      PTOI1.ptr_to_int a = PTOI2.ptr_to_int b.
End AddrConvert.

Module InfToFinAddrConvert : AddrConvert InfAddr InfPTOI FinAddr FinPTOI
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


(* SAZ: Move outside of this module? Replace Iptr with Z? *)
Lemma Int64_mod_eq:
  forall i i0 : Iptr,
    ((i <? 0)%Z || (i >=? Int64.modulus)%Z)%bool = false ->
    ((i0 <? 0)%Z || (i0 >=? Int64.modulus)%Z)%bool = false ->
    Int64.Z_mod_modulus i = Int64.Z_mod_modulus i0 -> i = i0.
Proof.
  intros i i0 H1 H2 EQ.
  apply Bool.orb_false_elim in H1.
  apply Bool.orb_false_elim in H2.
  destruct H1.
  destruct H2.
  assert (0 <= i < Integers.Int64.modulus)%Z by lia.
  assert (0 <= i0 < Integers.Int64.modulus)%Z by lia.
  do 2 rewrite Integers.Int64.Z_mod_modulus_eq in EQ.
  do 2 rewrite Zmod_small in EQ; auto.
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
  destruct c.
  break_match_hyp; inv BC.
  break_match_hyp; inv AC.
  Transparent Int64.repr.
  cbn in H0.
  Opaque Int64.repr.
  assert (i = i0) by (apply Int64_mod_eq; auto).
  subst.
  reflexivity.
Qed.

Lemma addr_convert_ptoi :
  forall a b,
    addr_convert a = NoOom b ->
    InfPTOI.ptr_to_int a = FinPTOI.ptr_to_int b.
Proof.
  intros a b CONV.
  unfold addr_convert in *.
  destruct a, b.
  cbn in *.
  erewrite FinITOP.ptr_to_int_int_to_ptr; eauto.
Qed.
    
End InfToFinAddrConvert.

Module FinToInfAddrConvert : AddrConvert FinAddr FinPTOI InfAddr InfPTOI
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

Lemma addr_convert_ptoi :
  forall a b,
    addr_convert a = NoOom b ->
    FinPTOI.ptr_to_int a = InfPTOI.ptr_to_int b.
Proof.
  intros a b CONV.
  unfold addr_convert in *.
  destruct a, b.
  cbn in *.
  inv CONV.
  unfold FinPTOI.ptr_to_int.
  cbn.
  reflexivity.
Qed.

End FinToInfAddrConvert.

Module Type AddrConvertSafe (ADDR1 : ADDRESS) (PTOI1 : PTOI ADDR1) (ADDR2 : ADDRESS) (PTOI2 : PTOI ADDR2) (AC1 : AddrConvert ADDR1 PTOI1 ADDR2 PTOI2 ) (AC2 : AddrConvert ADDR2 PTOI2 ADDR1 PTOI1).
  (* ADDR1 is "contained within" ADDR2 *)

  Parameter addr_convert_succeeds :
    forall a1,
    {a2 & AC1.addr_convert a1 = NoOom a2}.

  Parameter addr_convert_safe :
    forall a1 a2,
      AC1.addr_convert a1 = NoOom a2 ->
      AC2.addr_convert a2 = NoOom a1.
End AddrConvertSafe.

Module Type IPConvertSafe (IP1 : INTPTR) (IP2 : INTPTR).
  (* IP1 is contained within IP2 *)

  Parameter intptr_convert_succeeds :
    forall i1,
      {i2 & IP2.from_Z (IP1.to_Z i1) = NoOom i2}.

  Parameter intptr_convert_safe :
    forall i1 i2,
      IP2.from_Z (IP1.to_Z i1) = NoOom i2 ->
      IP1.from_Z (IP2.to_Z i2) = NoOom i1.
End IPConvertSafe.

Module FinToInfAddrConvertSafe : AddrConvertSafe FinAddr FinPTOI InfAddr InfPTOI FinToInfAddrConvert InfToFinAddrConvert.
  Lemma addr_convert_succeeds :
    forall a1,
    {a2 & FinToInfAddrConvert.addr_convert a1 = NoOom a2}.
  Proof.
    intros a1.
    destruct a1.
    cbn.
    eexists; reflexivity.
  Defined.

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
      {i2 & BigIP.from_Z (IP64Bit.to_Z i1) = NoOom i2}.
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
