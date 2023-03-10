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

Module FinToInfAddrConvertSafe : AddrConvertSafe FinAddr InfAddr FinToInfAddrConvert InfToFinAddrConvert.
  Lemma addr_convert_succeeds :
    forall a1,
    {a2 & FinToInfAddrConvert.addr_convert a1 = NoOom a2}.
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
