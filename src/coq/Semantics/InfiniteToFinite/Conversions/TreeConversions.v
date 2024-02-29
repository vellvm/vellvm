From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From TwoPhase Require Import
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
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Semantics.InfiniteToFinite.Conversions.EventConversions
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

Module Type TreeConvert (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev).
  Module E1 := IS1.LP.Events.
  Module E2 := IS2.LP.Events.

  Import EC.
  Import DVC.

  (** Converting trees with events in language 1 to trees with events in language 2 *)

  (* TODO: move this? *)
  (*
  Definition L0_convert_tree_lazy {T} (t : itree E1.L0 T) : itree E2.L0 T := interp L0_convert_lazy t.
  Definition L1_convert_tree_lazy {T} (t : itree E1.L1 T) : itree E2.L1 T := interp L1_convert_lazy t.
  Definition L2_convert_tree_lazy {T} (t : itree E1.L2 T) : itree E2.L2 T := interp L2_convert_lazy t.
  Definition L3_convert_tree_lazy {T} (t : itree E1.L3 T) : itree E2.L3 T := interp L3_convert_lazy t.
  Definition L4_convert_tree_lazy {T} (t : itree E1.L4 T) : itree E2.L4 T := interp L4_convert_lazy t.
  Definition L5_convert_tree_lazy {T} (t : itree E1.L5 T) : itree E2.L5 T := interp L5_convert_lazy t.
  Definition L6_convert_tree_lazy {T} (t : itree E1.L6 T) : itree E2.L6 T := interp L6_convert_lazy t.
   *)

  Definition L0_convert_tree_strict {T} (t : itree E1.L0 T) : itree E2.L0 T := interp L0_convert_strict t.
  Definition L1_convert_tree_strict {T} (t : itree E1.L1 T) : itree E2.L1 T := interp L1_convert_strict t.
  Definition L2_convert_tree_strict {T} (t : itree E1.L2 T) : itree E2.L2 T := interp L2_convert_strict t.
  Definition L3_convert_tree_strict {T} (t : itree E1.L3 T) : itree E2.L3 T := interp L3_convert_strict t.
  Definition L4_convert_tree_strict {T} (t : itree E1.L4 T) : itree E2.L4 T := interp L4_convert_strict t.
  Definition L5_convert_tree_strict {T} (t : itree E1.L5 T) : itree E2.L5 T := interp L5_convert_strict t.
  Definition L6_convert_tree_strict {T} (t : itree E1.L6 T) : itree E2.L6 T := interp L6_convert_strict t.

  (*
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
   *)
  
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
  (*
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
   *)

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

  (*
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
   *)
  
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

  (*
  Definition convert_uvalue_tree_lazy {E} `{OOME -< E} (t : itree E E1.DV.uvalue) : itree E E2.DV.uvalue
    := fmap uvalue_convert_lazy t.

  Definition convert_dvalue_tree_lazy {E} `{OOME -< E} (t : itree E E1.DV.dvalue) : itree E E2.DV.dvalue
    := fmap dvalue_convert_lazy t.
   *)
  
  Definition convert_uvalue_tree_strict {E} `{OOME -< E} (t : itree E E1.DV.uvalue) : itree E E2.DV.uvalue
    := x <- t;;
       lift_OOM (uvalue_convert_strict x).

  Definition convert_dvalue_tree_strict {E} `{OOME -< E} (t : itree E E1.DV.dvalue) : itree E E2.DV.dvalue
    := x <- t;;
       lift_OOM (dvalue_convert_strict x).

  (*
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
   *)
  
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

Module TreeConvertMake (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC.
  Include TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC.
End TreeConvertMake.

Module TCFinInf := TreeConvertMake InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert DVCFinInf DVCInfFin ECFinInf.
Module TCInfFin := TreeConvertMake InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert DVCInfFin DVCFinInf ECInfFin.
