From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     CFG
     Memory
     Refinement
     Environment
     TopLevel
     LLVMAst
     Handlers.Stack.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Logic
     Morphisms
     Relations.

Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.

(** The module _Refinement.Make_ defines a series of refinements between
    [itree]s at the various signatures of events a Vellvm goes through during
    the chain of interpretations leading to the definition of the model.
    These refinements state set inclusion of the concretization of the
    returned under-defined values, but impose no constraints on the states.

    In this module, we show that these refinements define a chain of growing
    relations when composed with the bits of interpretations relating each
    level.

    Finally, this allows us to lift these relations on [itree]s to a growing
    chain of relations on [mcfg typ].
 *)

(** BEGIN TO MOVE *)
Lemma subrelation_R_TT:
  forall A (R : relation A), subrelation R TT.
Proof. firstorder. Qed.

Lemma subrelation_prod_left :
  forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
Proof.
  intros A B R R' R2 H.
  unfold subrelation in *.
  intros x y HRR2.
  inversion HRR2; firstorder.
Qed.

Lemma eutt_tt_to_eq_prod :
  forall X R (RR : relation R) E (t1 t2 : itree E (X * R)),
    eutt (eq × RR) t1 t2 -> eutt (TT × RR) t1 t2.
Proof.
  intros X R RR E t1 t2 Heutt.
  unfold eutt.
  apply (eqit_mon (eq × RR) (TT × RR) true true true true); trivial.
  intros x0 x1 PR.
  eapply subrelation_prod_left. apply subrelation_R_TT. all: apply PR.
Qed.

(* Instance interp_prop_Proper : *)
(*   forall R E F G (t : itree (E +' G) R) (RR : relation R) (h : (E +' F +' G) ~> PropT.PropT (itree (E +' G))), *)
(*     Proper (@eutt (E +' F +' G) _ _ RR ==> iff) (fun t' => @PropT.interp_prop (E +' F +' G) _ _ _ _ h _ t' t). *)
(* Proof. *)
(*   intros R E F G t RR h. *)
(*   intros t1 t2 Heutt. *)
(*   unfold PropT.PropT in h. unfold Ensembles.Ensemble in h. *)
(* Admitted. *)

(* This formulation should be easier to use *)
Instance interp_prop_Proper :
  forall R E F G (RR : relation R) (h : (E +' F +' G) ~> PropT.PropT (itree (E +' G))),
    Proper (@eutt (E +' F +' G) _ _ RR ==> eq ==> Basics.impl) (@PropT.interp_prop (E +' F +' G) _ _ _ _ h R).
Proof.
  intros R E F G t RR h.
  intros t1 t2 Heutt.
  unfold PropT.PropT in h. unfold Ensembles.Ensemble in h.
Admitted.

Hint Unfold TT.
Instance TT_equiv :
  forall A, Equivalence (@TT A).
Proof.
  intros A; split; repeat intro; auto.
Qed.

(** END TO MOVE *)


(** We first prove that the [itree] refinement at level [i] entails the
    refinement at level [i+1] after running the [i+1] level of interpretation
 *)

Lemma refine_01: forall t1 t2,
    refine_L0 t1 t2 -> refine_L1 (build_L1 t1) (build_L1 t2).
Proof.
  intros t1 t2 H.
  apply eutt_tt_to_eq_prod, eutt_interp_state_gen; auto.
Qed.

Lemma refine_12 : forall t1 t2,
    refine_L1 t1 t2 -> refine_L2 (build_L2 t1) (build_L2 t2).
Proof.
  intros t1 t2 H.
  apply eutt_tt_to_eq_prod, eutt_interp_state_gen; auto.
Qed.

Lemma refine_23 : forall t1 t2,
    refine_L2 t1 t2 -> refine_L3 (build_L3 t1) (build_L3 t2).
Proof.
  intros t1 t2 H.
  apply eutt_tt_to_eq_prod, eutt_interp_state_gen; auto.
Qed.

(* Things are different for L4 and L5: we get into the [Prop] monad. *)
Lemma refine_34 : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4 (model_L4 t1) (model_L4 t2).
Proof.
  intros t1 t2 H t Ht.
  exists t; split.
  - unfold model_L4, P.model_undef in *.
    unfold IO.L3 in *.
    match goal with |- PropT.interp_prop ?x _ _ _ => remember x as h end.
    eapply interp_prop_Proper; eauto.
  - reflexivity.
Qed.

Lemma refine_45 : forall t1 t2,
    refine_L4 t1 t2 -> refine_L5 (model_L5 t1) (model_L5 t2).
Proof.
Admitted.

(**
   We now define partial interpretations in order to define refinements of [mcfg]s
 *)

Definition build_to_L1 user_intrinsics (prog: mcfg typ) :=
  let mcfg := normalize_types prog in
  let L0_trace        := build_L0 mcfg in
  let L0_trace'       := INT.interpret_intrinsics user_intrinsics L0_trace in
  let L1_trace        := build_L1 L0_trace' in
  L1_trace.

Definition build_to_L2 user_intrinsics (prog: mcfg typ) :=
  let mcfg := normalize_types prog in
  let L0_trace        := build_L0 mcfg in
  let L0_trace'       := INT.interpret_intrinsics user_intrinsics L0_trace in
  let L1_trace        := build_L1 L0_trace' in
  let L2_trace        := build_L2 L1_trace in
  L2_trace.

Definition build_to_L3 (user_intrinsics: IS.intrinsic_definitions) (prog: mcfg typ) :=
  let mcfg := normalize_types prog in

  let L0_trace        := build_L0 mcfg in
  let L0_trace'       := INT.interpret_intrinsics user_intrinsics L0_trace in
  let L1_trace        := build_L1 L0_trace' in
  let L2_trace        := build_L2 L1_trace in
  let L3_trace        := build_L3 L2_trace in
  L3_trace.

Definition build_to_L4 (user_intrinsics: IS.intrinsic_definitions) (prog: mcfg typ) :=
  let mcfg := normalize_types prog in

  let L0_trace        := build_L0 mcfg in
  let L0_trace'       := INT.interpret_intrinsics user_intrinsics L0_trace in
  let L1_trace        := build_L1 L0_trace' in
  let L2_trace        := build_L2 L1_trace in
  let L3_trace        := build_L3 L2_trace in
  let L4_trace        := model_L4 L3_trace in
  L4_trace.

Definition refine_mcfg_L1 (p1 p2: mcfg typ): Prop :=
  R.refine_L1 (build_to_L1 nil p1) (build_to_L1 nil p2).

Definition refine_mcfg_L2 (p1 p2: mcfg typ): Prop :=
  R.refine_L2 (build_to_L2 nil p1) (build_to_L2 nil p2).

Definition refine_mcfg_L3 (p1 p2: mcfg typ): Prop :=
  R.refine_L3 (build_to_L3 nil p1) (build_to_L3 nil p2).

Definition refine_mcfg_L4 (p1 p2: mcfg typ): Prop :=
  R.refine_L4 (build_to_L4 nil p1) (build_to_L4 nil p2).

Definition refine_mcfg (p1 p2: mcfg typ): Prop :=
  R.refine_L5 (model_mcfg p1) (model_mcfg p2).

Lemma refine_mcfg_L1_correct: forall p1 p2,
    refine_mcfg_L1 p1 p2 -> refine_mcfg p1 p2.
Admitted.

Lemma refine_mcfg_L2_correct: forall p1 p2,
    refine_mcfg_L2 p1 p2 -> refine_mcfg p1 p2.
Proof.
Admitted.

Lemma refine_mcfg_L3_correct: forall p1 p2,
    refine_mcfg_L3 p1 p2 -> refine_mcfg p1 p2.
Proof.
Admitted.

Lemma refine_mcfg_L4_correct: forall p1 p2,
    refine_mcfg_L4 p1 p2 -> refine_mcfg p1 p2.
Proof.
Admitted.


(* TODO SCRAPYARD, TO RECYCLE OR BURN
Instance refine_uvalue_refl :
  Reflexive refine_uvalue.
Proof.
  unfold Reflexive. intros x.
  induction x; constructor; auto.
Qed.

Instance TT_refl :
  forall A, Reflexive (@TT A).
Proof.
  firstorder.
Qed.

Lemma model_refines :
  forall t1 t, (model_L4 t1) t -> refine_L4 (fun t' => t = t') (model_L4 t1).
Proof.
  intros t1 t H.
  unfold refine_L4. intros t' Heq.
  exists t. split; auto.
  subst.

  apply Reflexive_eqit.
  repeat apply prod_rel_refl; auto using TT_refl, refine_uvalue_refl.
Qed.
*)

(* Unfinished proof *)
(*
Lemma refine_34_concrete : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4_concrete (build_L4 t1) (build_L4 t2).
Proof.
  intros t1 t2 H.
  unfold refine_L4_concrete.
  unfold refine_L3 in H.

  eapply eqit_mon.
  apply id. apply id.

  intros x0 x1 PR.
  unfold refine_res4.
  eapply subrelation_prod_left. apply subrelation_R_TT with (R:=eq). apply PR.

Qed.
 *)

(*
Lemma refine_45 : forall t1 t2,
    refine_L4 t1 t2 -> refine_L5 (model_L5 t1) (model_L5 t2).
Proof.
  intros t1 t2 H.
  unfold refine_L5.
  intros t Hip.

  exists t. split.
  - unfold model_L5 in *.
    unfold UndefinedBehaviour.model_UB in *.
    destruct Hip as [t' [t1p Hip]].

    exists t'. split.
    + unfold refine_L4 in H.
      pose proof (H t' t1p) as H1.
      destruct H1 as [t'' [Ht2t'' Ht't'']].

      Print Basics.impl.
      rewrite Ht't''.
    + apply Hip.
  - reflexivity.

  repeat apply prod_rel_refl; auto using TT_refl, refine_uvalue_refl.
Qed.
 *)

