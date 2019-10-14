From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Memory
     Refinement
     Environment
     TopLevel
     LLVMAst
     Handlers.Stack.

From ExtLib Require Import
     Structures.Functor
     
.

From Coq Require Import
     Logic
     Morphisms.

Import ITree.Basics.Basics.Monads.
Require Import Relations.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.

Require Import Omega.

(* CB: Does this already exist? *)
Lemma subrelation_R_TT: 
  forall A (R : relation A), subrelation R TT.
Proof. firstorder. Qed.

(* CB: Does this already exist? *)
Lemma subrelation_prod_left :
  forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
Proof.
  intros A B R R' R2 H.
  unfold subrelation in *.
  intros x y HRR2.
  inversion HRR2; firstorder.
Qed.

Lemma refine_01: forall t1 t2,
    refine_L0 t1 t2 -> refine_L1 (build_L1 t1) (build_L1 t2).
Proof.
  intros t1 t2 H.
  apply eqit_mon with (RR:=(eq × refine_uvalue)) (b1:=true) (b2:=true); trivial.
  - intros x0 x1 PR.
    eapply subrelation_prod_left. apply subrelation_R_TT. apply PR.
  - apply eutt_interp_state_gen; auto.
 Qed.

Lemma refine_12 : forall t1 t2,
    refine_L1 t1 t2 -> refine_L2 (build_L2 t1) (build_L2 t2).
Proof.
  intros t1 t2 H.
  apply eqit_mon with (RR:=(eq × refine_res1)) (b1:=true) (b2:=true); trivial.
  - intros x0 x1 PR.
    eapply subrelation_prod_left. apply subrelation_R_TT. apply PR.
  - apply eutt_interp_state_gen; auto.
Qed.

Lemma refine_23 : forall t1 t2,
    refine_L2 t1 t2 -> refine_L3 (build_L3 t1) (build_L3 t2).
Proof.
  intros t1 t2 H.
  apply eqit_mon with (RR:=(eq × refine_res2)) (b1:=true) (b2:=true); trivial.
  - intros x0 x1 PR.
    eapply subrelation_prod_left. apply subrelation_R_TT. apply PR.
  - apply eutt_interp_state_gen; auto.
Qed.

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

Instance interp_prop_Proper :
  forall R E F G (t : itree (E +' G) R) (RR : relation R) (h : (E +' F +' G) ~> PropT.PropT (itree (E +' G))),
    Proper (@eutt (E +' F +' G) _ _ RR ==> iff) (fun t' => @PropT.interp_prop (E +' F +' G) _ _ _ _ h _ t' t).
Proof.
  intros R E F G t RR h.
  intros t1 t2 Heutt.
  unfold PropT.PropT in h. unfold Ensembles.Ensemble in h.
Admitted.

Lemma refine_34 : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4 (model_L4 t1) (model_L4 t2).
Proof.
  intros t1 t2 H.
  unfold refine_L4.
  intros t Hip.

  unfold model_L4 in *.
  unfold P.model_undef in *.

  exists t; split.

  match goal with
  | [ |- context [PropT.interp_prop ?h _ _] ] =>
    apply (interp_prop_Proper res_L3 _ _ _ t refine_res3 h t1 t2 H)
  end.

  apply Hip.

  apply Reflexive_eqit.
  repeat apply prod_rel_refl; auto using TT_refl, refine_uvalue_refl.
Qed.


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
