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
