(* begin hide *)
From Coq Require Import
     RelationClasses
     Morphisms.

From Paco Require Import paco.
From ITree Require Import
     ITree
     ITreeFacts
     Eq.Eq.
Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

Import MonadNotation.
Open Scope monad_scope.

Lemma itree_eta_cont : forall {E A B} (t : itree E A) (k : A -> itree E B),
    'x <- t;; k x ≅ 'x <- t;; (fun y => {| _observe := observe (k y) |}) x.
Proof.
  intros.
  eapply eq_itree_clo_bind; [reflexivity | intros ? ? <-].
  rewrite itree_eta at 1; reflexivity.
Qed.

Lemma trivial_commut_gen : forall (t1 t2 t3 t4 : unit -> itree void1 unit),
    (forall x, t1 x ≈ t4 x) ->
    (forall x, t2 x ≈ t3 x) ->
    'x <- t1 tt;; t2 x ≈ 'x <- t3 tt;; t4 x.
Proof.
  cbn.
  einit; ecofix CIH.
  intros * EQ1 EQ2.
  setoid_rewrite (itree_eta (t1 tt)) at 1.
  destruct (observe (t1 tt)) eqn:EQ.
  - rewrite bind_ret_l.
    rewrite <- bind_ret_r at 1.
    ebind; econstructor.
    destruct r; apply EQ2.
    intros [] [] _.
    efinal.
    rewrite <- (EQ1 tt).
    rewrite (itree_eta (t1 tt)), EQ.
    destruct r; reflexivity.
  - rewrite (itree_eta (t3 tt)).
    destruct (observe (t3 tt)) eqn:EQ'.
    + destruct r.
      rewrite bind_ret_l.
      rewrite <- (bind_ret_r (t4 tt)). 
      ebind; econstructor.
      rewrite <- EQ1.
      rewrite (itree_eta (t1 tt)), EQ; reflexivity.
      intros [] [] _.
      edrop.
      rewrite EQ2, itree_eta, EQ'.
      reflexivity.
    + rewrite !bind_tau.
      estep.
      ebase; right.
      specialize (CIH (fun _ => t) t2 (fun _ => t0) t4).
      apply CIH.
      intros [].
      rewrite <- EQ1.
      rewrite (itree_eta (t1 tt)), EQ.
      rewrite tau_eutt; reflexivity.
      intros [].
      rewrite EQ2.
      rewrite (itree_eta (t3 tt)), EQ'.
      rewrite tau_eutt; reflexivity.
    + inv e.
  - inv e.
Qed.

Lemma trivial_commut : forall (t t' : unit -> itree void1 unit),
    'x <- t tt;; t' x ≈ 'x <- t' tt;; t x.
Proof.
  intros; apply trivial_commut_gen; intros; reflexivity.
Qed.

From Vellvm Require Import
     Utils.PostConditions.

Lemma commut_gen : forall {A : Type} (Q1 Q2 : A -> Prop) (Q : A -> A -> Prop) (a0 : A) (t1 t2 t3 t4 : A -> itree void1 A),
    (forall x, t1 x ≈ t4 x) ->
    (forall x, t2 x ≈ t3 x) ->
    (t1 a0 ⤳ Q1) ->
    (t3 a0 ⤳ Q2) ->
    (forall a1 a2, Q1 a1 -> Q2 a2 -> eutt Q (t2 a1) (t4 a2)) ->
    eutt Q ('a <- t1 a0;; t2 a) ('a <- t3 a0;; t4 a).
Proof.
Admitted.

(*   cbn. *)
(*   intros A Q1 Q2 Q a0. *)
(*   einit; ecofix CIH. *)
(*   clear CIH0. *)
(*   intros * EQ1 EQ2 POST1 POST2 POST. *)
(*   setoid_rewrite (itree_eta (t1 a0)).  *)
(*   destruct (observe (t1 a0)) eqn:EQ. *)
(*   - rewrite bind_ret_l. *)
(*     rewrite <- bind_ret_r at 1. *)
(*     ebind; econstructor. *)
(*     destruct r; apply EQ2. *)
(*     intros [] [] _. *)
(*     efinal. *)
(*     rewrite <- (EQ1 tt). *)
(*     rewrite (itree_eta (t1 tt)), EQ. *)
(*     destruct r; reflexivity. *)
(*   - rewrite (itree_eta (t3 tt)). *)
(*     destruct (observe (t3 tt)) eqn:EQ'. *)
(*     + destruct r. *)
(*       rewrite bind_ret_l. *)
(*       rewrite <- (bind_ret_r (t4 tt)).  *)
(*       ebind; econstructor. *)
(*       rewrite <- EQ1. *)
(*       rewrite (itree_eta (t1 tt)), EQ; reflexivity. *)
(*       intros [] [] _. *)
(*       edrop. *)
(*       rewrite EQ2, itree_eta, EQ'. *)
(*       reflexivity. *)
(*     + rewrite !bind_tau. *)
(*       estep. *)
(*       ebase; right. *)
(*       specialize (CIH (fun _ => t) t2 (fun _ => t0) t4). *)
(*       apply CIH. *)
(*       intros []. *)
(*       rewrite <- EQ1. *)
(*       rewrite (itree_eta (t1 tt)), EQ. *)
(*       rewrite tau_eutt; reflexivity. *)
(*       intros []. *)
(*       rewrite EQ2. *)
(*       rewrite (itree_eta (t3 tt)), EQ'. *)
(*       rewrite tau_eutt; reflexivity. *)
(*     + inv e. *)
(*   - inv e. *)
(* Qed. *)

