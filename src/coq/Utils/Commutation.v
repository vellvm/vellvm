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

Require Import Coq.Logic.FunctionalExtensionality.

Lemma eutt_post_bind_het :
  forall (E : Type -> Type) (A : Type) (QQ : A -> A -> Prop) (Q1 Q2 : A -> Prop)
    (t1 t2 : A -> itree E A) (k1 : A -> itree E A) (k2 : A -> itree E A) (a0 : A),
    t1 a0 ⤳ Q1 ->
    t2 a0 ⤳ Q2 ->
    (forall u1 u2, eutt (fun x y => Q1 x /\ Q2 y) (t1 u1) (t2 u2)) ->
    (forall u1 u2 : A, Q1 u1 -> Q2 u2 -> eutt QQ (k1 u1) (k2 u2)) ->
    eutt QQ (` x : A <- t1 a0;; k1 x) (` x : A <- t2 a0;; k2 x).
Proof.
  intros * POST1 POST2 EQ1 EQ2.
  apply eutt_clo_bind with (UU := fun x y => Q1 x /\ Q2 y); [ | intuition].
  apply eutt_conj.
  rewrite has_post_post_strong in POST1.
  rewrite has_post_post_strong in POST2.
  unfold has_post_strong in *.
  eapply eqit_mon; eauto. 2 : apply EQ1. intuition. destruct PR. auto.
  eapply eqit_mon; eauto. 2 : apply EQ1. intuition. destruct PR. auto.
Qed.

Lemma commut_gen :
  forall {A : Type}
    (Q1 Q2 : A -> Prop) (QQ : A -> A -> Prop) (a0 : A)
    (t1 t2 t3 t4 : A -> itree void1 A),
    (forall x, t1 x ≈ t4 x) ->
    (forall x, t2 x ≈ t3 x) ->
    (t1 a0 ⤳ Q1) ->
    (t3 a0 ⤳ Q2) ->
    (forall a1 a2, eutt (fun x y => Q1 x /\ Q2 y) (t1 a1) (t3 a2)) ->
    (forall a1 a2, Q1 a1 -> Q2 a2 -> eutt QQ (t2 a1) (t4 a2)) ->
    eutt QQ ('a <- t1 a0;; t2 a) ('a <- t3 a0;; t4 a).
Proof.
  cbn.
  einit. ecofix CIH.
  intros * EQ1 EQ2 EQ3 PC1 PC2 H.
  setoid_rewrite (itree_eta (t1 a0)) at 1.
  destruct (observe (t1 a0)) eqn: EQ; [ | | inv e].
  - ebind; econstructor; cycle 1.
    Unshelve. 3 : exact (fun x y => Q1 x /\ Q2 y).
    + intros. destruct H0. efinal.
    + clear H.
      rewrite <- bind_ret_r.
      setoid_rewrite <- bind_ret_r at 4.
      rewrite <- EQ. rewrite <- itree_eta.
      eapply eutt_post_bind_het; eauto.
      intros. eauto. apply eqit_Ret; eauto.
  - rewrite (itree_eta (t3 a0)).
    destruct (observe (t3 a0)) eqn: EQ'; [ | | inv e].
    + ebind; econstructor; cycle 1.
      Unshelve. 3 : exact (fun x y => Q1 x /\ Q2 y).
      * intros. destruct H0. efinal.
      * clear H. rewrite <- bind_ret_r.
        setoid_rewrite <- bind_ret_r at 5.
        rewrite <- EQ. rewrite <- itree_eta.
        rewrite <- EQ'. rewrite <- itree_eta.
        eapply eutt_post_bind_het; eauto.
        intros. apply eqit_Ret; eauto.
    + rewrite !bind_tau.

      assert (t1 a0 ≈ t). rewrite itree_eta. rewrite EQ.
      apply eqit_tauL. reflexivity.

      assert (t3 a0 ≈ t0). rewrite itree_eta. rewrite EQ'.
      apply eqit_tauL. reflexivity.

      clear CIH0.

      estep.
      ebind; econstructor; cycle 1.

      Unshelve. 3 : exact (fun x y => Q1 x /\ Q2 y).
      * intros. destruct H2. efinal.
      * rewrite <- bind_ret_r.
        setoid_rewrite <- bind_ret_r at 4.
        rewrite <- H0,<- H1.
        eapply eutt_post_bind_het; eauto.
        intros. apply eqit_Ret; eauto.
Qed.

