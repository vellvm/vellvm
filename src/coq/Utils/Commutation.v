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


Definition has_post_l {E X1 X2} (t: itree E X1) (t': itree E X2) (Q : X1 -> Prop) : Prop :=
  eutt (fun 'x _ => Q x) t t'.

Definition has_post_r {E X1 X2} (t: itree E X1) (t': itree E X2) (Q : X2 -> Prop) : Prop :=
  eutt (fun _ 'x => Q x) t t'.

Lemma eutt_True :
  forall {E X} (t t' : itree E X),
    eutt (fun _ _ => True) t t'.
Proof.
  intros.
  setoid_rewrite (itree_eta t) at 1.
  revert t t'.
  pcofix CIH.
  intros.
  destruct (observe t) eqn: EQ.
  - pstep.
Admitted.

Lemma has_post_post_l : forall {E X} (t t': itree E X) Q,
  has_post t Q -> has_post_l t t' Q.
Proof.
  intros. unfold has_post_l.
  eapply eqit_mon; auto. Unshelve.
  3 : exact (fun x _ => Q x /\ True).
  2 : eapply eutt_conj. 3 : eapply eutt_True.
Admitted.

Lemma has_post_post_r : forall {E X} (t t': itree E X) Q,
  has_post t' Q -> has_post_r t t' Q.
Proof.
Admitted.

Lemma eutt_post_bind : forall E R1 R2 RR U Q1 Q2 (t1 t2: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    t1 ⤳ Q1 ->
    t2 ⤳ Q2 ->
    (forall u1 u2, Q1 u1 -> Q2 u2 -> eutt RR (k1 u1) (k2 u2)) -> eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros * POST1 POST2 ?.
  apply eutt_clo_bind with (UU := fun x y => Q1 x /\ Q2 y); [ | intuition].
  apply eutt_conj.
  pose proof @has_post_post_l. unfold has_post_l in H0.
  apply H0. auto.
  pose proof @has_post_post_r. unfold has_post_r in H0.
  apply H0. auto.
Qed.

Lemma commut_gen :
  forall {A : Type}
         (Q1 Q2 : A -> Prop) (Q : A -> A -> Prop) (a0 : A)
         (t1 t2 t3 t4 : A -> itree void1 A) `{Symmetric _ Q} `{Transitive _ Q},
    (forall x, t1 x ≈ t4 x) ->
    (forall x, t2 x ≈ t3 x) ->
    (t1 a0 ⤳ Q1) ->
    (t3 a0 ⤳ Q2) ->
    (forall a1 a2, Q1 a1 -> Q2 a2 -> eutt Q (t2 a1) (t4 a2)) ->
    eutt Q ('a <- t1 a0;; t2 a) ('a <- t3 a0;; t4 a).
Proof.
  cbn.
  einit. ecofix CIH.
  intros * SYM TRA EQ1 EQ2 PC1 PC2 H.
  setoid_rewrite (itree_eta (t1 a0)) at 1.
  destruct (observe (t1 a0)) eqn: EQ; [ | | inv e].
  - ebind; econstructor; cycle 1.
    Unshelve. 3 : exact (fun x y => Q1 x /\ Q2 y).
    + intros. destruct H0. efinal.
    + clear H. rewrite <- bind_ret_r.
      setoid_rewrite <- bind_ret_r at 4.
      eapply eutt_post_bind.
      2 : eauto.
      specialize (EQ1 a0).
      setoid_rewrite (itree_eta (t1 a0)) in PC1. rewrite EQ in PC1.
      apply PC1.
      intros. apply eqit_Ret. auto.
  - rewrite (itree_eta (t3 a0)).
    destruct (observe (t3 a0)) eqn: EQ'; [ | | inv e].
    + ebind; econstructor; cycle 1.
      Unshelve. 3 : exact (fun x y => Q1 x /\ Q2 y).
      * intros. destruct H0. efinal.
      * clear H. rewrite <- bind_ret_r.
        setoid_rewrite <- bind_ret_r at 5.
        eapply eutt_post_bind.
        2 : eauto.
        specialize (EQ1 a0).
        setoid_rewrite (itree_eta (t1 a0)) in PC1. rewrite EQ in PC1.
        apply PC1.
        setoid_rewrite (itree_eta (t3 a0)) in PC2. rewrite EQ' in PC2.
        apply PC2.
        intros. apply eqit_Ret. auto.
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
      * rewrite <- H0,<- H1. apply eutt_conj.
        apply has_post_post_l. auto.
        apply has_post_post_r. auto.
Qed.

