(* begin hide *)
From Coq Require Import
     RelationClasses
     Morphisms.

From Vellvm Require Import Utils.NoEvent.

From Paco Require Import paco.

From ITree Require Import
     ITree
     ITreeFacts.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Scope monad_scope.

(* end hide *)

(** * Commutation of computations described as [itree]s
  This file develops some theory to justify when two computations described as
  interaction trees can be commuted, i.e. looks for sufficient condition under
  which we have: [t1 ;; t2 ≈ t2 ;; t1].

  We prove the obvious result that it always hold for computations that have no
  effects (E == void1) and computes no meaningful value (R == unit): [trivial_commut].
  While it is not surprising, it is not a completely trivial fact as it must
  account for divergence of either of the computation.

  We also establish more interesting results for computations involving a state.
  These lemmas are currently used in Helix in order to justify that the order of
  iteration of bounded loops over appropriate bodies can be reversed.

*)

Lemma itree_eta_cont : forall {E A B} (t : itree E A) (k : A -> itree E B),
    x <- t;; k x ≅ x <- t;; (fun y => {| _observe := observe (k y) |}) x.
Proof.
  intros.
  eapply eq_itree_clo_bind; [reflexivity | intros ? ? <-].
  rewrite itree_eta at 1; reflexivity.
Qed.

Lemma trivial_commut_gen : forall (t1 t2 t3 t4 : unit -> itree void1 unit),
    (forall x, t1 x ≈ t4 x) ->
    (forall x, t2 x ≈ t3 x) ->
    x <- t1 tt;; t2 x ≈ x <- t3 tt;; t4 x.
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
    x <- t tt;; t' x ≈ x <- t' tt;; t x.
Proof.
  intros; apply trivial_commut_gen; intros; reflexivity.
Qed.

From Vellvm Require Import
     Utils.PostConditions.

Lemma eutt_post_bind_het :
  forall (E : Type -> Type) (A : Type) (QQ : A -> A -> Prop) (Q1 Q2 : A -> Prop)
    (t1 t2 : A -> itree E A) (k1 : A -> itree E A) (k2 : A -> itree E A) (a0 : A),
    t1 a0 ⤳ Q1 ->
    t2 a0 ⤳ Q2 ->
    (forall u1 u2, eutt (fun x y => Q1 x /\ Q2 y) (t1 u1) (t2 u2)) ->
    (forall u1 u2 : A, Q1 u1 -> Q2 u2 -> eutt QQ (k1 u1) (k2 u2)) ->
    eutt QQ (x <- t1 a0;; k1 x) (x <- t2 a0;; k2 x).
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

(* We can commute computations where each atom coterminates with each other *)
Lemma commut_gen_coterminating_atoms :
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
      apply eqit_Tau_l. reflexivity.

      assert (t3 a0 ≈ t0). rewrite itree_eta. rewrite EQ'.
      apply eqit_Tau_l. reflexivity.

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

(* Lemma commut_gen : *)
(*   forall {A : Type} *)
(*     (Q1 Q2 : A -> Prop) (QQ : A -> A -> Prop) *)
(*     (t1 t3 : itree void1 A) *)
(*     (t2 t4 : A -> itree void1 A), *)
(*     (forall x, Q2 x -> t1 ≈ t4 x) -> *)
(*     (forall x, Q1 x -> t2 x ≈ t3) -> *)
(*     (t1 ⤳ Q1) -> *)
(*     (t3 ⤳ Q2) -> *)
(*     (forall a, Q1 a -> t2 a ⤳ (fun x => QQ x a)) -> *)
(*     (forall a, Q2 a -> t4 a ⤳ (fun x => QQ a x)) -> *)
(*     eutt QQ (a <- t1;; t2 a) (a <- t3;; t4 a). *)
(* Proof. *)
(*   cbn. *)
(*   einit. ecofix CIH. *)
(*   intros * EQ1 EQ2 PC1 PC2 F1 F2. *)
(*   setoid_rewrite (itree_eta t1) at 1. *)
(*   destruct (observe t1) eqn: EQ; [ | | inv e]. *)

(*   - (* Ret *) *)
(*     (* Need this rewriting to reason about co-termination on t2 and t3. *) *)
(*     rewrite bind_ret_l. rewrite <- bind_ret_r at 1. *)

(*     ebind; econstructor. *)
(*     + (* Prefix *) *)
(*       Unshelve. *)
(*       2 : { exact (fun x y => x = y /\ Q2 x). } *)
(*       rewrite EQ2; cycle 1. *)
(*       setoid_rewrite (itree_eta t1) in PC1. *)
(*       rewrite EQ in PC1. apply eqit_Ret in PC1. auto. *)
(*       rewrite has_post_post_strong in PC2. *)
(*       apply PC2. *)
(*     + (* Continuation. Equate t1 and t4. *) *)
(*       intros * [<- HQ]. efinal. *)
(*       setoid_rewrite (itree_eta t1) in EQ1. *)
(*       rewrite EQ in EQ1. rewrite <- EQ1; auto. *)
(*       apply eqit_Ret. *)
(*       specialize (F2 _ HQ). *)
(*       rewrite <- EQ1 in F2; auto. apply eqit_inv_Ret in F2. auto. *)

(*   - (* Tau *) *)
(*     rewrite (itree_eta t3). *)
(*     destruct (observe t3) eqn: EQ'; [ | | inv e]. *)
(*     + rewrite bind_ret_l. setoid_rewrite <- bind_ret_r at 5. *)
(*       ebind; econstructor. *)
(*       * (* Prefix *) *)
(*         Unshelve. *)
(*         2 : { exact (fun x y => x = y /\ Q1 x). } *)

(*         rewrite <- EQ1; cycle 1. *)
(*         setoid_rewrite (itree_eta t3) in PC2. *)
(*         rewrite EQ' in PC2. apply eqit_Ret in PC2. auto. *)

(*         setoid_rewrite (itree_eta t1). setoid_rewrite (itree_eta t1) in PC1. *)
(*         rewrite has_post_post_strong in PC1. *)
(*         rewrite EQ. apply eqit_Tau. rewrite EQ in PC1. *)
(*         apply eqit_inv_Tau_l in PC1. *)
(*         apply eqit_inv_Tau_r in PC1.  *)
(*         apply PC1. *)

(*       * (* Continuation. Equate t2 and t3. *) *)
(*         intros * [<- HQ]. efinal. *)
(*         setoid_rewrite (itree_eta t3) in EQ2. *)
(*         rewrite EQ' in EQ2. rewrite EQ2; auto. *)
(*         apply eqit_Ret. *)
(*         specialize (F1 _ HQ). *)
(*         rewrite EQ2 in F1; auto. apply eqit_inv_Ret in F1. auto. *)

(*     + rewrite !bind_tau. *)

(*       assert (t1 ≈ t). rewrite itree_eta. rewrite EQ. *)
(*       apply eqit_Tau_l. reflexivity. *)

(*       assert (t3 ≈ t0). rewrite itree_eta. rewrite EQ'. *)
(*       apply eqit_Tau_l. reflexivity. *)

(*       clear CIH0. *)

(*       estep. *)
(*       ebase; right. *)
(*       eapply CIH; eauto. *)
(*       setoid_rewrite <- H. auto. *)
(*       setoid_rewrite <- H0. auto. *)
(*       rewrite <- H. auto. rewrite <- H0. auto. *)
(* Qed. *)

(* Lemma eutt_inv_ret_l : *)
(*   forall E A Q r t1, eutt (E := E) (fun x y : A => Q x) (Ret r) t1 -> Q r. *)
(* Proof. *)
(*   intros. *)
(*   punfold H. *)
(*   unfold eqit_ in H. *)
(*   remember (observe (Ret r)) as x. *)
(*   revert Heqx . *)
(*   induction H; intros EQ; try now inv EQ. *)
(*   - apply IHeqitF; auto. *)
(* Qed. *)

(* Lemma eutt_inv_ret_r : *)
(*   forall E A Q r t1, eutt (E := E) (fun x y : A => Q y) t1 (Ret r) -> Q r. *)
(* Proof. *)
(*   intros. *)
(*   punfold H. *)
(*   unfold eqit_ in H. *)
(*   remember (observe (Ret r)) as x. *)
(*   revert Heqx . *)
(*   induction H; intros EQ; try now inv EQ. *)
(*   - apply IHeqitF; auto. *)
(* Qed. *)

(* Lemma commut_gen' : *)
(*   forall {A : Type} *)
(*     (Q1 Q2 : A -> Prop) (QQ : A -> Prop) *)
(*     (t1 t3 : itree void1 A) *)
(*     (t2 t4 : A -> itree void1 A), *)
(*     (forall i, eutt (fun x y => Q1 x /\ Q1 y) t1 (t4 i)) -> *)
(*     (forall i, eutt (fun x y => Q2 x /\ Q2 y) t3 (t2 i)) -> *)
(*       (forall a, Q1 a -> eutt (fun x y => QQ x /\ QQ y) t3 (t2 a)) -> *)
(*       (forall a, Q2 a -> eutt (fun x y => QQ x /\ QQ y) t1 (t4 a)) -> *)
(*     eutt (fun x y => QQ x /\ QQ y) (a <- t1 ;; t2 a) (a <- t3 ;; t4 a). *)
(* Proof. *)
(*   cbn. *)

(*   einit. ecofix CIH. *)
(*   intros * EQ1 EQ2 * PC1 PC2. *)
(*   setoid_rewrite (itree_eta t1) at 1. *)
(*   destruct (observe t1) eqn: EQ; [ | | inv e]. *)

(*   clear CIH0. *)
(*   - (* Ret *) *)
(*     (* Need this rewriting to reason about co-termination on t2 and t3. *) *)

(*     rewrite bind_ret_l. *)

(*     setoid_rewrite (itree_eta t1) in EQ1. rewrite EQ in EQ1. *)

(*     rewrite <- bind_ret_r. *)
(*     ebind. econstructor. *)
(*     Unshelve. 3 : exact (fun x y => QQ x /\ Q2 y). *)

(*     { *)
(*       specialize (EQ1 r). *)

(*       apply eutt_conj; cycle 1. *)
(*       eapply eqit_mon; auto. 2 : eapply eqit_flip; apply EQ2. intuition. destruct PR. auto. *)
(*       eapply eqit_mon; auto. *)
(*       2 : eapply eqit_flip; eapply PC1. intros * []; auto. *)

(*       setoid_rewrite (itree_eta (t4 r)) in EQ1. *)
(*       destruct (observe (t4 r)) eqn: EQ'; [ | | inv e]. *)
(*       apply eqit_inv_Ret in EQ1. destruct EQ1. auto. *)

(*       Set Nested Proofs Allowed. *)

(*       eapply eutt_inv_ret_l. eapply eqit_mon; auto. *)
(*       2 : eauto. *)
(*       intros * []; auto. *)
(*     } *)

(*     intros * []. *)

(*     efinal. *)

(*     specialize (EQ1 u2). *)

(*     setoid_rewrite (itree_eta (t4 u2)). *)
(*     setoid_rewrite (itree_eta (t4 u2)) in EQ1. *)
(*     destruct (observe (t4 u2)) eqn: EQ'; [ | | inv e]. *)
(*     apply eqit_Ret. split; eauto. *)
(*     apply eqit_inv_Ret in EQ1. destruct EQ1. *)
(*     specialize (PC2 _ H0). *)
(*     setoid_rewrite (itree_eta (t4 u2)) in PC2. *)
(*     setoid_rewrite (itree_eta t1) in PC2. *)
(*     rewrite EQ', EQ in PC2. apply eqit_inv_Ret in PC2. destruct PC2. auto. *)


(*     specialize (PC2 _ H0). *)
(*     setoid_rewrite (itree_eta t1) in PC2. *)
(*     rewrite EQ in PC2. *)
(*     setoid_rewrite (itree_eta (t4 u2)) in PC2. *)
(*     rewrite EQ' in PC2. *)

(*     eapply eqit_mon; auto; cycle 1. *)
(*     eapply eqit_trans; cycle 2. *)
(*     apply eqit_Ret. Unshelve. 7 : exact (fun x y => QQ x /\ QQ y). cbn. split; auto. *)
(*     eapply eutt_inv_ret_l. eapply eqit_mon; auto; cycle 1. eapply PC2. *)
(*     intros * []; auto. apply PC2. *)
(*     intros * []; auto. destruct REL1, REL2. split; auto. *)

(*   - (* Tau *) *)
(*     clear CIH0. *)

(*     (* specialize (EQ1 i). *) *)
(*     setoid_rewrite (itree_eta t3). *)
(*     destruct (observe t3) eqn: EQ'; [ | | inv e]; cycle 1. *)

(*     + rewrite !bind_tau. *)

(*       assert (t1 ≈ t). rewrite itree_eta. rewrite EQ. *)
(*       apply eqit_Tau_l. reflexivity. *)

(*       assert (t3 ≈ t0). rewrite itree_eta. rewrite EQ'. *)
(*       apply eqit_Tau_l. reflexivity. *)

(*       estep. *)

(*       ebase; right. *)
(*       eapply CIH; eauto. *)
(*       intros; rewrite <- H; eauto. *)
(*       intros; rewrite <- H0; eauto. *)
(*       intros; rewrite <- H0; eauto. *)
(*       intros; rewrite <- H; eauto. *)

(*     + rewrite bind_ret_l. *)
(*       setoid_rewrite (itree_eta t1) in EQ1. rewrite EQ in EQ1. *)

(*       setoid_rewrite <- bind_ret_r at 5. *)
(*       ebind. econstructor. *)
(*       Unshelve. 3 : exact (fun x y => Q1 x /\ QQ y). *)

(*       apply eutt_conj; cycle 1. *)
(*       specialize (PC2 r). setoid_rewrite (itree_eta t1) in PC2. *)
(*       rewrite EQ in PC2. *)
(*       eapply eqit_mon; auto. *)
(*       Unshelve. *)
(*       2 : eapply eqit_flip. 2 : unfold flip. *)
(*       5 : exact (fun _ x => QQ x). cbn. intros; auto. *)
(*       apply eqit_flip. eapply eqit_mon; auto. 2 : eapply PC2. *)
(*       intros * []; intuition. *)

(*       setoid_rewrite (itree_eta t3) in EQ2. *)
(*       rewrite EQ' in EQ2. eapply eutt_inv_ret_l. *)
(*       eapply eqit_mon; auto. 2 : eapply EQ2. *)
(*       intros * []; eauto. *)

(*       eapply eqit_mon; auto; cycle 1. *)
(*       apply EQ1. intros * []; auto. *)

(*       intros * []. *)

(*       efinal. *)

(*       specialize (EQ1 u2). *)
(*       setoid_rewrite (itree_eta (t2 u1)). *)
(*       destruct (observe (t2 u1)) eqn: EQ''; [ | | inv e]. *)
(*       apply eqit_Ret. split; eauto. *)
(*       specialize (EQ2 u1). setoid_rewrite (itree_eta (t2 u1)) in EQ2. *)
(*       rewrite EQ'' in EQ2. *)
(*       specialize (PC1 _ H). *)

(*       setoid_rewrite (itree_eta (t2 u1)) in PC1. *)
(*       rewrite EQ'' in PC1. clear EQ2. *)

(*       eapply eutt_inv_ret_r. eapply eqit_mon; eauto; cycle 1. *)
(*       intros * []; auto. *)

(*       specialize (PC1 _ H). *)
(*       setoid_rewrite (itree_eta (t2 u1)) in PC1. *)
(*       rewrite EQ'' in PC1. *)
(*       setoid_rewrite (itree_eta t3) in PC1. *)
(*       rewrite EQ' in PC1. *)

(*       eapply eqit_mon; auto; cycle 1. *)
(*       eapply eqit_trans; cycle 2. *)
(*       2 : apply eqit_Ret. Unshelve. 9 : exact (fun x y => QQ x /\ QQ y). 2 : split ; auto. *)
(*       2 : { *)
(*         eapply eutt_inv_ret_l. eapply eqit_mon; auto; cycle 1. eapply PC1. *)
(*         intros * []; auto. *)
(*       } *)
(*       apply eqit_flip. apply PC1. 2 : auto. *)
(*       intros * []; auto. destruct REL1, REL2. split; auto. *)
(* Qed. *)
