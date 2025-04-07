From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqProgInsens
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant case_rel {A1 A2 B : Type} (R1 : A1 -> B -> Prop) (R2 : A2 -> B -> Prop) : (A1 + A2) -> B -> Prop :=
  | crl a1 b : R1 a1 b -> case_rel R1 R2 (inl a1) b
  | crr a2 b : R2 a2 b -> case_rel R1 R2 (inr a2) b.

Lemma pi_eqit_secure_iter_ret E R S1 S2 Label priv l b2 s body
      (Rinv : R -> S2 -> Prop) (RS : S1 -> S2 -> Prop)
  (HRinv : (forall r', Rinv r' s ->
            pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (body r') (Ret s) )) :
  forall r,
  Rinv r s ->
  @pi_eqit_secure E S1 S2 Label priv RS true b2 l (ITree.iter body r) (Ret s).
Proof.
  ginit. gcofix CIH. intros r0 Hr0. setoid_rewrite unfold_iter.
  assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (body r0) (Ret s)).
  auto. remember (body r0) as t. clear Heqt. generalize dependent t.
  gcofix CIH'. intros t Ht.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq.
    assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Ret r1) (Ret s) ).
    rewrite <- Heq. auto.
    pinversion H. subst. inv H2.
    + rewrite bind_ret_l. gstep. constructor; auto.
      gfinal. left. eapply CIH; eauto.
    + rewrite bind_ret_l. gstep. constructor. auto.
  - rewrite Heq. rewrite bind_tau. gstep. constructor; auto.
    gfinal. left. eapply CIH'.
    assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Tau t0) (Ret s)).
    rewrite <- Heq. auto. pinversion H. rewrite <- itree_eta. auto.
  - destruct (classic (leq (priv _ e) l ) ).
    + exfalso. apply HRinv in Hr0.
      assert (pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Vis e k) (Ret s) ).
      { rewrite <- Heq. auto. }
      pinversion H0; subst. ddestruction. subst. contradiction.
    + rewrite Heq. rewrite bind_vis.
      gstep. constructor; auto. intros x. gfinal. left. eapply CIH'.
      assert ( pi_eqit_secure Label priv (case_rel Rinv RS) true b2 l (Vis e k) (Ret s)) .
      rewrite <- Heq. auto. pinversion H0; subst; ddestruction; subst.
      rewrite <- itree_eta. apply H2.
Qed.

Ltac use_simpobs :=
  repeat match goal with
         | H : TauF _ = observe ?t |- _ => apply simpobs in H
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

(* I believe we could generalize this lemma for any t2 that converges along all paths *)
Lemma pi_eqit_secure_trans_ret E R1 R2 R3 Label priv l b1 b2
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
      (t1 : itree E R1) (r : R2) (t3 : itree E R3) :
  pi_eqit_secure Label priv RR1 b1 b2 l t1 (Ret r) ->
  pi_eqit_secure Label priv RR2 b1 b2 l (Ret r) t3 ->
  pi_eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  revert t1 t3. ginit. gcofix CIH.
  intros. pinversion H0; subst; try inv CHECK; use_simpobs.
  - rewrite H. generalize dependent t3. gcofix CIH'. intros t3 Ht3.
    pinversion Ht3; use_simpobs.
    + rewrite H2. gstep. constructor; auto. econstructor; eauto.
    + rewrite H2. gstep. constructor; auto. gfinal. left. eapply CIH'.
      symmetry in H1. use_simpobs. rewrite H1 in H4. auto.
    + rewrite H2. gstep. constructor; auto. intros. gfinal. left.
      eapply CIH'. symmetry in H1. use_simpobs. setoid_rewrite H1 in H4. apply H4.
  - symmetry in H2. use_simpobs. rewrite H. gstep. constructor; auto.
    gfinal. left. eapply CIH; auto. rewrite <- H2. auto.
  - symmetry in H2. use_simpobs. rewrite H. gstep. constructor; auto.
    intros. gfinal. left. apply CIH; auto. rewrite <- H2. apply H3.
Qed.

Lemma pi_eqit_secure_pub_vis E R1 R2 RR Label priv l b1 b2 A (e : E A)
      (k1 : A -> itree E R1) (k2 : A -> itree E R2) :
  leq (priv _ e) l ->
  (forall a, pi_eqit_secure Label priv RR b1 b2 l (k1 a) (k2 a) ) ->
  pi_eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2).
Proof.
  intros. pfold. constructor; auto. left. apply H0.
Qed.

Lemma pi_eqit_secure_priv_vislr E R1 R2 RR Label priv l b1 b2 A B (e1 : E A) (e2 : E B)
      (k1 : A -> itree E R1) (k2 : B -> itree E R2) :
  ~ leq (priv _ e1) l -> ~ leq (priv _ e2) l ->
  (forall a b, pi_eqit_secure Label priv RR b1 b2 l (k1 a) (k2 b) ) ->
  pi_eqit_secure Label priv RR b1 b2 l (Vis e1 k1) (Vis e2 k2).
Proof.
  intros. pfold. constructor; auto. left. apply H1.
Qed.

Lemma pi_eqit_secure_priv_visl E R1 R2 RR Label priv l b2 A (e1 : E A)
      (k1 : A -> itree E R1) (t2 : itree E R2) :
  ~ leq (priv _ e1) l ->
  (forall a, pi_eqit_secure Label priv RR true b2 l (k1 a) t2 ) ->
  pi_eqit_secure Label priv RR true b2 l (Vis e1 k1) t2.
Proof.
  intros. pfold. constructor; auto. left. apply H0.
Qed.

Lemma pi_eqit_secure_priv_visr E R1 R2 RR Label priv l b1 A (e1 : E A)
      (t1 : itree E R1) (k2 : A -> itree E R2) :
  ~ leq (priv _ e1) l ->
  (forall a, pi_eqit_secure Label priv RR b1 true l t1 (k2 a) ) ->
  pi_eqit_secure Label priv RR b1 true l t1 (Vis e1 k2).
Proof.
  intros. pfold. constructor; auto. left. apply H0.
Qed.

Lemma pi_secure_eqit_bind'
     : forall (E : Type -> Type) (R1 R2 S1 S2 : Type) (RR : R1 -> R2 -> Prop)
         (RS : S1 -> S2 -> Prop) (b1 b2 : bool) (Label : Preorder)
         (priv : forall A : Type, E A -> L) (l : L)
         r
         (t1 : itree E R1) (t2 : itree E R2) (k1 : R1 -> itree E S1)
         (k2 : R2 -> itree E S2),
       (forall (r1 : R1) (r2 : R2),
        RR r1 r2 -> paco2 (pi_secure_eqit_ Label priv RS b1 b2 l id) r (k1 r1) (k2 r2)) ->
       pi_eqit_secure Label priv RR b1 b2 l t1 t2 ->
       gpaco2 (pi_secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) bot2 r
              (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. revert H0. generalize dependent t2. generalize dependent t1.
  gcofix CIH. intros t1 t2 Ht12.
  pinversion Ht12; use_simpobs.
  - rewrite H0, H1. repeat rewrite bind_ret_l. gfinal. right. eapply paco2_mon; try apply CIH0.
    auto.
  - rewrite H0, H1. repeat rewrite bind_tau. gstep. constructor. gfinal. left. eapply CIH.
    auto.
  - rewrite H0. rewrite bind_tau. gstep. constructor; auto.
    gfinal. left. eapply CIH. apply simpobs in H1. rewrite <- itree_eta in H1.
    rewrite H1. auto.
  - rewrite H1. rewrite bind_tau. gstep. constructor; auto.
    gfinal. left. eapply CIH. apply simpobs in H0. rewrite <- itree_eta in H0.
    rewrite H0. auto.
  - rewrite H0, H1. repeat rewrite bind_vis. gstep. constructor; auto.
    intros. gfinal. left. eapply CIH; eauto. apply H2.
  - rewrite H0, H1. rewrite bind_vis, bind_tau. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH; eauto. apply H2.
  - rewrite H0, H1. rewrite bind_vis, bind_tau. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH; eauto. apply H2.
  - rewrite H0, H1. repeat rewrite bind_vis. gstep. red. cbn. unpriv_pi.
    gfinal. left. eapply CIH. apply H2.
  - rewrite H0. rewrite bind_vis. gstep. constructor; auto. gfinal.
    left. eapply CIH. apply simpobs in H1. rewrite <- itree_eta in H1. rewrite H1.
    apply H2.
  - rewrite H1. rewrite bind_vis. gstep. constructor; auto. gfinal.
    left. eapply CIH. apply simpobs in H0. rewrite <- itree_eta in H0. rewrite H0.
    apply H2.
Qed.
