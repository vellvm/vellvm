From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqEuttHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma eses_aux3:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (R2 : Type) (RR1 : R1 -> R2 -> Prop)
    (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (m1 : itree E R2) (m2 : itree E R3),
    paco2 (eqit_ RR2 true true id) bot2 m1 m2 ->
    forall r0 : R1,
      secure_eqitF Label priv RR1 true true l id
                   (upaco2 (secure_eqit_ Label priv RR1 true true l id) bot2) (RetF r0)
                   (observe m1) ->
      secure_eqitF Label priv (rcompose RR1 RR2) true true l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true true l id) r)
                   (RetF r0) (observe m2).
Proof.
  intros E R3 R1 Label priv l R2 RR1 RR2 r m1 m2 REL r0 Hsec.
  remember (RetF r0) as x.
  punfold REL. red in REL. hinduction Hsec before r; intros; inv Heqx; eauto.
  - remember (RetF r2) as y. hinduction REL before r; intros; inv Heqy; eauto with itree.
  - eapply IHHsec; eauto. pstep_reverse. setoid_rewrite <- tau_eutt at 1. pfold. auto.
  - remember (VisF e k2) as y.
    hinduction REL before r; intros; inv Heqy; ddestruction; subst; eauto with itree.
    pclearbot. unpriv_ind. eapply H0; eauto. pstep_reverse.
Qed.


Lemma eses_aux4:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (R2 : Type) (RR1 : R1 -> R2 -> Prop)
    (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (m1 : itree E R2) (m2 : itree E R3),
    (forall (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
        eqit_secure Label priv RR1 true true l t1 t2 -> eutt RR2 t2 t3 -> r t1 t3) ->
    paco2 (eqit_ RR2 true true id) bot2 m1 m2 ->
    forall (X : Type) (e : E X) (k : X -> itree E R1),
      secure_eqitF Label priv RR1 true true l id
                   (upaco2 (secure_eqit_ Label priv RR1 true true l id) bot2) (VisF e k)
                   (observe m1) ->
      leq (priv X e) l ->
      secure_eqitF Label priv (rcompose RR1 RR2) true true l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true true l id) r)
                   (VisF e k) (observe m2).
Proof.
  intros E R3 R1 Label priv l R2 RR1 RR2 r m1 m2 CIH REL X e k Hsec SECCHECK.
  punfold REL. red in REL. remember (VisF e k) as y.
  hinduction Hsec before r; intros; inv Heqy; ddestruction; subst; try contradiction.
  - eapply IHHsec; eauto. pstep_reverse. rewrite <- tau_eutt at 1. pfold. auto.
  - pclearbot. inv REL; ddestruction; subst.
    + constructor; auto. right. pclearbot. eapply CIH; eauto with itree.
      apply H.
    + constructor; auto. remember (VisF e0 k2) as y.
      hinduction REL0 before r; intros; inv Heqy; ddestruction; subst; try contradiction.
      * constructor; auto. right. pclearbot. eapply CIH; eauto with itree. apply H.
      * constructor; auto. eapply IHREL0; eauto.
  - rewrite H2. remember (VisF e k2) as y.
    hinduction REL before r; intros; inv Heqy; ddestruction; subst; try contradiction.
    + rewrite itree_eta' at 1. unpriv_ind. rewrite <- H2. eapply H0; eauto.
      pclearbot.
      pstep_reverse.
    + constructor; auto. eapply IHREL; eauto.
Qed.

(*This lemma lets us lift compiler correctness results to compiler security preservation results*)
Lemma eutt_secure_eqit_secure : forall E Label priv l R1 R2 R3 (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
  (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
    eqit_secure Label priv RR1 true true l t1 t2 -> eutt RR2 t2 t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) true true l t1 t3.
Proof.
  intros E Label priv l R1 R2 R3 RR1 RR2. pcofix CIH. intros t1 t2 t3 Hsec Heutt.
  punfold Heutt. red in Heutt. punfold Hsec. red in Hsec.
  pfold. red. hinduction Heutt before r; intros; subst; auto with itree.
  - remember (RetF r2) as x. remember (RetF r1)  as y. hinduction Hsec before r; intros; try inv Heqx; try inv Heqy; subst; auto with itree.
    + constructor; eauto with itree.
    + constructor; auto. eapply IHHsec; eauto.
    + rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
  - genobs_clear t1 ot1.
    assert (Ht1 : (exists m3, ot1 = TauF m3) \/ (forall m3, ot1 <> TauF m3) ).
    { destruct ot1; eauto; right; repeat intro; discriminate. }
    (* because of the extra inductive cases this is not enough *)
    destruct Ht1 as [ [m3 Hm3] | Ht1 ].
    + subst. pclearbot. constructor. right. eapply CIH; eauto.
      apply tau_eqit_secure. apply eqit_secure_sym. apply tau_eqit_secure.
      apply eqit_secure_sym. pfold. auto.
    + destruct ot1; try (exfalso; eapply Ht1; eauto; fail).
      * pclearbot. rewrite itree_eta'. rewrite itree_eta' in Hsec.
        eapply eses_aux3; eauto. pfold. constructor.
        left. auto.
      * assert (leq (priv _ e) l \/ ~ leq (priv _ e) l).
        { apply classic. }
        destruct H as [SECCHECK | SECCHECK]; destruct ( classic_empty X  ).
        ++ pclearbot. rewrite itree_eta'. rewrite itree_eta' in Hsec.
           eapply eses_aux4; eauto. do 2 rewrite tau_eutt. auto.
        ++ pclearbot. rewrite itree_eta'.
           rewrite itree_eta' in Hsec. eapply eses_aux4; eauto.
           do 2 rewrite tau_eutt. auto.
        ++ unpriv_halt. pclearbot. right. eapply CIH; eauto.
           apply eqit_secure_sym. apply tau_eqit_secure. apply eqit_secure_sym.
           pfold. auto.
        ++ pclearbot.
           unpriv_co. pclearbot. right. eapply CIH; try apply REL.
           apply eqit_secure_sym. apply tau_eqit_secure.
           apply eqit_secure_sym.
           eapply unpriv_e_eqit_secure; eauto.
           pfold. auto.
  - pclearbot. destruct (classic (leq (priv _ e) l ) ).
    + genobs_clear t1 ot1.
      remember (VisF e k1) as y.
      hinduction Hsec before r; intros; try inv Heqy; ddestruction; subst; try contradiction;
      eauto with itree.
      * constructor; auto. right. pclearbot. eapply CIH; eauto with itree. apply H.
      * rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
    + remember (VisF e k1) as y.
      hinduction Hsec before r; intros; inv Heqy; ddestruction; subst; try contradiction.
      * eauto with itree.
      * pclearbot. unpriv_co. right. eapply CIH; eauto with itree. apply H.
      * pclearbot. unpriv_co. right. eapply CIH; eauto with itree. apply H.
      * rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
      * destruct (observe t0).
        -- rewrite itree_eta' at 1. unpriv_ind.
           specialize (H a).
           eapply eses_aux3; eauto.
        -- unpriv_co. right. eapply CIH; eauto with itree. apply tau_eqit_secure.
           pfold. apply H.
        -- destruct (classic (leq (priv _ e) l ) ).
           ++ rewrite itree_eta' at 1. unpriv_ind.
              eapply eses_aux4; eauto.
           ++ destruct (classic_empty X).
              ** unpriv_halt. right. eapply CIH; eauto with itree. pfold. apply H.
              ** unpriv_co. right. eapply CIH; eauto with itree.
                 eapply unpriv_e_eqit_secure; eauto. pfold. apply H.
      * pclearbot. unpriv_halt. right. eapply CIH; eauto. pfold.
        constructor; intros; auto with itree.
      * pclearbot. unpriv_halt. right. eapply CIH; eauto with itree. apply H.
      * pclearbot. unpriv_halt. right. eapply CIH; eauto with itree. apply H.
        pfold. constructor; auto with itree.
  - eapply IHHeutt; eauto. pstep_reverse. apply eqit_secure_sym.
    apply tau_eqit_secure. apply eqit_secure_sym. pfold. auto.
Qed.
