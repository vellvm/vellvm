From Coq Require Import Morphisms.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.Labels
     Secure.SecureEqHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma tau_eqit_secure : forall E R1 R2 Label priv l RR (t1 : itree E R1) (t2 : itree E R2),
    eqit_secure Label priv RR true true l (Tau t1) t2 -> eqit_secure Label priv RR true true l t1 t2.
Proof.
  intros E R1 R2 Label priv l RR.  intros t1 t2 Hsec. pstep. red.
  punfold Hsec. red in Hsec. cbn in *. remember (TauF t1) as x.
  hinduction Hsec before priv; intros;  inv Heqx; pclearbot; try inv CHECK; auto with itree.
  - constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse.
  - punfold H.
Qed.

Lemma unpriv_e_eqit_secure : forall E A R1 R2 Label priv l RR (e : E A) (k : A -> itree E R1)
      (t : itree E R2),
    (~leq (priv A e) l ) ->
    eqit_secure Label priv RR true true l (Vis e k) t ->
    forall a, eqit_secure Label priv RR true true l (k a) t.
Proof.
  intros. generalize dependent t. rename H into Hunpriv. generalize dependent a.
  intros. punfold H0. red in H0. cbn in *. pfold. red.
  remember (VisF e k) as x. genobs_clear t ot.
  hinduction H0 before l; intros; try inv Heqx;
    ddestruction; subst; try contradiction; try contra_size; auto.
  - constructor; auto. eapply IHsecure_eqitF; eauto.
  - pclearbot. constructor; auto. pstep_reverse.
  - unpriv_ind. pstep_reverse. pclearbot. apply H.
  - unpriv_ind. eapply H0; eauto.
  - pclearbot. rewrite itree_eta'. pstep_reverse.
Qed.


(* reformat this lemma? useful but unclear *)
Lemma eses_aux1: forall (E : Type -> Type) (R2 R1 : Type) (Label : Preorder)
                    (priv : forall A : Type, E A -> L) (l : L) (RR : R1 -> R2 -> Prop)
                    (r : itree E R1 -> itree E R2 -> Prop) (m1 m2 : itree E R1),
              m1 ≈ m2 ->
               (forall (t1 t1' : itree E R1) (t2 : itree E R2),
                   t1 ≈ t1' -> eqit_secure Label priv RR true true l t1 t2 -> r t1' t2) ->
               forall (X : Type) (e : E X) (k : X -> itree E R2),
                 secure_eqitF Label priv RR true true l id
                              (upaco2 (secure_eqit_ Label priv RR true true l id) bot2) (observe m1)
                              (VisF e k) ->
                 leq (priv X e) l ->
                 secure_eqitF Label priv RR true true l id
                              (upaco2 (secure_eqit_ Label priv RR true true l id) r) (observe m2)
                              (VisF e k).
Proof.
  intros E R2 R1 Label priv l RR r m1 m2 REL CIH X e k Hsec SECCHECK.
  remember (VisF e k) as x. punfold REL. red in REL. rewrite Heqx.
  hinduction Hsec before r; intros; try inv Heqx; ddestruction; subst; try contradiction; auto.
  - eapply IHHsec; eauto.
    pstep_reverse. setoid_rewrite <- tau_eutt at 1. pfold. auto.
  - pclearbot. remember (VisF e0 k1) as y.
    hinduction REL before r; intros; try inv Heqy; ddestruction; subst; auto.
    + constructor; auto. right. eapply CIH; eauto; try apply H.
      pclearbot. apply REL.
    + constructor; eauto.
  - rewrite H2. remember (VisF e k1) as y.
    hinduction REL before r; intros; try inv Heqy; ddestruction; subst; auto.
    + pclearbot. rewrite <- H2. unpriv_ind. rewrite H2. eapply H0; eauto.
      Unshelve. all: auto. pstep_reverse.
    + constructor; auto. eapply IHREL; eauto.
Qed.

Lemma eses_aux2:
forall (E : Type -> Type) (R2 R1 : Type) (Label : Preorder)
    (priv : forall A : Type, E A -> L) (l : L) (RR : R1 -> R2 -> Prop)
    (r : itree E R1 -> itree E R2 -> Prop) (m1 m2 : itree E R1) (r0 : R2),
  m1 ≈ m2 ->
  secure_eqitF Label priv RR true true l id
    (upaco2 (secure_eqit_ Label priv RR true true l id) bot2) (observe m1)
    (RetF r0) ->
  secure_eqitF Label priv RR true true l id
    (upaco2 (secure_eqit_ Label priv RR true true l id) r) (observe m2)
    (RetF r0).
Proof.
  intros E R2 R1 Label priv l RR r m1 m2 r0 Heutt Hsec.
  punfold Heutt. red in Heutt. remember (RetF r0) as x.
  rewrite Heqx. hinduction Hsec before r; intros; inv Heqx; auto with itree.
  - remember (RetF r1) as y.
    hinduction Heutt before r; intros; inv Heqy; auto with itree.
    constructor; auto. eapply IHHeutt; eauto.
  - eapply IHHsec; eauto. pstep_reverse. rewrite <- tau_eutt at 1. pfold. auto.
  - remember (VisF e k1) as y.
    hinduction Heutt before r; intros; inv Heqy; ddestruction; subst; auto.
    +  unpriv_ind. rewrite H2. eapply H0; eauto.
       pclearbot. pstep_reverse.
    + constructor; auto. eapply IHHeutt; eauto.
Qed.

Definition classic_empty := Secure.Labels.classic_empty.

(*tomorrow start on the transitivity proof *)
Lemma eutt_secure_eqit_secure : forall E Label priv l R1 R2 RR (t1 t1': itree E R1) (t2 : itree E R2),
    t1 ≈ t1' -> eqit_secure Label priv RR true true l t1 t2 ->
    eqit_secure Label priv RR true true l t1' t2.
Proof.
  intros E Label priv l R1 R2 RR. pcofix CIH. intros t1 t1' t2 Heutt Hsec.
  punfold Heutt. red in Heutt. punfold Hsec. red in Hsec.
  pfold. red. hinduction Heutt before r; intros; subst; auto with itree.
  - remember (RetF r2) as x. hinduction Hsec before r; intros; try inv Heqx; auto with itree.
    + constructor; auto. eapply IHHsec; eauto.
    + unpriv_ind. eapply H0; eauto.
  - genobs_clear t2 ot2.
    assert (Ht2 : (exists m3, ot2 = TauF m3) \/ (forall m3, ot2 <> TauF m3) ).
    { destruct ot2; eauto; right; repeat intro; discriminate. }
    (* because of the extra inductive cases this is not enough *)
    destruct Ht2 as [ [m3 Hm3] | Ht2 ].
    + subst. pclearbot. constructor. right. eapply CIH; eauto.
      apply tau_eqit_secure. apply eqit_secure_sym. apply tau_eqit_secure.
      apply eqit_secure_sym. pfold. auto.
    + destruct ot2; try (exfalso; eapply Ht2; eauto; fail).
      * pclearbot. rewrite itree_eta' at 1. eapply eses_aux2 with (m1 := Tau m1); eauto.
        do 2 rewrite tau_eutt. auto.
      * assert (leq (priv _ e) l \/ ~ leq (priv _ e) l).
        { apply classic. }
        destruct H as [SECCHECK | SECCHECK]; destruct ( classic_empty X  ).
        ++ pclearbot. rewrite itree_eta' at 1. apply eses_aux1 with (m1 := Tau m1); auto.
           do 2 rewrite tau_eutt. auto.
        ++ pclearbot. rewrite itree_eta' at 1. apply eses_aux1 with (m1 := Tau m1); auto.
           do 2 rewrite tau_eutt. auto.
        ++ unpriv_halt. pclearbot. right. eapply CIH; eauto.
           apply tau_eqit_secure. pfold. auto.
        ++ pclearbot.
           unpriv_co. pclearbot. right. eapply CIH. apply REL.
           apply tau_eqit_secure.
           apply eqit_secure_sym.
           eapply unpriv_e_eqit_secure; eauto.
           apply eqit_secure_sym. pfold. auto.
  - pclearbot. rewrite itree_eta' at 1. pstep_reverse.
    assert (eqit_secure Label priv RR true true l (Vis e k1) t2 ).
    { pfold; auto. }
    clear Hsec. rename H into Hsec.
    destruct (classic (leq (priv _ e) l ) ).
    + pstep. red. punfold Hsec. red in Hsec.
      cbn in *. remember (VisF e k1) as x.
      hinduction Hsec before r; intros; inv Heqx; ddestruction; subst; try contradiction; auto.
      * constructor; auto. eapply IHHsec; eauto.
      * constructor; auto; intros. right. eapply CIH; try apply REL. pclearbot. apply H.
      * rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + destruct (classic_empty u).
      * pfold. red. cbn.  punfold Hsec. red in Hsec. cbn in *.
        destruct (observe t2).
        -- inv Hsec; contra_size.
        -- unpriv_halt. right. apply CIH with (t1 := Vis e k1).
           ++ pfold. constructor. left. auto.
           ++ inv Hsec; ddestruction; subst; try contradiction;  try contra_size. pfold. auto.
              pclearbot. auto.
        -- inv Hsec; ddestruction; subst; try contradiction; try contra_size.
           ++ unpriv_halt. right. apply CIH with (t1 := Vis e k1).
              { pfold. constructor. red. auto. }
              { rewrite H1 in H3. pfold. apply H3. }
           ++ pclearbot. unpriv_halt. right. apply CIH with (t1 := Vis e k1).
              { pfold. constructor. red. auto. }
              { apply H2. }
           ++ pclearbot. unpriv_halt. contra_size.
      * pfold. red. cbn.  punfold Hsec. red in Hsec. cbn in *.
        destruct (observe t2).
        ++ rewrite itree_eta' at 1. rewrite itree_eta' in Hsec at 1.
           eapply eses_aux2; eauto. pfold. constructor. red. auto.
        ++ unpriv_co. right. apply CIH with (t1 := k1 a); try apply REL.
           eapply unpriv_e_eqit_secure; eauto. apply eqit_secure_sym.
           apply tau_eqit_secure. apply eqit_secure_sym. pfold. auto.
        ++ destruct (classic (leq (priv _ e0) l )).
           ** rewrite itree_eta' at 1.
              eapply eses_aux1 with (m1 := Vis e k1); eauto.
              pfold. constructor. red. auto.
           ** destruct (classic_empty X).
              --- unpriv_halt. right. eapply CIH; try apply REL.
                  eapply unpriv_e_eqit_secure; eauto. pfold. auto.
              --- unpriv_co. right. eapply CIH; try apply REL.
                  (* eapply unpriv_e_eqit_secure; eauto. *)
                  do 2 (eapply unpriv_e_eqit_secure; eauto; apply eqit_secure_sym).
                  pfold. auto.
  - eapply IHHeutt; eauto. pstep_reverse.
    apply tau_eqit_secure. pfold. auto.
Qed.


Lemma eqit_secure_TauLR :
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (t0 : itree E R2)
    (t4 : itree E R3),
    eqit_secure Label priv RR2 b1 b2 l (Tau t0) (Tau t4) ->
    eqit_secure Label priv RR2 b1 b2 l t0 t4.
Proof.
  intros E R3 Label priv l b1 b2 R2 RR2.
  intros. punfold H. red in H. cbn in *. pstep. red.
  remember (TauF t0) as x. remember (TauF t4) as y.
  hinduction H before b2; intros;  try discriminate.
  - inv Heqx; inv Heqy. pclearbot. pstep_reverse.
  - inv Heqx. inv H; eauto with itree.
    + pclearbot. unpriv_ind. pstep_reverse.
    + unpriv_ind. rewrite H1 in H2.
      specialize (H2 a). genobs (k1 a) ok1. clear Heqok1.
      remember (TauF t4) as y.
      hinduction H2 before b2; intros; inv Heqy; try inv CHECK; eauto with itree.
      * pclearbot. constructor; auto; pstep_reverse.
      * pclearbot. unpriv_ind. pstep_reverse.
      * pclearbot. punfold H.
    + pclearbot. punfold H2.
  - inv Heqy. inv H; eauto with itree.
    + pclearbot. unpriv_ind. pstep_reverse.
    + rewrite H0 in H2. unpriv_ind. specialize (H2 a).
      genobs (k2 a) ok2. clear Heqok2.
      remember (TauF t0) as y.
      hinduction H2 before b2; intros; inv Heqy; try inv CHECK; eauto with itree.
      * pclearbot. constructor; auto. pstep_reverse.
      * unpriv_ind. pclearbot. pstep_reverse.
      * pclearbot. punfold H.
    + pclearbot. punfold H2.
Qed.

Lemma eqit_secure_TauLVisR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop),
    forall (t3 : itree E R2) (X : Type) (e : E X) (k : X -> itree E R3) (a : X),
      (~ leq (priv _ e) l) ->
      eqit_secure Label priv RR2 b1 b2 l (Tau t3) (Vis e k) ->
      eqit_secure Label priv RR2 b1 b2 l t3 (k a).
Proof.
  intros E R3 Label priv l b1 b2 R2 RR t3 A e k a He Hsec.
  punfold Hsec. red in Hsec. cbn in *.
  remember (TauF t3) as x. remember (VisF e k) as y.
  hinduction Hsec before b2; intros; try discriminate.
  - inv Heqx. inv CHECK.
    remember (VisF e k) as y. pfold. red. clear IHHsec.
    hinduction Hsec before b2; intros; inv Heqy; ddestruction;  subst;
    try contradiction; try contra_size; eauto with itree.
    + constructor; auto. pclearbot. pstep_reverse.
    + unpriv_ind. pclearbot. pstep_reverse.
    + pclearbot. specialize (H a). punfold H.
  - inv Heqx. inv Heqy. ddestruction; subst. pclearbot. apply H.
  - inv Heqx. inv Heqy. ddestruction; subst. rewrite H2 in H.
    clear H0. clear H2 t1. remember (TauF t3) as x.
    pfold. red. specialize (H a).
    hinduction H before b2; intros; inv Heqx; try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. punfold H.
  -  pclearbot. inv Heqx. inv Heqy. ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_TauRVisL:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) RR2,
    forall (t3 : itree E R2) (X : Type) (e : E X) (k : X -> itree E R3) (a : X),
      (~ leq (priv _ e) l) ->
      eqit_secure Label priv RR2 b1 b2 l (Vis e k) (Tau t3)->
      eqit_secure Label priv RR2 b1 b2 l (k a) t3.
Proof.
  intros E R3 Label priv l b1 b2 R2 RR t3 A e k a He Hsec.
  punfold Hsec. red in Hsec. cbn in *.
  remember (TauF t3) as x. remember (VisF e k) as y.
  hinduction Hsec before b2; intros; try discriminate.
  - inv Heqx. inv CHECK. remember (VisF e k) as y. pfold. red. clear IHHsec.
    hinduction Hsec before b1; intros; inv Heqy; ddestruction; subst;
    try contradiction; eauto with itree.
    + constructor; auto with itree. pclearbot. pstep_reverse.
    + unpriv_ind. pclearbot. pstep_reverse.
    + contra_size.
    + contra_size.
    + pclearbot. specialize (H a). punfold H.
  - inv Heqx. inv Heqy. ddestruction; subst. pclearbot. apply H.
  - inv Heqx. inv Heqy. ddestruction; subst. pclearbot. rewrite H2 in H. inv CHECK.
    specialize (H a). pfold. red. remember (TauF t3) as y.
    hinduction H before b2; intros; inv Heqy; try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. punfold H.
  - inv Heqx. inv Heqy. ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_VisLR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2),
    ~ leq (priv A e) l ->
    forall (X : Type) (e0 : E X) (k : X -> itree E R3) (a : A),
      ~ leq (priv X e0) l ->
      forall a0 : X,
        eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) ->
        eqit_secure Label priv RR2 b1 b2 l (k2 a) (k a0).
Proof.
  intros E R3 Label priv l b1 b2 R2 RR2 A e k2 SECCHECK X e0 k a H0 a0 H1.
  pfold. red.
  punfold H1. red in H1. cbn in *. remember (VisF e k2) as x.
  remember (VisF e0 k) as y.
  hinduction H1 before l; intros; try discriminate.
  - inv Heqx. inv Heqy. ddestruction; subst. contradiction.
  - pclearbot. inv Heqx. inv Heqy. ddestruction; subst. pstep_reverse.
  - inv Heqx. ddestruction; subst. inv CHECK. clear H0.
    specialize (H a).
    rewrite Heqy in H. clear Heqy. remember (VisF e1 k) as y.
    hinduction H before l; intros; inv Heqy; ddestruction; subst; try contradiction;
    try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + unpriv_ind. pclearbot. pstep_reverse.
    + pclearbot. specialize (H a0). punfold H.

  - inv Heqy.  ddestruction; subst. inv CHECK. clear H0.
    rewrite Heqx in H. specialize (H a0).
    remember (VisF e0 k0) as y.
    hinduction H before b1; intros; inv Heqy; ddestruction; subst; try contradiction;
    try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. specialize (H a). punfold H.
  - inv Heqx; inv Heqy; ddestruction; subst. contra_size.
  - inv Heqx; inv Heqy; ddestruction; subst. contra_size.
Qed.

Lemma eqit_secure_private_VisLR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2),
    nonempty A ->
    ~ leq (priv A e) l ->
    forall (X : Type) (e0 : E X) (k : X -> itree E R3),
      ~ leq (priv X e0) l ->
      nonempty X ->
      (forall a a0,
        eqit_secure Label priv RR2 b1 b2 l (k2 a) (k a0)) ->
        eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) .
Proof.
  intros. pfold. red. cbn. unpriv_co. left. apply H3.
Qed.

Lemma eqit_secure_private_VisL:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b2 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R2) (t : itree E R3),
    nonempty A ->
    ~ leq (priv A e) l ->
    (forall a,
        eqit_secure Label priv RR2 true b2 l (k2 a) t) ->
        eqit_secure Label priv RR2 true b2 l (Vis e k2) t .
Proof.
  intros. pfold. red. cbn. unpriv_ind. pstep_reverse. apply H1.
Qed.

Lemma eqit_secure_private_VisR:
  forall (E : Type -> Type) (R3 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 : bool) (R2 : Type) (RR2 : R2 -> R3 -> Prop) (A : Type)
    (e : E A) (k2 : A -> itree E R3) (t : itree E R2),
    nonempty A ->
    ~ leq (priv A e) l ->
    (forall a,
        eqit_secure Label priv RR2 b1 true l t (k2 a)) ->
        eqit_secure Label priv RR2 b1 true l t (Vis e k2).
Proof.
  intros. pfold. red. cbn. unpriv_ind. pstep_reverse. apply H1.
Qed.

Lemma eqit_secure_public_Vis :  forall (E : Type -> Type) (R1 R2 : Type) (Label : Preorder) (priv : forall x : Type, E x -> L)
    (l : L) (b1 b2 : bool) (RR : R1 -> R2 -> Prop) (A : Type)
    (e : E A) (k1: A -> itree E R1) (k2 : A -> itree E R2),
    leq (priv A e) l ->
    (eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2) <->
    forall a, eqit_secure Label priv RR b1 b2 l (k1 a) (k2 a)).
Proof.
  split; intros.
  - pinversion H0; ddestruction; subst; try contradiction; apply H2.
  - pfold. constructor; auto. left. apply H0.
Qed.

Lemma eqit_secure_trans_aux1:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall x : Type, E x -> L) (l : L) (b2 : bool) (R2 : Type)
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (r0 : R3) (t4 : itree E R2),
    secure_eqitF Label priv RR2 true b2 l id
                 (upaco2 (secure_eqit_ Label priv RR2 true b2 l id) bot2) (observe t4)
                 (RetF r0) ->
    forall t : itree E R1,
      paco2 (secure_eqit_ Label priv RR1 true b2 l id) bot2 t t4 ->
      secure_eqitF Label priv (rcompose RR1 RR2) true b2 l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true b2 l id) r)
                   (observe t) (RetF r0).
Proof.
  intros E R3 R1 Label priv l b2 R2 RR1 RR2 r r0 t4 Ht23 t H.
  punfold H. red in H.
  remember (RetF r0) as x.
  hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; auto.
  - remember (RetF r1) as y.
    hinduction H0 before r; intros; inv Heqy; eauto with itree.
    rewrite itree_eta'. unpriv_ind. cbn. eapply H0; eauto.
  - eapply IHHt23; eauto.
    remember (TauF t1) as y.
    hinduction H before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. punfold H.
  - assert (Hne : nonempty A). { eauto. } (* add the condition that lets us assume this*)
    inv Hne. eapply (H0 a); eauto.
    remember (VisF e k1) as y.
    hinduction H1 before r; intros; inv Heqy; try inv CHECK; ddestruction; subst;
    try contradiction; try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. rewrite itree_eta' at 1. pstep_reverse.
Qed.

Lemma eqit_secure_trans_aux2:
  forall (E : Type -> Type) (R3 R1 : Type) (Label : Preorder)
    (priv : forall x : Type, E x -> L) (l : L) (b2 : bool) (R2 : Type)
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) (r : itree E R1 -> itree E R3 -> Prop)
    (X : Type) (e0 : E X) (k : X -> itree E R3) (t4 : itree E R2),
    leq (priv X e0) l ->
    secure_eqitF Label priv RR2 true b2 l id
                 (upaco2 (secure_eqit_ Label priv RR2 true b2 l id) bot2) (observe t4)
                 (VisF e0 k) ->
    (forall (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
        eqit_secure Label priv RR1 true b2 l t1 t2 ->
        eqit_secure Label priv RR2 true b2 l t2 t3 -> r t1 t3) ->
    forall t : itree E R1,
      paco2 (secure_eqit_ Label priv RR1 true b2 l id) bot2 t t4 ->
      secure_eqitF Label priv (rcompose RR1 RR2) true b2 l id
                   (upaco2 (secure_eqit_ Label priv (rcompose RR1 RR2) true b2 l id) r)
                   (observe t) (VisF e0 k).
Proof.
  intros E R3 R1 Label priv l b2 R2 RR1 RR2 r X e0 k t4 He0 Ht23 CIH0 t Ht.
  punfold Ht. red in Ht. remember (VisF e0 k) as x.
  hinduction Ht23 before r; intros; inv Heqx; try inv CHECK;
  ddestruction; subst; try contradiction; eauto.
  - eapply IHHt23; eauto. clear IHHt23. remember (TauF t1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. punfold H.
  - pclearbot. remember (VisF e0 k1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK;
    ddestruction; subst; try contradiction; eauto with itree.
    + pclearbot. constructor; auto. right. eapply CIH0. apply H.
      apply H0.
    + rewrite itree_eta'. unpriv_ind. eapply H0; eauto.
  - assert (nonempty A); eauto. inv H1. eapply H0; eauto.
    Unshelve. all : auto. clear H0. rewrite H2 in H.
    remember (VisF e k1) as y.
    hinduction Ht before r; intros; inv Heqy; try inv CHECK; ddestruction; subst;
    try contradiction; try contra_size; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. rewrite itree_eta' at 1. pstep_reverse.

Qed.


Lemma secret_halt_trans_1 : forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) t1 (e : E A) k t3,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l t1 (Vis e k) ->
    eqit_secure Label priv RR2 b1 b2 l (Vis e k) t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 A RR1 RR2 t1 e k t3 He HA.
  generalize dependent t3. generalize dependent t1.
  pcofix CIH. intros t1 t3 Ht1 Ht3.
  pfold. red. punfold Ht1. red in Ht1. punfold Ht3. red in Ht3.
  cbn in *.
  remember (VisF e k) as x.
  hinduction Ht1 before r; intros; inv Heqx; ddestruction; subst;
  try contradiction; try contra_size; eauto with itree.
  - pclearbot. inv Ht3; ddestruction; subst; try contradiction; try contra_size.
    + constructor. right. apply CIH; auto. pfold. auto.
    + unpriv_co; auto. right. apply CIH; auto. pfold. rewrite H0 in H2. apply H2.
    + pclearbot. constructor. right. apply CIH; auto.
    + pclearbot. destruct (classic_empty B).
      * unpriv_halt. right. apply CIH; auto with itree. pfold.
        red. cbn. unpriv_halt.
      * unpriv_co. right. apply CIH; auto. apply H1.
    + pclearbot. unpriv_halt. right. apply CIH; auto. pfold.
      red. cbn. unpriv_halt. contra_size.
  - pclearbot.  inv Ht3; ddestruction; subst; try contradiction; try contra_size.
    + unpriv_halt. right. apply CIH; auto.
      * pfold. red. cbn. unpriv_halt.
      * pfold. auto.
    + unpriv_halt. right. apply CIH; auto.
      * pfold. red. cbn. unpriv_halt.
      * pfold. auto. rewrite H0 in H2. apply H2.
    + pclearbot. unpriv_halt. right. apply CIH; auto.
      pfold. red. cbn. unpriv_halt.
    + pclearbot. unpriv_halt. right. apply CIH.
      * pfold. red. cbn. unpriv_halt.
      * apply H1.
    + unpriv_halt. contra_size.
  - pclearbot. inv Ht3; ddestruction; subst; try contradiction; try contra_size;
    destruct (classic_empty A0).
    + unpriv_halt. right. apply CIH; auto.
      * pfold. red. cbn. unpriv_halt. contra_size.
      * pfold. auto.
    + unpriv_co. right. apply CIH; auto; try apply H.
      pfold. auto.
    + unpriv_halt. right. apply CIH; auto.
      * pfold. red. cbn. unpriv_halt. contra_size.
      * pfold. rewrite H0 in H2. apply H2.
    + unpriv_co. right. apply CIH. apply H. rewrite H0 in H2.
      pfold. apply H2.
    + pclearbot. unpriv_halt. right. apply CIH; auto. pfold.
      red. cbn. unpriv_halt. contra_size.
    + pclearbot. unpriv_co. right. apply CIH; auto. apply H.
    + unpriv_halt. pclearbot. right. apply CIH; try apply H1.
      pfold. red. cbn. unpriv_halt. contra_size.
    + pclearbot. destruct (classic_empty B).
      * unpriv_halt. right. apply CIH; auto. apply H.
        pfold. red. cbn. unpriv_halt.
      * unpriv_co. right. apply CIH; eauto. apply H. apply H1.
    + pclearbot. unpriv_halt. contra_size.
    + pclearbot. unpriv_halt. right. apply CIH; auto. apply H.
      pfold. red. cbn. unpriv_halt. contra_size.
Qed.

Lemma secret_halt_trans_2 :  forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) (e : E A) k t2 t3,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l (Vis e k) t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l (Vis e k) t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 A RR1 RR2 e k t2 t3 He HA.
  generalize dependent t3. generalize dependent t2.
  pcofix CIH. intros t2 t3 Ht2 Ht23. pfold.
  red. cbn. punfold Ht2. punfold Ht23. red in Ht2. red in Ht23.
  cbn in *.
  hinduction Ht23 before r; intros; eauto with itree.
  - inv Ht2. ddestruction; subst. contra_size.
  - unpriv_halt. right. pclearbot. eapply CIH; eauto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot;  eauto.
    pfold. auto.
  - eapply IHHt23; eauto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
    punfold H0.
  - pclearbot.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
  - unpriv_halt. pclearbot.  inv SIZECHECK. right. eapply CIH; try apply H.
    Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
    + pfold. apply H2.
    + apply H1.
  - pclearbot. unpriv_halt. right. eapply CIH; try apply H.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
    pfold. auto.
  - pclearbot. unpriv_halt. inv SIZECHECK1. inv SIZECHECK2. right. eapply CIH; try apply H.
    Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
    + pfold. apply H2.
    + apply H1.
  - inv SIZECHECK.  eapply H0; eauto. Unshelve. all : auto.
    inv Ht2; ddestruction; subst; try contra_size; try contradiction; pclearbot; eauto.
    rewrite itree_eta' at 1. pstep_reverse.
  - unpriv_halt. right. eapply CIH; eauto. pfold. apply Ht2.
    pfold. apply H.
  - pclearbot. unpriv_halt. right. eapply CIH; eauto. pfold. auto.
  - unpriv_halt. contra_size.
  - unpriv_halt. right. pclearbot. eapply CIH with (t2 := Vis e1 k1); eauto.
    + pfold. auto.
    + apply H.
  - unpriv_halt. contra_size.
Qed.

Lemma eqit_secure_RR_imp : forall E b1 b2 R1 R2 (RR1 RR2 : R1 -> R2 -> Prop) Label priv l
                (t1 : itree E R1) (t2 : itree E R2),
    RR1 <2= RR2 ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t1 t2.
Proof.
  intros. generalize dependent t2. revert t1.
  pcofix CIH. intros t1 t2 Ht12. pfold. red.
  punfold Ht12. red in Ht12.
  hinduction Ht12 before r; intros; eauto;
  try (pclearbot; constructor; auto; right; eapply CIH; eauto; fail);
  try (pclearbot; unpriv_co; right; eapply CIH; eauto; apply H0; fail).
  pclearbot. constructor; auto. right. eapply CIH; eauto. apply H0.
  - pclearbot. unpriv_halt. right. eapply CIH; eauto. apply H0.
  - pclearbot. unpriv_halt. right. eapply CIH; eauto. apply H0.
Qed.

Lemma secret_halt_trans_3 :  forall E Label priv l b1 b2 (R1 R2 R3 A : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop)  t1 t2 (e : E A) k,
    (~ leq (priv A e) l ) ->
    empty A ->
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 (Vis e k) ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 (Vis e k).
Proof.
  intros. apply eqit_secure_sym in H1. apply eqit_secure_sym in H2.
  apply eqit_secure_sym. eapply secret_halt_trans_2 in H1; eauto.
  eapply eqit_secure_RR_imp; eauto.
  intros. inv PR. econstructor; eauto.
Qed.

Lemma eqit_secure_trans : forall E Label priv l b1 b2 (R1 R2 R3 : Type) (RR1 : R1 -> R2 -> Prop)
            (RR2 : R2 -> R3 -> Prop) (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3),
    eqit_secure Label priv RR1 b1 b2 l t1 t2 ->
    eqit_secure Label priv RR2 b1 b2 l t2 t3 ->
    eqit_secure Label priv (rcompose RR1 RR2) b1 b2 l t1 t3.
Proof.
  intros E Label priv l b1 b2 R1 R2 R3 RR1 RR2.
  pcofix CIH0. intros t1 t2 t3 Ht12 Ht23.
  punfold Ht12. red in Ht12. punfold Ht23. red in Ht23. pfold. red.
  hinduction Ht12 before r; intros; try inv CHECK; auto with itree.
  - remember (RetF r2) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  - pclearbot. genobs t4 ot4.
    assert ( (exists t5, ot4 = TauF t5) \/ (forall t5, ot4 <> TauF t5) ).
    { destruct ot4; eauto; right; intros; discriminate. }
    destruct H0 as [ [t5 Ht4] | Ht4].
    + subst. rewrite Ht4. rewrite Ht4 in Ht23. constructor.
      right. eapply CIH0; eauto. eapply eqit_secure_TauLR. pfold.
      auto.
    + destruct ot4; try (exfalso; eapply Ht4;  eauto; fail  ).
      * inv Ht23. inv CHECK. rewrite itree_eta' at 1.
        assert (eqit_secure Label priv (rcompose RR1 RR2) true b2 l (Tau t0) (Ret r0)  ).
        { pfold. red. cbn. rewrite itree_eta' at 1. eapply eqit_secure_trans_aux1; eauto.
          pfold. red. constructor; auto. pstep_reverse. }
        rewrite itree_eta'. pstep_reverse. eapply paco2_mon; eauto.
        intros; contradiction.
      * destruct (classic (leq (priv _ e) l ) ).
        -- inv Ht23; ddestruction; subst; try contradiction; try inv CHECK.
           constructor; auto. eapply eqit_secure_trans_aux2; eauto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. rewrite itree_eta' at 1.
              pstep_reverse.
              eapply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3 with (t2 := Tau t3); eauto.
              ** pfold. constructor. left. auto.
              ** pfold. auto.
           ++ unpriv_co. right. eapply CIH0; eauto.
              assert (eqit_secure Label priv RR2 b1 b2 l (Tau t3) (Vis e k)).
              pfold. auto. eapply eqit_secure_TauLVisR; eauto.
  - apply IHHt12; auto.
    remember (TauF t0) as y.
    hinduction Ht23 before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    + pclearbot. constructor; auto. pstep_reverse.
    + pclearbot. unpriv_ind. pstep_reverse.
    + pclearbot. punfold H.
  - pclearbot. remember (VisF e k2) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; ddestruction; subst;
    try contradiction; eauto with itree.
    + pclearbot. constructor; auto. intros. right. eapply CIH0; eauto; try apply H0.
      apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  - pclearbot. remember (TauF t0) as x.
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; auto.
    + pclearbot. unpriv_co. right. eapply CIH0; try apply H0.
      auto.
    + destruct ot2.
      * clear IHHt23. rewrite itree_eta'. unpriv_ind.
        remember (k1 a) as t. specialize (H a). setoid_rewrite <- Heqt in H.
        clear Heqt a k1. cbn. eapply eqit_secure_trans_aux1; eauto.
      * unpriv_co. right. eapply CIH0; try apply H.
        clear IHHt23. remember (TauF t) as y.
        pfold. red.
        hinduction Ht23 before r; intros; inv Heqy; try inv CHECK; eauto with itree.
        -- pclearbot. constructor; auto. pstep_reverse.
        -- pclearbot. unpriv_ind. pstep_reverse.
        -- pclearbot. punfold H.
      * destruct (classic (leq (priv _ e0) l ) ).
        -- rewrite itree_eta'. unpriv_ind. cbn.
           clear IHHt23. remember (k1 a) as t. specialize (H a). setoid_rewrite <- Heqt in H.
           clear Heqt a k1. eapply eqit_secure_trans_aux2; eauto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. unpriv_ind.
              pstep_reverse. apply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3; eauto. apply H.
              pfold. auto.
           ++ unpriv_co. right. eapply CIH0. apply H.
              clear IHHt23. pstep. red. remember (VisF e0 k) as y.
              hinduction Ht23 before r; intros; inv Heqy; try inv CHECK;
                ddestruction; subst; try contradiction; try contra_size; eauto with itree.
              ** pclearbot. constructor; auto. pstep_reverse.
              ** unpriv_ind. pclearbot. pstep_reverse.
              ** pclearbot. rewrite itree_eta' at 1. pstep_reverse.
    + constructor; auto. eapply IHHt23; eauto.
    + pclearbot. unpriv_co. right. eapply CIH0; try apply H0. apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + unpriv_halt. right. pclearbot. eapply CIH0; eauto. apply H0.
  - pclearbot.
    genobs_clear t3 ot3.
    assert (Hne : nonempty A); eauto. inv Hne.
    assert ( (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4) ).
    { destruct ot3; eauto; right; intros; discriminate. }
    destruct H0 as [ [t4 Ht3] | Ht3].
    + subst. constructor. right. eapply CIH0; try apply H.
      Unshelve. all: auto.
      eapply eqit_secure_TauRVisL; eauto. pfold. auto.
       (* should be fine but new lemma, also shelved goal *)
    +
      destruct ot3; try (exfalso; eapply Ht4;  eauto; fail  ).
      * inv Ht23; inv CHECK. ddestruction. subst. clear CIH0.
        constructor; auto. rewrite H4. eapply eqit_secure_trans_aux1; eauto.
        rewrite <- H4. apply H1. Unshelve. auto. (* shelved goal*)
      * constructor. right. eapply CIH0; try apply H.
        eapply eqit_secure_TauRVisL; eauto. pfold. auto.
        (* same goal as last admit *)
      * destruct (classic (leq (priv _ e0) l ) ).
        -- inv Ht23; try inv CHECK; ddestruction; subst; try contradiction.
           constructor; auto. rewrite H5. eapply eqit_secure_trans_aux2; eauto.
           rewrite <- H5. apply H2. Unshelve. all : auto.
        -- destruct (classic_empty X).
           ++ rewrite itree_eta'. rewrite itree_eta' at 1. pstep_reverse.
              eapply paco2_mon with (r := bot2); intros; try contradiction.
              eapply secret_halt_trans_3 with (t2 := Vis e k2); eauto.
              ** pfold. red. cbn. unpriv_co.
              ** pfold. auto.
           ++ unpriv_co. right. eapply CIH0; try apply H.
              Unshelve. all : auto.
              assert (eqit_secure Label priv RR2 b1 b2 l (Vis e k2) (Vis e0 k) ).
              pfold. auto. eapply eqit_secure_VisLR; eauto.
  - pclearbot. remember (VisF e2 k2) as x.
    (* maybe need to separate the inductive and coinductive progress cases? *)
    hinduction Ht23 before r; intros; inv Heqx; try inv CHECK; try contradiction;
    try contra_size;
    ddestruction; subst; auto.
    + constructor; auto. eapply IHHt23; eauto.
    + pclearbot. unpriv_co. right. eapply CIH0; try apply H0. apply H.
    + pclearbot. assert (Hne : nonempty B); eauto. inv Hne.
      unpriv_co. right. eapply CIH0; eauto; try eapply H0. apply H.
      Unshelve. auto.
    + pclearbot. assert (Hne : nonempty B0); eauto. inv Hne.
      unpriv_co. right. eapply CIH0; try apply H0. apply H.
      Unshelve. auto.
    + genobs t2 ot2. destruct ot2.
      * assert (Hne : nonempty B); eauto. inv Hne.
        rewrite itree_eta'. unpriv_ind. eapply eqit_secure_trans_aux1; eauto.
        Unshelve. auto.
      * assert (Hne : nonempty B); eauto. inv Hne.
        unpriv_co. right. eapply CIH0; try apply H1. Unshelve. all : auto.
        clear H0. specialize (H a). pfold. red. genobs (k2 a) ok2.
        clear Heqok2 H1 k2.
        remember (TauF t) as y.
        hinduction H before r; intros; inv Heqy; try inv CHECK; auto.
        -- constructor; auto. pclearbot. pstep_reverse.
        -- constructor; eauto.
        -- pclearbot. unpriv_ind. pstep_reverse.
        -- unpriv_ind. eapply H0; eauto.
        -- pclearbot. rewrite itree_eta' at 1. pstep_reverse.
      * inv SIZECHECK2.
        destruct (classic (leq (priv _ e) l ) ).
        -- rewrite itree_eta'. unpriv_ind.
           eapply eqit_secure_trans_aux2; eauto. Unshelve. all : auto.
        -- destruct (classic_empty X).
           ++ unpriv_halt. right. eapply CIH0; eauto. apply H1.
              pfold. apply H. Unshelve. auto.
           ++ unpriv_co. right. eapply CIH0; try apply H1.
              Unshelve. all : auto.
              clear H0. pstep. red. remember (VisF e k) as y.
              specialize (H a). clear Heqot2. genobs (k2 a) ok2.
              clear Heqok2.
              hinduction H before r; intros; inv Heqy; try inv CHECK;
                ddestruction; subst; try contradiction; try contra_size; eauto with itree.
              ** pclearbot. constructor; auto. pstep_reverse.
              ** unpriv_ind. pclearbot. pstep_reverse.
              ** pclearbot. rewrite itree_eta' at 1. pstep_reverse.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + pclearbot. inv SIZECHECK2. unpriv_halt. right. eapply CIH0; eauto. apply H0.
      apply H. Unshelve. auto.
  - remember (VisF e k2) as x. hinduction Ht23 before r; intros; inv Heqx; try inv CHECK;
    ddestruction; subst; try contradiction; try contra_size;  auto.
    + constructor; auto. eapply IHHt23; eauto.
    + constructor; auto. pclearbot. assert (Hne : nonempty A0); eauto. inv Hne. eapply H0; eauto.
      pstep_reverse. Unshelve. auto.
    + unpriv_ind. assert (Hne : nonempty A0); eauto. inv Hne. eapply H0; eauto.
      pclearbot. pstep_reverse. Unshelve. auto.
    + assert (Hne : nonempty A0). { eauto. } inv Hne. eauto. Unshelve.  auto.
    + unpriv_ind. eauto.
    + pclearbot. rewrite itree_eta'. pstep_reverse.
      apply paco2_mon with (r := bot2); intros; try contradiction.
      inv SIZECHECK0.
      eapply secret_halt_trans_3 with (t2 := k0 a); eauto.
      * pfold. apply H1.
      * apply H.
  - pclearbot.
    remember (TauF t0) as y.
    hinduction Ht23 before r; intros; inv Heqy; subst; eauto with itree; pclearbot.
    + unpriv_halt. right. eapply CIH0; eauto.
    + clear IHHt23. rewrite itree_eta'. rewrite itree_eta' at 1.
      pstep_reverse. apply paco2_mon with (r := bot2); intros; try contradiction.
      eapply secret_halt_trans_2; eauto. pfold. auto.
    + unpriv_halt. right. eapply CIH0; eauto. apply H.
    + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
    + unpriv_halt. contra_size.
  - pclearbot.
    inv Ht23; ddestruction; subst; try contra_size; try contradiction;
    try inv CHECK.
    + constructor. right. eapply CIH0; eauto. pfold. auto.
    + unpriv_co. right. eapply CIH0; eauto. rewrite H0 in H2.
      pfold. apply H2.
    + pclearbot. constructor. right. eapply CIH0; eauto.
    + pclearbot. destruct (classic_empty B).
      * unpriv_halt. right. eapply CIH0; eauto. pfold. red. cbn. unpriv_halt.
      * unpriv_co. right. eapply CIH0; eauto. apply H1.
    + pclearbot. unpriv_halt. right. eapply CIH0; eauto.
      pfold. red. cbn. unpriv_halt. contra_size.
 - pclearbot. rewrite itree_eta' at 1. pstep_reverse.
   apply paco2_mon with (r := bot2); intros; try contradiction.
   eapply secret_halt_trans_2 with (t2 := Vis e2 k2); eauto.
   + pfold. red. cbn. unpriv_halt.
   + pfold. auto.
 - pclearbot. destruct (classic_empty A).
   + inv Ht23; ddestruction; subst; try contradiction; try contra_size; try inv CHECK.
     * unpriv_halt. right. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- pfold. red. cbn. unpriv_halt. contra_size.
       -- pfold. auto.
     * unpriv_halt. right. rewrite H1 in H3. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- pfold. red. cbn. unpriv_halt. contra_size.
       -- pfold. apply H3.
     * unpriv_halt. pclearbot. right. eapply CIH0; eauto.
       pfold. red. cbn. unpriv_halt. contra_size.
     * unpriv_halt. pclearbot. right. eapply CIH0 with (t2 := Vis e2 k2); eauto.
       -- pfold. red. cbn. unpriv_halt. contra_size.
       -- apply H2.
     * unpriv_halt. contra_size.
   + destruct (observe t3).
     * inv Ht23; ddestruction; subst; try contra_size; try contradiction.
     * unpriv_co. right. eapply CIH0; eauto. apply H.
       inv Ht23; ddestruction; subst; try contra_size; try contradiction.
       pfold. auto. pclearbot. auto.
     * destruct (classic (leq (priv _ e) l ) ).
       { inv Ht23; ddestruction; subst; try contra_size; try contradiction. }
       destruct (classic_empty X).
       -- unpriv_halt. right. eapply CIH0; eauto. apply H. pfold. auto.
       -- unpriv_co. right. eapply CIH0; eauto. apply H.
          inv Ht23; ddestruction; subst; try contra_size; try contradiction.
          ++ pfold. apply H5.
          ++ pclearbot. apply H4.
Qed.


Lemma eqit_itree_eqit_secure : forall E Label priv l R1 R2 RR (t1 t1': itree E R1) (t2 : itree E R2),
    t1 ≅ t1' -> eqit_secure Label priv RR false false l t1 t2 ->
    eqit_secure Label priv RR false false l t1' t2.
Proof.
  intros E Label priv l R1 R2 RR. pcofix CIH.
  intros t1 t1' t2 Heq Hsec. pstep. red.
  punfold Heq. red in Heq. punfold Hsec. red in Hsec.
  inv Heq; try inv CHECK.
  - rewrite <- H0 in Hsec. rewrite itree_eta' at 1. pstep_reverse.
    eapply paco2_mon with (r := bot2); intros; try contradiction. pfold.
    red. cbn. remember (RetF r2) as x. clear H H0.
    hinduction Hsec before r; intros; inv Heqx; eauto with itree.
  - pclearbot. genobs t2 ot2.
    assert ( (exists t3, ot2 = TauF t3) \/ (forall t3, ot2 <> TauF t3) ).
    { destruct ot2; eauto; right; intros; discriminate. }
    destruct H1 as [ [t3 Ht2] | Ht2].
    + subst. rewrite Ht2. rewrite Ht2 in Hsec. constructor.
      right. eapply CIH; eauto. rewrite <- H0 in Hsec. inv Hsec; try inv CHECK. pclearbot. auto.
    + destruct ot2; try (exfalso; eapply Ht2;  eauto; fail  ).
      * rewrite <- H0 in Hsec. inv Hsec; try inv CHECK.
      * rewrite <- H0 in Hsec. inv Hsec; ddestruction; subst; try inv CHECK.
        -- pclearbot. unpriv_co. right. eapply CIH; eauto. apply H3.
        -- pclearbot. unpriv_halt. right. eapply CIH; eauto.
  - rewrite <- H0 in Hsec. inv Hsec; ddestruction; subst; try inv CHECK; try contradiction; try contra_size.
    + pclearbot. constructor; auto. right. eapply CIH; eauto with itree. apply H2.
    + pclearbot. unpriv_co. right. eapply CIH; eauto with itree. apply H2.
    + pclearbot. unpriv_co. right. eapply CIH; eauto with itree. apply H2.
    + pclearbot. unpriv_halt. right. eapply CIH; eauto. pfold. constructor. left. auto.
    + pclearbot. unpriv_halt. right. eapply CIH with (t1 := Vis e k1); try apply H2.
      pfold. constructor. left. auto.
    + pclearbot. unpriv_halt. right. eapply CIH; eauto with itree. apply H2.
Qed.

Lemma eqit_secure_eq_trans : forall E R b1 b2 Label priv l (t1 t2 t3 : itree E R),
    eqit_secure Label priv eq b1 b2 l t1 t2 ->
    eqit_secure Label priv eq b1 b2 l t2 t3 ->
    eqit_secure Label priv eq b1 b2 l t1 t3.
Proof.
  intros. apply eqit_secure_RR_imp with (RR1 := rcompose eq eq).
  { intros. inv PR. auto. }
  eapply eqit_secure_trans; eauto.
Qed.

Lemma eqit_secure_anything : forall E R1 b Label priv l
                      (t1 : itree E R1) t2,
    eqit_secure Label priv eq b b l t1 t2 ->
    eqit_secure Label priv eq b b l t1 t1.
Proof.
  intros.
  eapply eqit_secure_eq_trans; eauto.
  apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto.
Qed.


Global Instance proper_eqit_secure_eqit {E} {R1 R2 : Type} {b} {RR : R1 -> R2 -> Prop} {Label priv l} :
       Proper (eqit eq b b ==> eqit eq b b ==> iff) (@eqit_secure E R1 R2 Label priv RR b b l).
Proof.
  repeat intro. destruct b; split; intros.
  - eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - assert (x ≈ y); auto. assert (x0 ≈ y0); auto.
    symmetry in H2.
    eapply eutt_secure_eqit_secure; eauto.
    symmetry in H3. apply eqit_secure_sym.
    eapply eutt_secure_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
  - assert (x ≅ y); auto. assert (x0 ≅ y0); auto.
    symmetry in H2. symmetry in H3.
    eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. eapply eqit_itree_eqit_secure; eauto.
    apply eqit_secure_sym. auto.
Qed.

Global Instance proper_eqit_secure_eqit_secure
       {E} {b} {R1 R2 : Type} {RR : R1 -> R2 -> Prop} {Label priv l} :
  Proper (eqit_secure Label priv eq b b l ==> eqit_secure Label priv eq b b l ==> iff)
         (@eqit_secure E R1 R2 Label priv RR b b l).
Proof.
  repeat intro; split; intros.
  - eapply eqit_secure_RR_imp with (RR1 := rcompose RR eq); eauto.
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
    apply eqit_secure_sym.
    eapply eqit_secure_RR_imp with (RR1 := rcompose (flip RR) eq); eauto.
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto. apply eqit_secure_sym. auto.
  - assert (eqit_secure Label priv eq b b l y0 x0).
    { apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto. }
    eapply eqit_secure_RR_imp with (RR1 := rcompose RR eq).
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
    assert (eqit_secure Label priv eq b b l y x).
    { apply eqit_secure_sym. eapply eqit_secure_RR_imp; eauto. }
    eapply eqit_secure_RR_imp with (RR1 := rcompose eq RR).
    { intros. inv PR. auto. }
    eapply eqit_secure_trans; eauto.
Qed.
