From Stdlib Require Import
     Program
     Setoid
     Morphisms
     Relations.

From ITree Require Import
  Basics.Basics
  Monad
  Basics.Utils
  Basics.HeterogeneousRelations
  Eq.Eqit
  Eq.EqAxiom
  Core.ITreeDefinition.

From ITreeSpec Require Import
  Padded
  ITreeSpecDefinition
  MRecSpec
  Relations.

From Paco Require Import paco.

Local Open Scope itree_scope.

Ltac inj_existT := repeat match goal with
                          | H:existT _ _ _ = _ |- _ => apply inj_pairT2 in H
                          end.

#[global] Hint Resolve monotone_refines_ : paco.

#[global] Hint Constructors refinesF : itree_spec.

Section quant_elim1.
Context (E1 E2 : Type -> Type).
Context (RPre : prerel E1 E2) (RPost : postrel E1 E2).
Context (R1 R2 : Type) (RR : R1 -> R2 -> Prop).
Context (A : Type).
Lemma refines_Vis_forallR b1 b2 : forall t k,
             refines' RPre RPost RR b1 b2 t (Vis (Spec_forall A) k) ->
         forall a, refines' RPre RPost RR b1 b2 t (k a).
Proof.
 intros t k Href a. punfold Href. red in Href. cbn in *. pstep. red.
  remember (observe t) as ot. clear Heqot.
  remember (VisF (Spec_forall A) k) as x.
  hinduction Href before E1; intros; inv Heqx; inj_existT; subst; pclearbot; eauto with itree_spec.
Qed.

Lemma refines_existsL b1 b2 : forall t k,
    refines' RPre RPost RR b1 b2 (Vis (Spec_exists A) k) t ->
    forall a, refines' RPre RPost RR b1 b2 (k a) t.
Proof.
  intros t k Href a. punfold Href. red in Href. cbn in *. pstep. red.
  remember (observe t) as ot. clear Heqot.
  remember (VisF (Spec_exists A) k) as x.
  hinduction Href before E1; intros; inv Heqx; inj_existT; subst; pclearbot; eauto with itree_spec.
Qed.
End quant_elim1.

Section refinesF_inv.
Context {E1 E2 : Type -> Type} {R1 R2 : Type} (A : Type).
Context (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop).

(* A version of refinesF specialized to a forall on the left *)
Inductive forallRefinesF b1 b2 vclo (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          (kphi1 : A -> itree_spec E1 R1) : itree_spec' E2 R2 -> Prop :=
  | forallRefines_forallR B (kphi2 : B -> itree_spec E2 R2) :
    (forall b, forallRefinesF b1 b2 vclo F kphi1 (observe (kphi2 b))) ->
    forallRefinesF b1 b2 vclo F kphi1 (VisF (Spec_forall B) kphi2)
  | forallRefines_forallL phi (a : A) :
    refinesF RPre RPost RR b1 b2 vclo F (observe (kphi1 a)) phi ->
    forallRefinesF b1 b2 vclo F kphi1 phi
  | forallRefines_existsR B kphi2 (b : B) :
    (forallRefinesF b1 b2 vclo F kphi1 (observe (kphi2 b))) ->
    forallRefinesF b1 b2 vclo F kphi1 (VisF (Spec_exists B) kphi2)
| forallRefines_TauR phi2 :
    is_true b2 ->
    forallRefinesF b1 b2 vclo F kphi1 (observe phi2) ->
    forallRefinesF b1 b2 vclo F kphi1 (TauF phi2).

(* A version of refinesF specialized to an exists on the left *)
Inductive existsRefinesF b1 b2 vclo (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          (kphi2 : A -> itree_spec E2 R2) : itree_spec' E1 R1 -> Prop :=
  | existsRefines_existsR phi a :
    refinesF RPre RPost RR b1 b2 vclo F phi (observe (kphi2 a)) ->
    existsRefinesF b1 b2 vclo F kphi2 phi
  | existsRefines_forallL B (kphi1 : B -> itree_spec E1 R1) (b : B):
    existsRefinesF b1 b2 vclo F kphi2 (observe (kphi1 b)) ->
    existsRefinesF b1 b2 vclo F kphi2 (VisF (@Spec_forall E1 B) kphi1)
  | existsRefines_existsL B (kphi1 : B -> itree_spec E1 R1) :
    (forall b, existsRefinesF b1 b2 vclo F kphi2 (observe (kphi1 b))) ->
    existsRefinesF b1 b2 vclo F kphi2 (VisF (@Spec_exists E1 B) kphi1)
  | existsRefines_TauL phi1 :
    is_true b1 ->
    existsRefinesF b1 b2 vclo F kphi2 (observe phi1) ->
    existsRefinesF b1 b2 vclo F kphi2 (TauF phi1).
End refinesF_inv.

Lemma refinesF_Vis_existsR
  {E1 E2 R1 R2} (A : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
  : forall b1 b2 vclo F (t : itree_spec' E1 R1) (k : A -> itree_spec E2 R2),
    is_true b1 ->
    refinesF RPre RPost RR b1 b2 vclo F t (VisF (@Spec_exists E2 A) k) ->
    existsRefinesF A RPre RPost RR b1 b2 vclo F k t.
Proof.
  intros. remember (VisF (Spec_exists A) k) as t1.
  induction H0; try discriminate.
  - constructor; auto.
  - inversion Heqt1. subst. inj_existT. subst. econstructor.
    eauto.
  - eapply existsRefines_forallL. eauto.
  - cbn.
    constructor. eauto.
Qed.

Lemma refinesF_Vis_forallL {E1 E2 R1 R2} (A : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
  : forall b1 b2 vclo F (t : itree_spec' E2 R2) (k : A -> itree_spec E1 R1),
    is_true b2 ->
    refinesF RPre RPost RR b1 b2 vclo F (VisF (@Spec_forall E1 A) k) t ->
    forallRefinesF A RPre RPost RR b1 b2 vclo F k t.
Proof.
  intros. remember (VisF (Spec_forall A) k) as t1.
  induction H0; try discriminate.
  - constructor; auto.
  - constructor.
    intros a.
    auto.
  - eapply forallRefines_existsR. eauto.
  - inversion Heqt1. subst. inj_existT. subst.
    econstructor. eauto.
Qed.

Section refines_tau_inv.
Context (E1 E2 : Type -> Type).
Context (RPre : prerel E1 E2) (RPost : postrel E1 E2).
Context (R1 R2 : Type) (RR : R1 -> R2 -> Prop).

Lemma refines_TauL_inv : forall b1 b2 (CHECK : is_true b2) phi1 phi2,
    refines' RPre RPost RR b1 b2 (Tau phi1) phi2 -> refines' RPre RPost RR b1 b2 phi1 phi2.
Proof.
  intros b1 b2 CHECK.
  pcofix CIH. intros. pstep. red. punfold H0. red in H0.
  cbn in *. remember (TauF phi1) as x.
  hinduction H0 before RPre; intros; inv Heqx; pclearbot; eauto with itree_spec.
  constructor; eauto.
  pstep_reverse.
  eapply paco2_mon; try apply H. intros. contradiction.
  eapply monotone_refinesF.
  4: {
    apply H0.
  }
  all: eauto with paco.
  intros; auto.
  pclearbot.
  left.
  eapply paco2_mon; try apply PR. intros. contradiction.
Qed.

Lemma refines_TauR_inv : forall (b1 b2 : bool) (CHECK : is_true b1) phi1 phi2,
    refines' RPre RPost RR b1 b2 phi1 (Tau phi2) -> refines' RPre RPost RR b1 b2 phi1 phi2.
Proof.
  intros. pstep. red. punfold H. red in H.
  cbn in *. remember (TauF phi2) as x.
  hinduction H before RPre; intros; inv Heqx; pclearbot; eauto with itree_spec.
  constructor; auto; try constructor.
  pstep_reverse.
Qed.

Lemma refinesF_TauR_inv : forall b1 b2 (CHECK : is_true b1) phi1 phi2,
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (observe phi1) (TauF phi2) ->
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (observe phi1) (observe phi2).
Proof.
  intros. pstep_reverse. apply refines_TauR_inv; auto. pstep. auto.
Qed.

Lemma refinesF_TauL_inv : forall b1 b2 (CHECK : is_true b2) phi1 phi2,
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (TauF phi1) (observe phi2) ->
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (observe phi1) (observe phi2).
Proof.
  intros. pstep_reverse. apply refines_TauL_inv; auto. pstep. auto.
Qed.

Lemma refinesF_Vis_existsR_Tau_inv {A} b1 b2 (CHECK: is_true b2) : forall t (k : A -> _),
    existsRefinesF A RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) k (TauF t) ->
    existsRefinesF A RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) k (observe t).
Proof.
  intros. inv H; auto.
  econstructor. eapply refinesF_TauL_inv; auto. eauto.
Qed.
End refines_tau_inv.

Create HintDb solve_padded.
#[global] Hint Constructors refinesF : solve_padded.
#[global] Hint Resolve padded_monotone_ : paco.
Section paddedF_hints.
Context (E : Type -> Type).


Lemma paddedF_TauF_hint:
  forall (R : Type) (phi1 : itree_spec E R), paddedF (upaco1 padded_ bot1) (TauF phi1) -> padded phi1.
Proof.
  intros R phi1. intros. inv H. pclearbot. auto.
Qed.

Lemma paddedF_TauF_hint':
  forall (R1 : Type) (phi1 : itree_spec E R1), paddedF (upaco1 padded_ bot1) (TauF phi1) -> paddedF (upaco1 padded_ bot1) (observe phi1).
Proof.
  intros. pstep_reverse. apply paddedF_TauF_hint. auto.
Qed.

Lemma paddedF_VisF_hint:
  forall (R1 A : Type) (kphi : A -> itree E R1)
     (e : E A),
    paddedF (upaco1 padded_ bot1) (VisF e kphi) -> forall a, padded (kphi a).
Proof.
  intros. pstep. red.
  inv H. inj_existT. subst. constructor. eauto.
Qed.

Lemma paddedF_VisF_hint':
  forall (R1 A : Type) (kphi : A -> itree E R1)
     (e : E A) ,
    paddedF (upaco1 padded_ bot1) (VisF e kphi) -> forall a, paddedF (upaco1 padded_ bot1) (observe (kphi a)).
Proof.
  pstep_reverse. apply paddedF_VisF_hint.
Qed.

Lemma padded_Tau_hint:
  forall {A} R3 (e : E A) (k1 : A -> itree_spec E R3) (b : A), (forall a , paco1 padded_ bot1 (k1 a)) -> padded (Tau (k1 b)).
Proof.
  intros. pstep. constructor. left. auto.
Qed.

Lemma paddedF_Tau_inv_hint:
  forall (R1 : Type) (phi1 : itree_spec E R1),
    paddedF (upaco1 padded_ bot1) (observe phi1) -> paddedF (upaco1 padded_ bot1) (TauF phi1).
Proof.
  intros. constructor. left. pstep. auto.
Qed.

Lemma paddedF_Tau_Vis_hint:
  forall {A} (R2: Type) (e : E A) (a : A) (kphi0 : A -> itree E R2) (phi2 : itree E R2),
    paddedF (upaco1 padded_ bot1) (TauF phi2) -> VisF e kphi0 = observe phi2 -> paddedF (upaco1 padded_ bot1) (TauF (kphi0 a)).
Proof.
  intros. inv H. pclearbot. punfold H2. red in H2.
  rewrite <- H0 in H2. inv H2. inj_existT. subst.
  constructor. left. pstep. constructor. auto.
Qed.

Lemma paddedF_TauF_TauF_hint:
  forall (R1 : Type) (phi phi1 : itree_spec E R1),
    paddedF (upaco1 padded_ bot1) (TauF phi1) -> TauF phi = observe phi1 -> paddedF (upaco1 padded_ bot1) (TauF phi).
Proof.
  intros. inv H. constructor. left. pclearbot. punfold H2. red in H2.
  rewrite <- H0 in H2. inv H2. pclearbot. auto.
Qed.

Lemma paddedF_VisF_TauF_hint:
  forall {A} (E1 : Type -> Type) (R1 : Type) (e : E1 A)
    (k2 : A -> itree E1 R1) (a : A),
    paddedF (upaco1 padded_ bot1) (VisF e k2) -> paddedF (upaco1 padded_ bot1) (TauF (k2 a)).
Proof.
  intros E1 Henc1 R1 A k2 a H1.
  inversion H1. subst. inj_existT. subst. constructor.
  left. pstep. constructor. auto.
Qed.

End paddedF_hints.

Lemma rcompose_hint A B C (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) a b c :
  R1 a b -> R2 b c -> rcompose R1 R2 a c.
Proof.
  intros. exists b. auto.
  auto.
Qed.

#[local] Hint Resolve paddedF_TauF_hint : solve_padded.
#[local] Hint Resolve paddedF_TauF_hint' : solve_padded.
#[local] Hint Resolve paddedF_VisF_hint : solve_padded.
#[local] Hint Resolve paddedF_VisF_hint' : solve_padded.
(* hopefully this is *)
#[local] Hint Resolve rcompose_hint : solve_padded.
#[local] Hint Resolve padded_Tau_hint : solve_padded.
#[local] Hint Unfold padded : solve_padded.
#[local] Hint Unfold padded_ : solve_padded.
#[local] Hint Resolve paddedF_Tau_inv_hint : solve_padded.
#[local] Hint Resolve paddedF_Tau_Vis_hint : solve_padded.
#[local] Hint Resolve  paddedF_TauF_TauF_hint : solve_padded.
#[local] Hint Resolve paddedF_VisF_TauF_hint : solve_padded.

Section refines_tau_inv.
  Context (E1 E2 : Type -> Type).
  Context (RPre : prerel E1 E2) (RPost : postrel E1 E2).
  Context (R1 R2 : Type) (RR : R1 -> R2 -> Prop).

  Lemma refines_TauTau_inv : forall b1 b2 phi1 phi2,
      refines' RPre RPost RR b1 b2 (Tau phi1) (Tau phi2) -> refines' RPre RPost RR b1 b2 phi1 phi2.
  Proof with eauto with itree.
    intros * H. punfold H. red in H. simpl in *.
    remember (TauF phi1) as tt1. remember (TauF phi2) as tt2.
    hinduction H before b2; intros; try discriminate; try inv CHECK.
    - inv Heqtt1. inv Heqtt2. pclearbot. eauto.
    - inv Heqtt1. inv H.
      + pclearbot. punfold H2. pstep. red. simpobs...
        constructor; auto.
      + pstep. red.
        simpobs. econstructor; eauto. pstep_reverse. apply IHrefinesF; eauto with solve_padded.
      + pstep; red; auto.
      + pstep; red.
        rewrite <- H0.
        econstructor.
        eapply refinesF_TauR_inv; eauto.
      + pstep; red.
        rewrite <- H0.
        econstructor.
        intros a.
        eapply refinesF_TauR_inv; eauto.
    - inv Heqtt2. inv H;
        try solve [pstep; red; eauto].
      + pclearbot. punfold H2. pstep. red. simpobs...
        constructor; auto.
      + pstep; red.
        rewrite <- H0.
        constructor; auto.
        eapply refinesF_TauL_inv; eauto.
      + pstep; red.
        rewrite <- H0.
        econstructor.
        intros a.
        eapply refinesF_TauL_inv; eauto.
      + pstep; red.
        rewrite <- H0.
        econstructor; eauto.
        eapply refinesF_TauL_inv; eauto.
  Qed.

  Lemma refinesF_TauTau_inv : forall b1 b2 phi1 phi2,
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (TauF phi1) (TauF phi2) ->
      refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) (observe phi1) (observe phi2).
  Proof.
    intros. pstep_reverse. apply refines_TauTau_inv; eauto. pstep. eauto.
  Qed.

End refines_tau_inv.

Lemma refines_eutt_padded_l_tau_aux:
  forall (E1 E2 : Type -> Type) (R2 : Type)
    (R1 : Type) (RPre : prerel E1 E2)
    (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
    b1 b2
    (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
    (m1 m2 : itree_spec E1 R1) (t3 : itree_spec E2 R2),
    is_true b1 ->
    is_true b2 ->
    (forall (t1 t2 : itree_spec E1 R1) (t4 : itree_spec E2 R2),
        padded t2 ->
        padded t4 -> t1 ≈ t2 -> refines' RPre RPost RR b1 b2 t1 t4 -> r t2 t4) ->
    paco2 (eqit_ eq true true id) bot2 m1 m2 ->
    paddedF (upaco1 padded_ bot1) (TauF m2) ->
    paddedF (upaco1 padded_ bot1) (observe t3) ->
    refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2)
             (TauF m1) (observe t3) ->
    refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) r)
             (TauF m2) (observe t3).
Proof.
  intros E1 E2 R2 R1 RPre RPost RR b1 b2 r m1 m2 t3 B1 B2 CIH REL Hpad2 Hpad3 Href.
  remember (observe t3) as ot3. clear Heqot3 t3.
  assert (HDEC : (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4)).
  { destruct ot3; eauto; right; repeat intro; discriminate. }
  destruct HDEC as [ [t4 Ht4] |  Ht3]; subst.
  {
    constructor. right. eapply CIH; eauto. inv Hpad2. pclearbot. auto.
    inv Hpad3. pclearbot. auto.
    apply refines_TauTau_inv; pstep; auto.
  }
  destruct ot3; try (exfalso; eapply Ht3; eauto; fail); try destruct e.
  + inv Href. constructor; auto. punfold REL. red in REL.
    remember (RetF r0) as y. hinduction H0 before r; intros; inv Heqy; subst; eauto with itree_spec.
    * remember (RetF r1) as x. hinduction REL before r; intros; inv Heqx; subst; eauto with itree_spec.
    * eapply IHrefinesF; eauto. pstep_reverse.
      (* need to move tau_eutt and tau_euttge into this branch, *)
      setoid_rewrite <- (tau_eutt t1). pstep. auto.
    * inv Hpad2. pclearbot. punfold H1. red in H1.
      remember (VisF (Spec_forall A) k) as x. hinduction REL before r; intros; inv Heqx; inj_existT; subst;
        eauto with solve_padded.
      econstructor. eapply IHrefinesF; eauto. pclearbot. pstep_reverse.
      eauto with solve_padded.
    * inv Hpad2. pclearbot. punfold H2. red in H2.
      remember (VisF (Spec_exists A) k) as x. hinduction REL before r; intros; inv Heqx; inj_existT; subst;
        eauto with solve_padded.
      econstructor. intros. pclearbot. eapply H0; eauto with solve_padded. pstep_reverse.

      (* left off here *)
  + inv Href. constructor; auto.
    inv Hpad2. pclearbot. punfold H1. red in H1. punfold REL. red in REL.
    inv Hpad3. inj_existT. subst.
    remember (VisF (Spec_vis e) (fun a : _  => Tau (k1 a))) as y.
    assert (Hy : paddedF (upaco1 padded_ bot1) y).
    { subst. constructor. auto. }
    hinduction H0 before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded.
    (* * eapply IHrefinesF; eauto. pstep_reverse. rewrite <- (tau_eutt phi). pstep. auto. *)
    * remember (VisF (Spec_vis e1) k1) as y.
      (*
       * dholland 20250131: with coq-paco 4.2.3 this pclearbot changes
       * the upaco2 in H0 to paco2; with coq-paco 4.2.2 and earlier
       * it's missed.
       *)
      pclearbot.
      (* shouldn't I know that k2 is padded here? *)
      hinduction REL before r; intros; inv Heqy; inj_existT; subst.
      -- pclearbot. constructor; auto. intros. eapply H0 in H3.
         (* dholland 20250131: consequently this is no longer needed *)
         (*destruct H3; try contradiction.*)
         right. pclearbot. inv Hy. inj_existT. subst. eapply CIH; eauto with solve_padded; try apply REL.
      -- constructor; auto. eapply IHREL; eauto.
         inv H1. pclearbot. pstep_reverse.
    * eapply IHrefinesF; eauto with solve_padded. pstep_reverse. rewrite <- (tau_eutt t1).
      pstep. auto.
    * remember (VisF (Spec_forall A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
      econstructor. pclearbot. eapply IHrefinesF; eauto with solve_padded. pstep_reverse.
    * remember (VisF (Spec_exists A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
      econstructor. intros. eapply H0; eauto. pclearbot. pstep_reverse.
      inv H1; inj_existT; subst. constructor. auto.
  + inv Hpad3. inj_existT. subst. apply refinesF_forallR. intros. constructor.
    right. eapply CIH; pclearbot; eauto with solve_padded.
    inv Hpad2. pclearbot.
    inv Href.
    { eapply refines_TauR_inv; auto.
      set (fun a => Tau (k1 a)) as k2'. assert (Tau (k1 a) = k2' a). auto.
      rewrite H.
      apply refines_Vis_forallR. unfold k2'. apply refines_TauL_inv; auto.
      pstep; red; cbn; eauto.
      apply refinesF_TauL; auto.
    }

    inj_existT; subst.
    specialize (H3 a).
    apply refines_TauTau_inv.
    pstep; red; auto.
  + inv Hpad3. inj_existT. subst.
    assert ( refinesF RPre RPost RR b1 b2 id
                      (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2)
                      (observe m1)
                      (VisF (Spec_exists A) (fun a => Tau (k1 a))) ).
    { rewrite itree_eta'. pstep_reverse. apply refines_TauL_inv; auto. pstep. auto. }
    clear Href. rename H into Href. pclearbot.
    eapply refinesF_Vis_existsR in Href; auto. punfold REL. red in REL.
    hinduction Href before r; intros; eauto.
    * eapply refinesF_existsR. constructor. right.
      eapply CIH; eauto with solve_padded. pstep. Unshelve. 3 : exact a.
      3: {
        apply go.
        apply phi.
      }
      red. auto. red. cbn in H.
      apply refines_TauR_inv; auto.
      pstep; auto.
    * inv Hpad2. pclearbot. punfold H1. red in H1.
      remember (VisF (Spec_forall B) kphi1) as x. remember (observe m2) as om2.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      -- inv H1. inj_existT. subst. constructor; auto. rewrite <- Heqom2.
         eapply refinesF_forallL. Unshelve. 2 : exact b. eapply IHHref; eauto.
         pclearbot. pstep_reverse. rewrite <- (tau_eutt (k1 b)). auto.
         constructor. auto.
      -- constructor. auto. rewrite <- Heqom2. inv H1. pclearbot. punfold H2.
    * inv Hpad2. pclearbot. punfold H3. red in H3.
      remember (VisF (Spec_exists B) kphi1) as x. remember (observe m2) as om2.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; auto.
      -- inv H3. inj_existT. subst. constructor. auto. intros.
         rewrite <- Heqom2. constructor. intros. eapply H0; eauto. Unshelve. all : auto.
         pclearbot. pstep_reverse.  setoid_rewrite tau_eutt in REL. auto.
         constructor. auto.
      -- constructor. auto. rewrite <- Heqom2.
         eapply IHREL; eauto. inv H3. pclearbot. pstep_reverse.
    * eapply IHHref; eauto. pstep_reverse. rewrite <- (tau_eutt phi1). pstep. auto.
Qed.

(* Lemma refines'_eutt_padded_l_tau_aux: *)
(*   forall (E1 E2 : Type -> Type) (R2 : Type) *)
(*     (R1 : Type) (RPre : prerel E1 E2) *)
(*     (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) *)
(*     b1 b2 *)
(*     (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop) *)
(*     (m1 m2 : itree_spec E1 R1) (t3 : itree_spec E2 R2), *)
(*     (forall (t1 t2 : itree_spec E1 R1) (t4 : itree_spec E2 R2), *)
(*         padded t2 -> *)
(*         padded t4 -> eqit eq b1 b1 t1 t2 -> refines' RPre RPost RR b1 b2 t1 t4 -> r t2 t4) -> *)
(*     paco2 (eqit_ eq b1 b1 id) bot2 m1 m2 -> *)
(*     paddedF (upaco1 padded_ bot1) (TauF m2) -> *)
(*     paddedF (upaco1 padded_ bot1) (observe t3) -> *)
(*     refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) *)
(*              (TauF m1) (observe t3) -> *)
(*     refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) r) *)
(*              (TauF m2) (observe t3). *)
(* Proof. *)
(*   intros E1 E2 R2 R1 RPre RPost RR b1 b2 r m1 m2 t3 CIH REL Hpad2 Hpad3 Href. *)
(*   remember (observe t3) as ot3. clear Heqot3 t3. *)
(*   assert (HDEC : (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4)). *)
(*   { destruct ot3; eauto; right; repeat intro; discriminate. } *)
(*   destruct HDEC as [ [t4 Ht4] |  Ht3]; subst. *)
(*   { *)
(*     constructor. right. eapply CIH; eauto. inv Hpad2. pclearbot. auto. *)
(*     inv Hpad3. pclearbot. auto. *)
(*     apply refines_TauTau_inv; pstep; auto. *)
(*   } *)
(*   destruct ot3; try (exfalso; eapply Ht3; eauto; fail); try destruct e. *)
(*   + inv Href. constructor; auto. punfold REL. red in REL. *)
(*     remember (RetF r0) as y. hinduction H0 before r; intros; inv Heqy; subst; eauto with itree_spec. *)
(*     * remember (RetF r1) as x. hinduction REL before r; intros; inv Heqx; subst; eauto with itree_spec. *)
(*     * eapply IHrefinesF; eauto. pstep_reverse. *)
(*       inv CHECK; inv CHECK0. *)
(*       rewrite <- (tau_euttge t1). *)
(*       pstep. auto. *)
(*     * inv Hpad2. pclearbot. punfold H1. red in H1. *)
(*       remember (VisF (Spec_forall A) k) as x. hinduction REL before r; intros; inv Heqx; inj_existT; subst; *)
(*         eauto with solve_padded. *)
(*       econstructor. eapply IHrefinesF; eauto. pclearbot. pstep_reverse. *)
(*       eauto with solve_padded. *)
(*     * inv Hpad2. pclearbot. punfold H2. red in H2. *)
(*       remember (VisF (Spec_exists A) k) as x. hinduction REL before r; intros; inv Heqx; inj_existT; subst; *)
(*         eauto with solve_padded. *)
(*       econstructor. intros. pclearbot. eapply H0; eauto with solve_padded. pstep_reverse. *)

(*       (* left off here *) *)
(*   + inv Href. constructor; auto. *)
(*     inv Hpad2. pclearbot. punfold H1. red in H1. punfold REL. red in REL. *)
(*     inv Hpad3. inj_existT. subst. *)
(*     remember (VisF (Spec_vis e) (fun a : _  => Tau (k1 a))) as y. *)
(*     assert (Hy : paddedF (upaco1 padded_ bot1) y). *)
(*     { subst. constructor. auto. } *)
(*     hinduction H0 before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded. *)
(*     (* * eapply IHrefinesF; eauto. pstep_reverse. rewrite <- (tau_eutt phi). pstep. auto. *) *)
(*     * remember (VisF (Spec_vis e1) k1) as y. *)
(*       (* *)
(*        * dholland 20250131: with coq-paco 4.2.3 this pclearbot changes *)
(*        * the upaco2 in H0 to paco2; with coq-paco 4.2.2 and earlier *)
(*        * it's missed. *)
(*        *) *)
(*       pclearbot. *)
(*       (* shouldn't I know that k2 is padded here? *) *)
(*       hinduction REL before r; intros; inv Heqy; inj_existT; subst. *)
(*       -- pclearbot. constructor; auto. intros. eapply H0 in H3. *)
(*          (* dholland 20250131: consequently this is no longer needed *) *)
(*          (*destruct H3; try contradiction.*) *)
(*          right. pclearbot. inv Hy. inj_existT. subst. eapply CIH; eauto with solve_padded; try apply REL. *)
(*       -- constructor; auto. eapply IHREL; eauto. *)
(*          inv H1. pclearbot. pstep_reverse. *)
(*     * eapply IHrefinesF; eauto with solve_padded. pstep_reverse. *)
(*       inv CHECK. *)
(*       rewrite <- (tau_euttge t1). *)
(*       pstep. auto. *)
(*     * remember (VisF (Spec_forall A) k) as x. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded. *)
(*       econstructor. pclearbot. eapply IHrefinesF; eauto with solve_padded. pstep_reverse. *)
(*     * remember (VisF (Spec_exists A) k) as x. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded. *)
(*       econstructor. intros. eapply H0; eauto. pclearbot. pstep_reverse. *)
(*       inv H1; inj_existT; subst. constructor. auto. *)
(*   + inv Hpad3. inj_existT. subst. apply refinesF_forallR. intros. constructor. *)
(*     right. eapply CIH; pclearbot; eauto with solve_padded. *)
(*     inv Hpad2. pclearbot. *)
(*     inv Href. *)
(*     { eapply refines_TauR_inv; auto. *)
(*       set (fun a => Tau (k1 a)) as k2'. assert (Tau (k1 a) = k2' a). auto. *)
(*       rewrite H. *)
(*       inv CHECK. *)
(*       apply refines_Vis_forallR. unfold k2'. *)
(*       pstep; red; cbn; eauto. *)
(*     } *)

(*     inj_existT; subst. *)
(*     specialize (H3 a). *)
(*     apply refines_TauTau_inv. *)
(*     pstep; red; auto. *)
(*   + inv Hpad3. inj_existT. subst. *)
(*     pclearbot. *)
(*     punfold REL. red in REL. *)
(*     (* Href is close, but it has m1 instead of m2 and bot2 instead of r *) *)
(*     eapply refinesF_Vis_existsR_Tau_inv. *)
(*     rewrite (itree_eta_ m2). *)
(*     rewrite (itree_eta_ m1) in Href. *)
(*     dependent induction REL; intros; *)
(*       try rewrite <- x; try rewrite <- x0 in Href. *)
(*   - inv Href; eauto. *)
    
    
(*     apply Href. *)
    
(*     remember (TauF m1) as x. *)
(*     remember (VisF (Spec_exists A) (fun a : A => Tau (k1 a))) as y. *)
    

    
(*     induction Href; intros; *)
(*       try solve [inversion Heqx; inversion Heqy; subst; inj_existT; subst; eauto with solve_padded]. *)
(*     { subst. *)
(*       apply IHHref; eauto. *)

(*     } *)
(*     2: { *)
(*       subst. *)
(*       cbn in *. *)
(*       clear IHHref. *)
(*       apply refinesF_existsR with (a:=a). *)
(*       rewrite (itree_eta_ m2). *)
(*       rewrite (itree_eta_ m1) in Href. *)
(*       inv Href; pclearbot; eauto. *)
(*       inv REL; *)
(*         try rewrite <- H1 in *. *)
      
(*       eapply IHHref; eauto. *)
(*       admit. *)
      
(*       apply Href. *)
(*       apply *)
      
(*       induction REL; intros. *)
(*       admit. *)
(*       admit. *)
(*     } *)
(*     * eapply refinesF_existsR. constructor. right. *)
(*       eapply CIH; eauto with solve_padded. pstep. Unshelve. 3 : exact a. *)
(*       3: { *)
(*         apply go. *)
(*         apply phi. *)
(*       } *)
(*       red. auto. red. cbn in H. *)
(*       apply refines_TauR_inv; auto. *)
(*       admit. *)
(*       pstep; auto. *)
(*     * inv Hpad2. pclearbot. punfold H1. red in H1. *)
(*       remember (VisF (Spec_forall B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst. *)
(*       -- inv H1. inj_existT. subst. constructor; auto. rewrite <- Heqom2. *)
(*          eapply refinesF_forallL. Unshelve. 2 : exact b. eapply IHHref; eauto. *)
(*          pclearbot. pstep_reverse. rewrite <- (tau_eutt (k1 b)). auto. *)
(*          constructor. auto. *)
(*       -- constructor. auto. rewrite <- Heqom2. inv H1. pclearbot. punfold H2. *)
(*     * inv Hpad2. pclearbot. punfold H3. red in H3. *)
(*       remember (VisF (Spec_exists B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; auto. *)
(*       -- inv H3. inj_existT. subst. constructor. auto. intros. *)
(*          rewrite <- Heqom2. constructor. intros. eapply H0; eauto. Unshelve. all : auto. *)
(*          pclearbot. pstep_reverse.  setoid_rewrite tau_eutt in REL. auto. *)
(*          constructor. auto. *)
(*       -- constructor. auto. rewrite <- Heqom2. *)
(*          eapply IHREL; eauto. inv H3. pclearbot. pstep_reverse. *)
(*     * eapply IHHref; eauto. pstep_reverse. rewrite <- (tau_eutt phi1). pstep. auto. *)



(*   + inv Hpad3. inj_existT. subst. *)
(*     assert ( refinesF RPre RPost RR b1 b2 id *)
(*                       (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2) *)
(*                       (observe m1) *)
(*                       (VisF (Spec_exists A) (fun a => Tau (k1 a))) ). *)
(*     { rewrite itree_eta'. pstep_reverse. *)
(*       apply refines_TauL_inv; auto. admit. pstep. auto. } *)
(*     clear Href. rename H into Href. pclearbot. *)
(*     eapply refinesF_Vis_existsR in Href; auto. punfold REL. red in REL. *)
(*     hinduction Href before r; intros; eauto. *)
(*     * eapply refinesF_existsR. constructor. right. *)
(*       eapply CIH; eauto with solve_padded. pstep. Unshelve. 3 : exact a. *)
(*       3: { *)
(*         apply go. *)
(*         apply phi. *)
(*       } *)
(*       red. auto. red. cbn in H. *)
(*       apply refines_TauR_inv; auto. *)
(*       admit. *)
(*       pstep; auto. *)
(*     * inv Hpad2. pclearbot. punfold H1. red in H1. *)
(*       remember (VisF (Spec_forall B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst. *)
(*       -- inv H1. inj_existT. subst. constructor; auto. rewrite <- Heqom2. *)
(*          eapply refinesF_forallL. Unshelve. 2 : exact b. eapply IHHref; eauto. *)
(*          pclearbot. pstep_reverse. rewrite <- (tau_eutt (k1 b)). auto. *)
(*          constructor. auto. *)
(*       -- constructor. auto. rewrite <- Heqom2. inv H1. pclearbot. punfold H2. *)
(*     * inv Hpad2. pclearbot. punfold H3. red in H3. *)
(*       remember (VisF (Spec_exists B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; auto. *)
(*       -- inv H3. inj_existT. subst. constructor. auto. intros. *)
(*          rewrite <- Heqom2. constructor. intros. eapply H0; eauto. Unshelve. all : auto. *)
(*          pclearbot. pstep_reverse.  setoid_rewrite tau_eutt in REL. auto. *)
(*          constructor. auto. *)
(*       -- constructor. auto. rewrite <- Heqom2. *)
(*          eapply IHREL; eauto. inv H3. pclearbot. pstep_reverse. *)
(*     * eapply IHHref; eauto. pstep_reverse. rewrite <- (tau_eutt phi1). pstep. auto. *)
(* Qed. *)

Lemma refines_eutt_padded_r_tau_aux:
  forall (E1 E2 : Type -> Type) (R2 : Type)
    (R1 : Type) (RPre : prerel E1 E2)
    (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
    b1 b2
    (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
    (m1 m2 : itree_spec E2 R2) (t1 : itree_spec E1 R1),
    is_true b1 ->
    is_true b2 ->
    refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) bot2)
             (observe t1) (TauF m1) ->
    paddedF (upaco1 padded_ bot1) (TauF m2) ->
    paddedF (upaco1 padded_ bot1) (observe t1) ->
    paco2 (eqit_ eq true true id) bot2 m1 m2 ->
    (forall (t2 : itree_spec E1 R1) (t3 t4 : itree_spec E2 R2),
        padded t2 ->
        padded t4 -> (eqit eq true true t3 t4) -> refines' RPre RPost RR b1 b2 t2 t3 -> r t2 t4) ->
    refinesF RPre RPost RR b1 b2 id (upaco2 (refines_ RPre RPost RR b1 b2 id) r)
             (observe t1) (TauF m2).
Proof.
  intros E1 E2 R2 R1 RPre RPost RR b1 b2 r m1 m2 t1 B1 B2 Href Hpad3 Hpad1 REL CIH.
  remember (observe t1) as ot1. clear Heqot1 t1.
  assert (HDEC : (exists t4, ot1 = TauF t4) \/ (forall t4, ot1 <> TauF t4)).
  { destruct ot1; eauto; right; repeat intro; discriminate. }
  destruct HDEC as [ [t4 Ht4] | Ht1]; subst.
  { constructor. right. eapply CIH; eauto. inv Hpad1. pclearbot. auto.
    inv Hpad3. pclearbot. auto.
    apply refines_TauTau_inv.
    pstep; eauto.
  }
  destruct ot1; try (exfalso; eapply Ht1; eauto; fail); try destruct e.
  - inv Href. constructor; auto. remember (RetF r0) as x.
    punfold REL. red in REL. hinduction H1 before r; intros; inv Heqx; subst.
    + remember (RetF r2) as x. hinduction REL before r; intros; inv Heqx; subst; eauto with solve_padded.
    + eapply IHrefinesF; eauto. pstep_reverse.
      rewrite <- (tau_eutt t2).
      pstep. auto.
    + inv Hpad3. pclearbot. punfold H2. red in H2.
      remember (VisF (Spec_forall A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; pclearbot.
      constructor. intros. eapply H0; eauto.  inv H2. inj_existT.
      subst. constructor. left. pstep. constructor. auto.
      pstep_reverse. constructor; auto. eapply IHREL; eauto. inv H2. pclearbot. punfold H3.
    + inv Hpad3. pclearbot. punfold H0. red in H0.
      remember (VisF (Spec_exists A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; pclearbot.
      econstructor. Unshelve. all : auto. intros. eapply IHrefinesF; eauto.  inv H0. inj_existT.
      subst. constructor. left. pstep. constructor. auto.
      pstep_reverse. constructor; auto. eapply IHREL; eauto. inv H0. pclearbot. pstep_reverse.
  - inv Href. constructor; auto. remember (VisF (Spec_vis e) k) as x.
    inv Hpad3. pclearbot. punfold H0. red in H0. punfold REL. red in REL.
    remember (VisF (Spec_vis e) k) as x.
    hinduction H1 before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
    + remember (VisF (Spec_vis e2) k2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * constructor; auto. intros. eapply H0 in H2. right. pclearbot.
        eapply CIH; eauto with solve_padded.
        apply REL.
      * constructor; auto. eapply IHREL; eauto. inv H1. pclearbot. pstep_reverse.
    + eapply IHrefinesF; eauto. pstep_reverse.
      rewrite <- (tau_eutt t2).
      pstep. auto.
   + remember (VisF (Spec_forall A) k) as x.
     hinduction REL before r; intros; inv Heqx; inj_existT; subst.
     * constructor; intros. eapply H0; eauto. pclearbot. pstep_reverse.
       inv H1. inj_existT. subst. constructor. auto.
     * constructor; auto. eapply IHREL; eauto. inv H1. pclearbot. pstep_reverse.
   + remember (VisF (Spec_exists A) k) as x.
     hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
     econstructor; intros. Unshelve. all : auto. eapply IHrefinesF; eauto with solve_padded.
     pclearbot. pstep_reverse.
  - inv Hpad1. inj_existT. subst.
    assert (refines' RPre RPost RR b1 b2 (Vis (Spec_forall A) (fun a => Tau (k1 a))) m1).
    { apply refines_TauR_inv; auto. pstep. auto. }
    clear Href. rename H into Href.
    punfold Href; red in Href.
    inv Hpad3. pclearbot. punfold H1. red in H1.
    apply refinesF_Vis_forallL in Href; auto. punfold REL. red in REL.

    hinduction Href before r; intros; pclearbot.
    + constructor; auto. remember (VisF (Spec_forall B) kphi2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * inv H2. inj_existT. subst. constructor. intros. eapply H0; auto.
        Unshelve. all : auto. pclearbot. setoid_rewrite tau_eutt in REL. pstep_reverse.
        pclearbot. pstep_reverse.
      * constructor; auto. eapply IHREL; eauto. inv H2. pclearbot. pstep_reverse.
    + eapply refinesF_forallL. Unshelve. all : auto. constructor.
      right. eapply CIH; eauto with solve_padded.
      rewrite (itree_eta' phi) in REL. pstep. red. eauto.
      apply refines_TauL_inv; auto. pstep. auto.
    + constructor; auto. remember (VisF (Spec_exists B) kphi2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * inv H1. inj_existT. subst. eapply refinesF_existsR.
        Unshelve. all : auto. cbn. eapply IHHref; eauto.
        pclearbot. setoid_rewrite tau_eutt in REL.
        pstep_reverse. pclearbot. pstep_reverse.
      * constructor; auto. eapply IHREL; eauto. inv H1. pclearbot.
        pstep_reverse.
    + eapply IHHref; eauto. pstep_reverse. setoid_rewrite <- (tau_eutt phi2).
      pstep. auto.
  - inv Hpad1. inj_existT. subst.
    apply refinesF_existsL. intros. constructor. right. eapply CIH; eauto with solve_padded.
    pclearbot. apply H0. inv Hpad3. pclearbot. auto.
    apply refines_TauL_inv; auto.
    set (fun a => Tau (k1 a)) as k2'.
    assert (k2' a = Tau (k1 a)). auto. rewrite <- H.
    eapply refines_existsL. unfold k2'. apply refines_TauR_inv; auto.
    pstep; red; cbn; auto.
Qed.


Lemma refines_eutt_padded_l E1 E2 R1 R2 RPre RPost RR :
  forall (t1 t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2),
    padded t2 -> padded t3 -> t1 ≈ t2 ->
    refines RPre RPost RR t1 t3 -> refines RPre RPost RR t2 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 Hpad2 Hpad3 Heutt Href.
  punfold Hpad2. red in Hpad2.
  punfold Hpad3. red in Hpad3.
  punfold Heutt. red in Heutt.
  punfold Href. red in Href. pstep.
  red.
  hinduction Heutt before r; intros; pclearbot; eauto.
  - subst. rewrite itree_eta' at 1. pstep_reverse.
    eapply paco2_mon; [ pstep; eapply Href | intros; contradiction].
  - eapply refines_eutt_padded_l_tau_aux; eauto.
  - (* need to figure this out *)
    destruct e.
    + assert (Hx : Vis (Spec_vis e) k1 ≈ Vis (Spec_vis e) k2).
      pstep. constructor. left. auto.
      punfold Hx. red in Hx. cbn in *.
      remember (VisF (Spec_vis e) k1) as x.
      hinduction Href before r; intros; inv Heqx; inj_existT; subst; eauto.
      * constructor; auto. intros a b Hab.
        eapply H0 in Hab. destruct Hab; try contradiction.
        right. eapply CIH; eauto with solve_padded. inv Hpad2.
        inj_existT. subst. pstep. constructor. auto.
        inv Hpad3. inj_existT. subst. (* pstep. constructor. auto. *)
        inv Hx. inj_existT. subst. destruct (REL0 a); try contradiction. auto.
        pclearbot.
        rewrite tau_eutt in H2.
        punfold H2.
      * constructor. auto. eapply IHHref; eauto with solve_padded.
      * constructor; auto. intros.
        eapply H0; eauto with solve_padded.
      * econstructor. eapply IHHref; eauto with solve_padded.
    + inv Hpad2. inj_existT. subst. pclearbot.
      eapply refinesF_Vis_forallL in Href; auto.
      induction Href.
      * constructor. intros. eapply H1. eauto with solve_padded.
      * econstructor. Unshelve. all : auto.
        rewrite itree_eta'.
        eapply refines_eutt_padded_l_tau_aux; eauto.
        setoid_rewrite tau_eutt in REL. auto. constructor. left. auto.
        constructor. constructor. auto.
      * eapply refinesF_existsR. eapply IHHref; eauto with solve_padded.
      * constructor; auto. eapply IHHref. inv Hpad3. pclearbot. pstep_reverse.
    + inv Hpad2. inj_existT. subst.
      (* this should be fine, exists L is invertible and then I just
         further invert Href until I learn more about t3
       *)
      constructor. intros.
      assert (forall a, refinesF RPre RPost RR true true id (upaco2 (refines_ RPre RPost RR true true id) bot2) (observe (k1 a)) (observe t3)).
      intros. pstep_reverse. eapply refines_existsL. pstep. auto.
      clear Href. rename H into Href. specialize (Href a).
      eapply refines_eutt_padded_l_tau_aux; eauto.
      setoid_rewrite tau_eutt in REL. auto.
      constructor. auto. constructor. constructor. auto.
  - eapply IHHeutt; eauto.
    pstep_reverse. apply refines_TauL_inv; auto. pstep. auto.
  - constructor. constructor. eapply IHHeutt; eauto with solve_padded.
Qed.

Lemma refines_eutt_padded_r E1 E2 R1 R2 RPre RPost RR :
  forall (t1 : itree_spec E1 R1) (t2 t3 : itree_spec E2 R2),
    padded t1 -> padded t3 -> t2 ≈ t3 ->
    refines RPre RPost RR t1 t2 -> refines RPre RPost RR t1 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 Hpad1 Hpad3 Heutt Href.
  punfold Href. punfold Heutt. red in Heutt. red in Href.
  punfold Hpad1. red in Hpad1. punfold Hpad3. red in Hpad3.
  pstep. red. hinduction Heutt before r; intros; pclearbot.
  - subst. rewrite itree_eta'. pstep_reverse.
    eapply paco2_mon; [ pstep; eapply Href | intros; contradiction].
  - eapply refines_eutt_padded_r_tau_aux; eauto.
  - destruct e.
    + assert (Hx : Vis (Spec_vis e) k1 ≈ Vis (Spec_vis e) k2).
      pstep. constructor. left. auto. punfold Hx. red in Hx.
      cbn in Hx.
      remember (VisF (Spec_vis e) k1) as y.
      hinduction Href before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded.
      constructor. auto. right. eapply CIH; eauto with solve_padded.
      inv Hpad1. inj_existT. cbn in *. subst.
      apply REL.
      inversion Hx. subst. inj_existT. subst. destruct (REL0 b); try contradiction.
      apply H0 in H1. destruct H1; auto; try contradiction.
    + inv Hpad3. inj_existT. subst.
      constructor. intros.
      eapply refines_eutt_padded_r_tau_aux with (m1 := k1 a); auto.
      constructor.
      constructor. pstep_reverse. apply refines_Vis_forallR. pstep. auto.
      constructor. auto. setoid_rewrite tau_eutt in REL. auto.
    + eapply refinesF_Vis_existsR in Href; auto.
      hinduction Href before r; intros; eauto.
      * econstructor. inv Hpad3. inj_existT. subst.
        Unshelve. all : auto. cbn.
        rewrite itree_eta' at 1.
        eapply refines_eutt_padded_r_tau_aux; auto. eauto.
        constructor. constructor. eauto.
        constructor. auto. setoid_rewrite tau_eutt in REL. auto.
      * eapply refinesF_forallL. eapply IHHref; eauto.
        inv Hpad1. inj_existT. subst. constructor. auto.
      * apply refinesF_existsL. intros. eapply H0; eauto.
        inv Hpad1. inj_existT. subst. constructor. auto.
      * constructor; auto. eapply IHHref; eauto. inv Hpad1. pclearbot. pstep_reverse.
  - eapply IHHeutt; eauto. pstep_reverse. apply refines_TauR_inv; auto. pstep. auto.
  - constructor; auto. eapply IHHeutt; eauto. inv Hpad3. pclearbot. pstep_reverse.
Qed.

Lemma refines'_eq_itree_r E1 E2 R1 R2 RPre RPost RR b1 b2 :
  forall (t1 : itree_spec E1 R1) (t2 t3 : itree_spec E2 R2),
    eq_itree eq t2 t3 ->
    refines' RPre RPost RR b1 b2 t1 t2 -> refines' RPre RPost RR b1 b2 t1 t3.
Proof.
  pcofix CIH. intros t1 t2 t3 Heutt Href.
  punfold Href. punfold Heutt. red in Heutt. red in Href.
  pstep. red. hinduction Heutt before r; intros; pclearbot; try discriminate.
  - subst. rewrite itree_eta'. pstep_reverse.
    eapply paco2_mon; [ pstep; eapply Href | intros; contradiction].
  - (* Tau / Tau case...

       Must use CIH. The tricky part here is that b1 / b2 could be
       true.

       If b1 and b2 are both false then we would know that t1 has to
       have a Tau, and we can apply the Tau/Tau constructor to get to
       r in order to apply CIH.

       If b1 and b2 are both true, then it's possible that we're just
       in a case with extra Taus on the right hand side of either the
       goal or Href. If that's the case, then we need to do induction
       to strip off the extra Taus.

     *)

    remember (TauF m1) as x.
    hinduction Href before r; intros;
      inv Heqx; inj_existT; subst; pclearbot; eauto with solve_padded.

    apply bisimulation_is_eq in REL; subst.
    constructor; auto.

    setoid_rewrite itree_eta'.
    pstep_reverse.
    eapply paco2_mon; [ pstep; eapply Href | intros; contradiction].      
  - destruct e.
    + assert (Hx : eq_itree eq (Vis (Spec_vis e) k1) (Vis (Spec_vis e) k2)).
      pstep. constructor. left. auto. punfold Hx. red in Hx.
      cbn in Hx.
      remember (VisF (Spec_vis e) k1) as y.
      hinduction Href before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded.
      constructor. auto. right. eapply CIH; eauto.
      inv Hx; inj_existT; cbn in *; subst.
      pclearbot.
      apply REL0.
      apply H0 in H1. destruct H1; auto; try contradiction.
    + constructor. intros.

      remember (VisF (Spec_forall A) k1) as x.
      hinduction Href before r; intros;
        inv Heqx; inj_existT; subst; pclearbot; eauto with solve_padded.

      specialize (REL a).
      apply bisimulation_is_eq in REL.
      rewrite <- REL.
      setoid_rewrite itree_eta'.
      pstep_reverse.
      eapply paco2_mon; [pstep; apply H | intros; contradiction].
    + remember (VisF (Spec_exists A) k1) as x.
      hinduction Href before r; intros;
        inv Heqx; inj_existT; subst; pclearbot; eauto with solve_padded.

      econstructor.
      specialize (REL a).
      apply bisimulation_is_eq in REL.
      rewrite <- REL.
      setoid_rewrite itree_eta'.
      pstep_reverse.
      eapply paco2_mon; [pstep; apply Href | intros; contradiction].
Qed.

Lemma Spec_vis_inv:
  forall (E1 : Type -> Type) (R1 : Type) (E2 : Type -> Type) (R2 : Type)
    R3 R4
    (RPre1 : prerel E1 E2) (RPost1 : postrel E1 E2) (RR1 : R3 -> R4 -> Prop) (e3 : E2 R2)
    (k1 : R2 -> itree_spec E2 R4) (e0 : E1 R1) (k0 : R1 -> itree_spec E1 R3),
    padded ((Vis (Spec_vis e0) k0)) -> padded (Vis (Spec_vis e3) k1 : itree_spec E2 R4) ->
    refinesF RPre1 RPost1 RR1 true true id (upaco2 (refines_ RPre1 RPost1 RR1 true true id) bot2) (VisF (Spec_vis e0) k0)
             (VisF (Spec_vis e3) k1) ->
    forall (a : R1) (c : R2),
      RPost1 _ _ e0 a e3 c -> refines RPre1 RPost1 RR1 (k0 a) (k1 c).
Proof.
  intros E1 R1 E2 R2 R3 R4 RPre1 RPost1 RR1 e3 k1 e0 k0 Hpad1 Hpad2 Href a c H6.
  remember (VisF (Spec_vis e0) k0) as x.
  remember (VisF (Spec_vis e3) k1) as y. cbn in *.
  hinduction Href before E1; intros; try discriminate.
  inversion Heqx. subst; inj_existT; subst.
  inversion Heqy. subst; inj_existT; subst.

  eapply refines_eutt_padded_l; eauto.
  eapply H0 in H6. pclearbot.
  pinversion Hpad1. subst. inj_existT. subst. pstep. constructor. auto.
  pinversion Hpad2. subst. inj_existT. subst. pstep. constructor. auto.
  reflexivity.
  eapply refines_eutt_padded_r; eauto.
  pinversion Hpad1. subst. inj_existT. subst. pstep. constructor.
  auto.
  pinversion Hpad2. subst. inj_existT. subst. pstep. constructor.
  auto. reflexivity.
  apply H0 in H6. pclearbot. auto.
Qed.

Lemma refinesTrans_aux:
  forall (E3 : Type -> Type) (R3 : Type) (E1 : Type -> Type) (R1 : Type) (E2 : Type -> Type) (R2 : Type)
    (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2)
    (RPost2 : postrel E2 E3) (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    b1 b2
    (r : itree_spec E1 R1 -> itree_spec E3 R3 -> Prop) (t1 : itree_spec E1 R1) (t0 : itree_spec E2 R2)
    X (e : SpecEvent E3 X) (k1 : X -> itree (SpecEvent E3) R3),
    (forall (t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) (t4 : itree_spec E3 R3),
        padded t2 ->
        padded t3 -> padded t4 -> refines' RPre1 RPost1 RR1 b1 b2 t2 t3 -> refines' RPre2 RPost2 RR2 b1 b2 t3 t4 -> r t2 t4) ->
    paco2 (refines_ RPre1 RPost1 RR1 b1 b2 id) bot2 t1 t0 ->
    paddedF (upaco1 padded_ bot1) (TauF t1) ->
    paddedF (upaco1 padded_ bot1) (TauF t0) ->
    refinesF RPre2 RPost2 RR2 b1 b2 id (upaco2 (refines_ RPre2 RPost2 RR2 b1 b2 id) bot2) (TauF t0)
             (VisF e (fun a : _ => Tau (k1 a))) ->
    (forall a : _, upaco1 padded_ bot1 (k1 a)) ->
    refinesF (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) b1 b2 id
             (upaco2 (refines_ (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) b1 b2 id) r)
             (TauF t1) (VisF e (fun a : _ => Tau (k1 a))).
Proof.
  intros E3 R3 E1 R1 E2 R2 RPre1 RPre2 RPost1 RPost2 RR1 RR2 b1 b2 r t1 t0 X e k1.
  (* Pad names... *)
  pose proof True as H.
  pose proof True as H1.
  pose proof True as H0.
  intros CIH Ht10 Ht1 Ht0 Ht23 Hk1.
  destruct e.
  - inv Ht23. rename H3 into Ht23. constructor; auto.
    punfold Ht10. red in Ht10.
    assert (Hy : padded (Vis (Spec_vis e) (fun a : X => Tau (k1 a)))).
    pstep. constructor. auto. punfold Hy. red in Hy. cbn in *.
    remember ((fun a => Tau (k1 a))) as k1'. assert (forall a, padded (k1' a)).
    pclearbot. auto. pstep. red. cbn. subst. constructor. auto.
    clear Heqk1' Hk1 k1. rename k1' into k1.
    inv Ht1. inv Ht0. pclearbot. punfold H4. punfold H5. red in H4. red in H5.
    remember (VisF (Spec_vis e) k1) as y. (* at this point need to prove that go _ _ y is padded*)
    hinduction Ht23 before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded.
    + assert (refines' RPre2 RPost2 RR2 b1 b2 (Vis (Spec_vis e1) k1) (Vis (Spec_vis e) k0)).
      pstep. constructor. auto. auto.
      clear H3. punfold H7. red in H7. cbn in H7.
      remember (VisF (Spec_vis e1) k1) as x. cbn in *.
      hinduction Ht10 before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
      constructor; eauto with solve_padded.

      (* Compose prerelation... *)
      econstructor; eauto.

      intros a b H10.
      inv H10. inj_existT. subst.
      pclearbot.
      specialize (H18 _ e0 H H1).
      destruct H18 as (?&?&?).
      right; eapply CIH; eauto with solve_padded.
      apply H0; eauto.
      apply H2; eauto.
    + eapply IHHt23; eauto with solve_padded. inv CHECK0.
      apply refinesF_TauR_inv; auto.
    + eapply IHHt23; eauto with solve_padded. pstep_reverse. eapply refines_Vis_forallR. pstep. auto.
    + eapply refinesF_Vis_existsR in Ht10; auto. assert (Hk : forall a, padded (k a)). inv H6. inj_existT.
      subst. intros. pstep. constructor. auto.
      induction Ht10.
      * rewrite itree_eta' at 1. eapply H0; eauto with solve_padded.
      * econstructor. eapply IHHt10; eauto. inv H5. inj_existT. subst. constructor. auto.
      * constructor. intros. eapply H8; eauto with solve_padded.
      * constructor; auto. eauto with solve_padded.
  - apply refinesF_forallR. intros. constructor. right. eapply CIH; eauto with solve_padded.
    pclearbot. apply Hk1. apply refines_TauTau_inv; eauto with solve_padded.
    specialize (Hk1 a).
    pclearbot. auto.
    set (fun a => Tau (k1 a)) as k'. assert (Tau (k1 a) = k' a). auto. rewrite H2.
    apply refines_Vis_forallR. pstep. auto.
  - rewrite itree_eta' in Ht23.
    cbn in *.
    punfold Ht10. red in Ht10. inv Ht1. inv Ht0. pclearbot.
    punfold H3. punfold H4. red in H3. red in H4. eapply refinesF_Vis_existsR in Ht23.
    remember (observe t1) as ot1. remember (observe t0) as ot0.
    remember (fun a => Tau (k1 a)) as k'.
    remember (TauF t0) as t0'.
    hinduction Ht23 before r; intros; subst.
    + eapply refinesF_existsR. Unshelve. all : auto. constructor.
      right. eapply CIH; eauto with solve_padded. pstep. auto.
      apply refinesF_TauTau_inv in H; eauto with solve_padded.
      pstep; red; auto.
    + inv H4. inj_existT. subst. pclearbot. cbn in Ht23.
      assert (Hk2 : forall a, refinesF RPre1 RPost1 RR1 b1 b2 id (upaco2 (refines_ RPre1 RPost1 RR1 b1 b2 id) bot2) (observe t1) (observe (kphi1 a)) ).
      { cbn. intros.
        eapply refinesF_TauTau_inv; eauto with solve_padded.
        (* set (fun a => Tau (k0 a)) as k2'. *)
(*         assert (TauF (k0 a) = observe (k2' a)). auto. rewrite H2. *)
(*         pstep_reverse. eapply refines_Vis_forallR. pstep. auto. } *)
(*       apply refinesF_Vis_existsR_Tau_inv in Ht23. *)
(*       specialize (Hk2 b). specialize (H5 b). punfold H5. red in H5. *)
(*       eapply IHHt23; eauto with solve_padded. *)
(*     + inv H5. inj_existT. subst. pclearbot. *)
(*       apply refinesF_Vis_existsR in Ht10. *)
(*       assert (Hk2 : forall b, existsRefinesF A RPre2 RPost2 RR2 true true id (upaco2 (refines_ RPre2 RPost2 RR2 true true id) bot2) *)
(*          (fun a : A => Tau (k1 a)) (observe ((k0 b)))). *)
(*       { *)
(*         intros. apply refinesF_Vis_existsR_Tau_inv. *)
(*         eauto. *)
(*       } *)
(*       clear H2. *)
(*       remember (observe t1) as ot1. pclearbot. *)
(*       remember (fun a => Tau (k1 a)) as k'. *)
(*       assert (go ot1 ≈ t1). subst. rewrite <- itree_eta. reflexivity. *)
(*       assert (Ht1 : padded t1). pstep. red. rewrite <- Heqot1. auto. *)
(*       clear Heqot1. *)
(*       hinduction Ht10 before r; intros; subst. *)
(*       * eapply H1; eauto with solve_padded. Unshelve. all : auto. *)
(*         pstep_reverse. eapply refines_eutt_padded_l; eauto with solve_padded. *)
(*         pstep. constructor. auto. *)
(*         pstep. auto. pstep_reverse. constructor. auto. *)
(*       * inv H4. inj_existT. subst. pclearbot. constructor. *)
(*         punfold H2. punfold H2. red in H2. cbn in *. *)
(*         punfold Ht1. red in Ht1. *)
(*         remember (VisF (Spec_forall _) (fun a => Tau (k2 a)) : itree_spec' E1 R1) as x. *)
(*         cbn in Heqx. setoid_rewrite <- Heqx in H2. *)
(*         remember (observe t1) as ot1. clear Heqot1 t1. pclearbot. *)
(*         remember (fun a => Tau (k2 a)) as k3'. *)
(*         hinduction H2 before r; intros; try (exfalso; inv Heqx; fail). *)
(*         -- pclearbot. subst. inv Heqx. inj_existT. subst. *)
(*            inv Ht1. inj_existT. subst. *)
(*            eapply refinesF_forallL. Unshelve. all : auto. *)
(*            eapply IHHt10; eauto with solve_padded. *)
(*            constructor. auto. clear - REL. *)
(*            specialize (REL b). *)
(*            rewrite <- (tau_eutt (k1 b)). *)
(*            apply REL. *)
(*            pclearbot. apply H4. *)
(*         -- constructor. constructor. eapply IHeqitF; eauto with solve_padded. *)
(*       * inv H5. inj_existT. subst. constructor. constructor. punfold H6. red in H6. *)
(*         cbn in H6. punfold Ht1. red in Ht1. *)
(*         remember (VisF (Spec_exists _) (fun a => Tau (k2 a)) : itree_spec' E1 R1) as x. *)
(*         cbn in Heqx. setoid_rewrite <- Heqx in H6. *)
(*         remember (fun a : _ => Tau (k2 a)) as k3'. *)
(*         hinduction H6 before r; intros; inv Heqx; inj_existT; subst. *)
(*         -- inv Ht1. inj_existT. subst. *)
(*            constructor. cbn. intros. *)
(*            eapply H0; eauto with solve_padded. Unshelve. all : auto. *)
(*            constructor. auto. cbn. pclearbot. *)
(*            rewrite <- (tau_eutt (k1 a)). *)
(*            apply REL. *)
(*            pclearbot. apply H6. *)
(*         -- constructor. constructor. eapply IHeqitF; eauto with solve_padded. auto. *)
(*       * eapply IHHt10; eauto with solve_padded. rewrite <- itree_eta. rewrite <- H2. *)
(*         rewrite tau_eutt. reflexivity. *)
(*     + eapply IHHt23; eauto with solve_padded. apply refinesF_TauR_inv. auto. *)
(* Qed. *)
Admitted.

Theorem refinesTrans {E1 E2 E3 R1 R2 R3} RPre1 RPre2 RPost1 RPost2
        (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) b1 b2
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) (t3 : itree_spec E3 R3):
  padded t1 -> padded t2 -> padded t3 ->
  refines' RPre1 RPost1 RR1 b1 b2 t1 t2 -> refines' RPre2 RPost2 RR2 b1 b2 t2 t3 ->
  refines' (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2)
          (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  revert t1 t2 t3; pcofix CIH.
  intros t1 t2 t3  Ht1 Ht2 Ht3 Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23. punfold Ht3. red in Ht3.
  punfold Ht2. red in Ht2.
  punfold Ht1. red in Ht1.
  remember (observe t3) as ot3.  clear t3 Heqot3.
  remember (observe t1) as ot1. clear t1 Heqot1.
  hinduction Ht12 before r; intros.
  - remember (RetF r2) as x. clear Ht2 Ht3.
    hinduction Ht23 before r; intros; inv Heqx; eauto with solve_padded.
  - pclearbot.
    assert (Hdec : (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4)).
    { destruct ot3; eauto; right; repeat intro; discriminate. }
    destruct Hdec as [ [t4 Ht4] | Ht4 ]; subst.
    + constructor. right. eapply CIH; eauto with solve_padded.
      pstep. red.
      apply refinesF_TauTau_inv in Ht23; eauto with solve_padded.
    + destruct ot3; try (exfalso; eapply Ht4; eauto; fail).
      * inv Ht23. clear Ht2 Ht3.
        inv Ht1. pclearbot. punfold H2.
        red in H2.
        punfold H. red in H. remember (RetF r0) as y.
        remember (observe t0) as ot0.
        constructor; auto.
        hinduction H1 before r; intros; inv Heqy; eauto with solve_padded.
        -- remember (RetF r1) as y.
           remember (observe t1) as ot1. clear Heqot1.
           hinduction H0 before r; intros; inv Heqy; eauto with solve_padded.
        -- eapply IHrefinesF; eauto.
           inv CHECK0.
           pstep_reverse. apply refines_TauR_inv; auto. pstep. auto.
        -- eapply IHrefinesF; eauto. pstep_reverse.
           inv CHECK.
           eapply refines_Vis_forallR. pstep. auto.
        -- eapply refinesF_Vis_existsR in H1; auto.
           induction H1; eauto with solve_padded.
           rewrite itree_eta' at 1. eapply H0; eauto with solve_padded.
      * inv Ht3. inj_existT. subst.
        eapply refinesTrans_aux; eauto.
(*   - assert (Href : refines RPre1 RPost1 RR1 (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2)). *)
(*     pstep. red. constructor. auto. auto. punfold Href. red in Href. cbn in *. *)
(*     remember (VisF (Spec_vis e2) k2) as x. *)
(*     (*k2 is getting captured in a weird way here from H3, *)
(*       need to ter *)
(*      *) *)

(*     hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto. *)
(*     + (*k1 and k3 are the same thing here *) *)
(*       constructor. *)
(*       econstructor; eauto. *)
(*       intros a b H3. *)
(*       inv H3; inj_existT; subst. *)
(*       specialize (H11 _ e3 H1 H) as [c [? ?]]. *)
(*       right. eapply CIH; (* k3 vs k1?, might be an artifact of my recursion *) eauto with solve_padded. inv Ht1. inj_existT. subst. *)
(*       pclearbot. *)
(*       eapply H2; eauto. *)
(*       pclearbot. *)
(*       eapply H0; eauto. *)
(*     + constructor. constructor. eapply IHHt23; eauto with solve_padded. *)
(*     + pclearbot. constructor. intros. eapply H0; try unfold id; eauto with solve_padded. *)
(*     + econstructor. eapply IHHt23; eauto with solve_padded. *)
(*   - constructor. constructor. eapply IHHt12; eauto with solve_padded. *)
(*   - eapply IHHt12; eauto with solve_padded. *)
(*     rewrite itree_eta'. *)
(*     apply refinesF_TauL_inv. auto. *)
(*   - apply refinesF_Vis_forallL in Ht23. *)
(*     induction Ht23. *)
(*     + constructor. intros. eauto with solve_padded. *)
(*     + eapply H0; eauto with solve_padded. *)
(*     + econstructor. eapply IHHt23; eauto with solve_padded. *)
(*     + constructor. constructor. eapply IHHt23; eauto with solve_padded. *)
(*   - eapply IHHt12; eauto with solve_padded. rewrite itree_eta'. *)
(*     pstep_reverse. apply refines_existsL. *)
(*     pstep. auto. *)
(*   - econstructor. eapply IHHt12; eauto with solve_padded. *)
(*   - constructor. intros. eapply H0; eauto with solve_padded. *)
(* Qed. *)
Admitted.

Definition padded_refines' {E1 E2 : Type -> Type}
  {R1 R2 : Type} (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
  b1 b2
  (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) :=
  refines' RPre RPost RR b1 b2 (pad t1) (pad t2).

Definition padded_refines {E1 E2 : Type -> Type}
           {R1 R2 : Type} (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
           (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) :=
  @padded_refines' E1 E2 R1 R2 RPre RPost RR true true t1 t2.

Section refines_monot.
Context (E1 E2 : Type -> Type).
Context (R1 R2: Type).
Context (RPre1 RPre2 : prerel E1 E2) (RPost1 RPost2 : postrel E1 E2) (RR1 RR2 : R1 -> R2 -> Prop).

Lemma refines_monot b1 b2 :
  (forall A B, RPre1 A B <2= RPre2 A B) ->
  (forall A B e1 e2, (fun a b => RPost2 A B e1 a e2 b) <2= (fun a b => RPost1 A B e1 a e2 b)) ->
  RR1 <2= RR2 ->
  forall phi1 phi2,
    refines' RPre1 RPost1 RR1 b1 b2 phi1 phi2 ->
    refines' RPre2 RPost2 RR2 b1 b2 phi1 phi2.
Proof.
  intros HPre HPost HRR. pcofix CIH.
  intros phi1 phi2 Hphi12. punfold Hphi12. red in Hphi12.
  pstep. red.
  pclearbot.
  hinduction Hphi12 before r; intros; pclearbot; eauto with itree_spec.
  constructor; eauto.
  intros. right. apply HPost in H1.
  eapply H0 in H1.
  eauto.
Qed.

Lemma padded_refines_monot b1 b2 :
  (forall A B, RPre1 A B <2= RPre2 A B) ->
  (forall A B e1 e2, (fun a b => RPost2 A B e1 a e2 b) <2= (fun a b => RPost1 A B e1 a e2 b)) ->
  RR1 <2= RR2 ->
  forall phi1 phi2,
    padded_refines' RPre1 RPost1 RR1 b1 b2 phi1 phi2 ->
    padded_refines' RPre2 RPost2 RR2 b1 b2 phi1 phi2.
Proof.
  intros. apply refines_monot; auto.
Qed.

End refines_monot.

Theorem padded_refines_trans (E1 E2 E3 : Type -> Type) b1 b2
        (R1 R2 R3 : Type) (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2)
        (RPost2 : postrel E2 E3) (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) t1 t2 t3:
  padded_refines' RPre1 RPost1 RR1 b1 b2 t1 t2 ->
  padded_refines' RPre2 RPost2 RR2 b1 b2 t2 t3 ->
  padded_refines' (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) b1 b2 t1 t3.
Proof.
  unfold padded_refines. intros. eapply refinesTrans; eauto; apply pad_is_padded.
Qed.


#[global] Instance padded_refines_proper_eutt {E1 E2 R1 R2} RPre RPost RR: Proper (eutt eq ==> eutt eq ==> flip impl)  (@padded_refines E1 E2 R1 R2 RPre RPost RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34 Href. red. red in Href.
  eapply refines_eutt_padded_r; try apply pad_is_padded.
  setoid_rewrite pad_eutt in Ht34.
  symmetry. eauto.
  eapply refines_eutt_padded_l; try apply pad_is_padded.
  setoid_rewrite pad_eutt in Ht12.
  symmetry. eauto. auto.
Qed.

#[global] Instance padded_refines_proper_eq_itree {E1 E2 R1 R2} RPre RPost RR b1 b2 : Proper (eq_itree eq ==> eq_itree eq ==> flip impl)  (@padded_refines' E1 E2 R1 R2 RPre RPost RR b1 b2).
Proof.
(*   repeat intro. eapply padded_refines_proper_eutt; eauto. *)
(*   rewrite H. reflexivity. rewrite H0. reflexivity. *)
(* Qed. *)
Admitted.

Variant PostRelEq {E : Type -> Type} : postrel E E :=
  | PostRelEq_intro A e a : @PostRelEq E A A e a e a.

Import EqdepFacts.

Definition eq_prerel {E} : prerel E E.
  intros A B e1 e2.
  apply (eq_dep _ E A e1 B e2).
Defined.

(* Definition eq_prerel {E} : prerel E E :=
  (fun (A B : Type) e1 e2 => @JMeq (E A) e1 (E B) e2). *)

Definition strict_refines' {E R} b1 b2 : itree_spec E R -> itree_spec E R -> Prop :=
  padded_refines' eq_prerel PostRelEq eq b1 b2.

Definition strict_refines {E R} : itree_spec E R -> itree_spec E R -> Prop :=
  strict_refines' true true.

Definition strict_refines_unpadded' {E R} b1 b2 : itree_spec E R -> itree_spec E R -> Prop :=
  refines' eq_prerel PostRelEq eq b1 b2.

Definition strict_refines_unpadded {E R} : itree_spec E R -> itree_spec E R -> Prop :=
  strict_refines_unpadded' true true.

#[global] Instance strict_refines_proper {E1 E2 R1 R2}
       (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) b1 b2:
  Proper (strict_refines' b1 b2 ==> flip (strict_refines' b1 b2) ==> Basics.flip Basics.impl) (padded_refines' RPre RPost RR b1 b2).
Proof.
  repeat intro. red in H1. eapply padded_refines_monot with (RPre1 := RComposePreRel eq_prerel (RComposePreRel RPre eq_prerel)).
  4 : { eapply padded_refines_trans; eauto.
        eapply padded_refines_trans. eauto.
        eapply H0. }
  - intros. destruct PR. destruct H3.
    destruct H2.
    destruct H4.
    auto.
  - intros. econstructor. intros. subst. destruct H3.
    destruct H4. destruct H2. subst. exists x1. split; [constructor | idtac].
    constructor. intros. subst.
    destruct H4.
    exists x2; split; eauto.
    constructor.
  - intros. destruct PR. subst.
    inv REL2; auto.
Qed.

Lemma refines_padded_refines :
  forall E1 E2 R1 R2 in_rel in_post_rel RR b1 b2 t1 t2,
    @refines'
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      b1 b2
      t1 t2 ->
    @padded_refines'
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      true true
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR b1 b2 t1 t2 REF.
  punfold REF; red in REF; cbn in REF.
  setoid_rewrite itree_eta.
  genobs t1 ot1.
  genobs t2 ot2.
  clear t1 t2 Heqot1 Heqot2.
  revert ot1 ot2 REF.
  pcofix CIH; intros ot1 ot2 REF.
  induction REF; cbn in *; subst; pclearbot;
    pstep; red; cbn;
    try solve [constructor; eauto with paco].
  - constructor.
    right.
    apply CIH.
    punfold H.
  - constructor; eauto.
    intros a b H1.
    left.
    pstep; red; cbn.
    constructor.
    right.
    apply CIH.
    apply H0 in H1.
    punfold H1.
  - constructor; eauto.
    punfold IHREF.
  - constructor; eauto.
    punfold IHREF.
  - constructor; eauto.
    intros a.
    specialize (H0 a).
    cbn.
    constructor; auto.
    punfold H0.
  - econstructor.
    cbn.
    constructor. constructor.
    punfold IHREF.
  - econstructor.
    cbn.
    constructor. constructor.
    punfold IHREF.
  - constructor; eauto.
    intros a.
    specialize (H0 a).
    cbn.
    constructor. constructor.
    punfold H0.
Qed.

#[global] Instance strict_refines_unpadded_proper {E1 E2 R1 R2}
       (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) :
  Proper (strict_refines_unpadded ==> flip strict_refines_unpadded ==> Basics.flip Basics.impl) (padded_refines RPre RPost RR).
Proof.
  repeat intro. red in H1. eapply padded_refines_monot with (RPre1 := RComposePreRel eq_prerel (RComposePreRel RPre eq_prerel)).
  4 : { eapply padded_refines_trans; eauto.
        apply refines_padded_refines; eauto.
        eapply padded_refines_trans. eauto.
        apply refines_padded_refines; eauto.
  }
  - intros. destruct PR. destruct H3.
    destruct H2.
    destruct H4.
    auto.
  - intros. econstructor. intros. subst. destruct H3.
    destruct H4. destruct H2. subst. exists x1. split; [constructor | idtac].
    constructor. intros. subst.
    destruct H4.
    exists x2; split; eauto.
    constructor.
  - intros. destruct PR. subst.
    inv REL2; auto.
Qed.

Lemma refines_refl {E R} (RPre : prerel E E) (RPost : postrel E E)
      (RR : R -> R -> Prop) b1 b2 :
  ReflexivePreRel RPre -> ReflexivePostRel RPost -> Reflexive RR ->
  forall t, padded t ->
  refines' RPre RPost RR b1 b2 t t.
Proof.
  intros HRPre HRPost HRR.  pcofix CIH. intros t Ht. pstep. red.
  punfold Ht. red in Ht. inversion Ht.
  - constructor. auto.
  - constructor. right. pclearbot. eauto.
  - destruct e.
    + constructor. auto. intros. apply HRPost in H1. subst. pclearbot.
      left. pstep. constructor. right. eapply CIH; eauto. apply H0.
    + constructor. intros. eapply refinesF_forallL. constructor.
      right. pclearbot. eapply CIH; eauto. apply H0.
    + constructor. intros. eapply refinesF_existsR. constructor.
      right. pclearbot. eapply CIH; eauto. apply H0.
Qed.

Lemma padded_refines_refl {E R} (RPre : prerel E E) (RPost : postrel E E)
      (RR : R -> R -> Prop) b1 b2 :
  ReflexivePreRel RPre -> ReflexivePostRel RPost -> Reflexive RR ->
  Reflexive (padded_refines' RPre RPost RR b1 b2).
Proof.
  repeat intro. apply refines_refl; auto. apply pad_is_padded.
Qed.

#[global] Instance strict_refines_refl {E R} : Reflexive (@strict_refines E R).
Proof.
  apply padded_refines_refl; auto. red. intros.
  constructor.
  constructor.
  - intros X e x.
    constructor.
  - repeat red.
    intros X e a b H.
    dependent destruction H; auto.
Qed.

#[global] Instance strict_refines_trans  {E R} : Transitive (@strict_refines E R).
Proof.
  repeat intro. eapply strict_refines_proper; eauto. reflexivity.
Qed.

Lemma padded_refines_weaken_l {E1 E2 R1 R2}
       (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) phi1 phi2 phi3 :
  strict_refines phi2 phi3 ->
  padded_refines RPre RPost RR phi1 phi2 ->
  padded_refines RPre RPost RR phi1 phi3.
Proof.
  intros. eapply strict_refines_proper; eauto. reflexivity.
Qed.

Lemma padded_refines_weaken_r {E1 E2 R1 R2}
       (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) phi1 phi2 phi3 :
  strict_refines phi1 phi2 ->
  padded_refines RPre RPost RR phi2 phi3 ->
  padded_refines RPre RPost RR phi1 phi3.
Proof.
  intros. eapply strict_refines_proper; eauto. reflexivity.
Qed.

Lemma refines_tauR_inv :
  forall E1 E2 R1 R2 in_rel in_post_rel RR t1 t2,
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 (Tau t2) ->
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR t1 t2 REF.
  punfold REF; red in REF; cbn in *.
  eapply refinesF_TauR_inv in REF.
  pstep; red; cbn; eauto.
Qed.

Lemma refines_tauL_inv :
  forall E1 E2 R1 R2 in_rel in_post_rel RR t1 t2,
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      (Tau t1) t2 ->
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR t1 t2 REF.
  punfold REF; red in REF; cbn in *.
  eapply refinesF_TauL_inv in REF.
  pstep; red; cbn; eauto.
Qed.

Lemma refinesF_tau_tau_inv:
  forall (E1 E2 : Type -> Type) (RPre : prerel E1 E2) (RPost : postrel E1 E2) 
    (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (phi1 : itree (SpecEvent E1) R1)
    (phi2 : itree (SpecEvent E2) R2),
  refinesF RPre RPost RR true true id (upaco2 (refines_ RPre RPost RR true true id) bot2) (TauF phi1) (TauF phi2) ->
  refinesF RPre RPost RR true true id (upaco2 (refines_ RPre RPost RR true true id) bot2) (observe phi1) (observe phi2).
Proof.
  intros E1 E2 RPre RPost R1 R2 RR phi1 phi2 REF.
  change (TauF phi2) with (observe (Tau phi2)) in REF.
  eapply refinesF_TauL_inv, refinesF_TauR_inv in REF.
  auto.
Qed.

Lemma refines_tau_tau_inv :
  forall E1 E2 R1 R2 in_rel in_post_rel RR t1 t2,
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      (Tau t1) (Tau t2) ->
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR t1 t2 REF.
  punfold REF; red in REF; cbn in *.
  eapply refinesF_tau_tau_inv in REF.
  pstep; red; cbn; eauto.
Qed.

Definition itree_spec_eqv {E R} (t1 t2 : itree_spec E R) : Prop :=
  strict_refines t1 t2 /\ strict_refines t2 t1.

#[global] Instance itree_spec_MonadEq1 {E} : Eq1 (itree_spec E).
red.
unfold itree_spec.
intros A.
apply itree_spec_eqv.
Defined.

Lemma eutt_spec_eqv :
  forall {E R} (t1 t2 : itree_spec E R),
    eutt eq t1 t2 ->
    eq1 t1 t2.
Proof.
  intros E R t1 t2 EQ.
  repeat red.
  rewrite EQ.
  split; reflexivity.  
Qed.

Section refine_closure.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
Context (pre : prerel E E) (post : postrel E E).

(** *** "Up-to" principles for coinduction. *)
Inductive refines_trans_clo (b1 b2 b1' b2' : bool) (r : itree_spec E R1 -> itree_spec E R2 -> Prop)
  : itree_spec E R1 -> itree_spec E R2 -> Prop :=
| refine_trans_clo_intro t1 t2 t1' t2' RR1 RR2
      (* t1' is smaller (or equal) to t1 *)
      (EQVl: refines' eq_prerel PostRelEq RR1 b1 b1' t1 t1')
      (* t2' is bigger (or equal) to t2 *)
      (EQVr: refines' eq_prerel PostRelEq RR2 b2' b2 t2' t2)
      (REL: r t1' t2')
      (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
      (LERR2: forall x y y', RR2 y' y -> RR x y' -> RR x y)
  : refines_trans_clo b1 b2 b1' b2' r t1 t2
.

(*
t1 >= t2   ===> t1' >= t2 where t1' >= t1
t1 >= t2   ===> t1 >= t2' where t2' <= t2

t1 >= t2 ====> t1' >= t2' where t1' >= t1 and t2' <= t2
*)

Hint Constructors refines_trans_clo : itree.

Definition refinesC b1 b2 := refines_trans_clo b1 b2 false false.
Hint Unfold refinesC : itree.

Lemma refinesC_mon b1 b2 r1 r2 t1 t2
      (IN: refinesC b1 b2 r1 t1 t2)
      (LE: r1 <2= r2):
  refinesC b1 b2 r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve refinesC_mon : paco.

Ltac unfold_refines :=
  (try match goal with [|- refines_ _ _ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: refines_ _ _ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma refinesC_wcompat b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (refinesC b1 b2) vclo <3= compose vclo (refinesC b1 b2)):
  wcompatible2 (@refines_ E E R1 R2 pre post RR b1 b2 vclo) (refinesC b1 b2).
Proof with eauto with paco itree_spec itree.
  econstructor; [ eauto with paco itree itree_spec | ].
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_refines.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto with paco itree itree_spec.
    remember (RetF r3) as y.
    induction EQVr;
      try solve [intros; subst; try inv Heqy; eauto with paco itree_spec itree].
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK...
    remember (TauF t4) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK...
    pclearbot. econstructor. gclo.
    econstructor; eauto with paco.
  - (* LHS can be replaced with (VisF (Spec_vis e1) k1)
       RHS can be replaced with (VisF (Spec_vis e2) k2)
     *)
    rename k1 into kl.
    rename k2 into kr.
    rename e1 into el.
    rename e2 into er.
    remember (VisF (Spec_vis el) kl) as x.
    (* Heqx: x = VisF (Spec_vis e1) k1 *)
    (* H: pre X Y e1 e2 *)
    hinduction EQVl before r; intros; try solve [discriminate Heqx | eauto with paco itree itree_spec].
    inv Heqx; inj_existT; subst.
    (* H: pre X X0 e1 e0 *)
    (* This is a different H because of the intros... *)
    (* e1 became e0, e2 became e3 *)
    (* a new e1 was introduced for observe t1 *)

    (* Heqx: VisF (Spec_vis e2) k2 = VisF (Spec_vis e0) k0 *)
    (* I don't understand where e1 and k1 went? *)
    (* e2 turned into e3... EQVr *)
    remember (VisF (Spec_vis er) kr) as y.
    hinduction EQVr before r; intros; try discriminate Heqy...
    inv Heqy; inj_existT; subst.
    inv H1; inj_existT; subst.
    inv H; inj_existT; subst.

    rename H2 into HL.
    rename H0 into HR.
    rename H4 into HREC.
    move HL after H8.
    move HR after HL.
    move HREC after HR.
    unfold id in HL, HR.
    pclearbot.
    (* In this remaining case we know that our original t1 / t2 are vis vodes...

       observe t1 = VisF (Spec_vis e0) k0
       observe t2 = VisF (Spec_vis e2) k2

       And we also have relations between these and our intermediate rewrites...

  HL :
    forall (a : X0) (b : X1),
    post X0 X1 e0 a el b ->
    paco2 (refines_ pre post RR1 b1 false (fun x : itree_spec E R1 -> itree_spec E R1 -> Prop => x))
      bot2 (k0 a) (kl b)
  HR :
    forall (a : Y0) (b : Y),
    post Y0 Y er a e2 b ->
    paco2 (refines_ pre post RR2 false b2 (fun x : itree_spec E R2 -> itree_spec E R2 -> Prop => x))
      bot2 (kr a) (k2 b)
  HREC : forall (a : X1) (b : Y0), post X1 Y0 el a er b -> vclo r (kl a) (kr b)
     *)
    constructor; eauto.
    (* e0 and e2 have to be related with post *)
    (* We want to replace:

       - e0 with el
       - e2 with er

       We have...

       H : pre Y0 Y er e2
       H1 : pre X0 X1 e0 el
       H3 : pre X1 Y0 el er

       So, I know that those events are somehow related.

       I also know...

       post X0 Y e0 a e2 b
     *)
    intros.
    pclearbot.
    eapply MON.
    + (* Want to use the closure to apply transitivity *)
      apply CMP.
      red.
      econstructor...
      -- apply HL.
         (* e0 and el are related with H1

            H0 should be irrelevant, e2 is for the RHS.
            Same with H3...
          *)
         constructor.
      -- apply HR.
         constructor.
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK...
    pclearbot.
    punfold H...
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK...
    pclearbot. punfold H...
  - (* forallR *)
    remember (VisF (Spec_forall A) k) as y.
    hinduction EQVr before r; intros; try discriminate Heqy...
    inv Heqy; inj_existT; subst.
    (* Should make sense by transitivity...

       H: ot1 >= observe (k0 a)
       EQVr: observe (k0 a) >= ot2
       EQVl: observe t1 >= ot1
       ===>
       observe t1 >= ot2

       Induction principles:
       IHEQVr: observe ?x >= ot2
       H0: observe ?x >= observe ?y
    *)

    rewrite (itree_eta' ot2); eauto.
  - (* existsR *)
    remember (VisF (Spec_exists A) k) as y.
    hinduction EQVr before r; intros; try discriminate Heqy...
    inv Heqy; inj_existT; subst.
    rewrite (itree_eta' ot2); eauto.
  - (* forallL *)
    remember (VisF (Spec_forall A) k) as y.
    hinduction EQVl before r; intros; try discriminate Heqy...
    inv Heqy; inj_existT; subst.
    rewrite (itree_eta' ot1); eauto.
  - (* existsL *)
    remember (VisF (Spec_exists A) k) as y.
    hinduction EQVl before r; intros; try discriminate Heqy...
    inv Heqy; inj_existT; subst.
    rewrite (itree_eta' ot1); eauto.
Qed.

Hint Resolve refinesC_wcompat : paco.

Lemma refines_idclo_compat b1 b2 : compose (refinesC b1 b2) id <3= compose id (refinesC b1 b2).
Proof.
  intros. apply PR.
Qed.
Hint Resolve refines_idclo_compat : paco.

Lemma refinesC_dist b1 b2 :
  forall r1 r2, refinesC b1 b2 (r1 \2/ r2) <2= (refinesC b1 b2 r1 \2/ refinesC b1 b2 r2).
Proof.
  intros. destruct PR. destruct REL; eauto with itree.
Qed.

Hint Resolve refinesC_dist : paco.

Lemma refines_clo_trans b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (refinesC b1 b2) vclo <3= compose vclo (refinesC b1 b2)):
  refines_trans_clo b1 b2 false false <3= gupaco2 (eqit_ RR b1 b2 vclo) (refinesC b1 b2).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End refine_closure.

#[global] Hint Unfold refinesC : itree.
#[global] Hint Resolve refinesC_mon : paco.
#[global] Hint Resolve refinesC_wcompat : paco.
#[global] Hint Resolve refines_idclo_compat : paco.
#[global] Hint Resolve refinesC_dist : paco.
Arguments refines_clo_trans : clear implicits.
#[global] Hint Constructors refines_trans_clo : itree.
