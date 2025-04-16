From Stdlib Require Import
     Program
     Setoid
     Morphisms
     Relations.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Eq.Eqit
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
Lemma refines_Vis_forallR : forall t k,
             refines RPre RPost RR t (Vis (Spec_forall A) k) ->
         forall a, refines RPre RPost RR t (k a).
Proof.
 intros t k Href a. punfold Href. red in Href. cbn in *. pstep. red.
  remember (observe t) as ot. clear Heqot.
  remember (VisF (Spec_forall A) k) as x.
  hinduction Href before E1; intros; inv Heqx; inj_existT; subst; pclearbot; eauto with itree_spec.
Qed.

Lemma refines_existsL : forall t k,
    refines RPre RPost RR (Vis (Spec_exists A) k) t ->
    forall a, refines RPre RPost RR (k a) t.
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
Inductive forallRefinesF (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          (kphi1 : A -> itree_spec E1 R1) : itree_spec' E2 R2 -> Prop :=
  | forallRefines_forallR B (kphi2 : B -> itree_spec E2 R2) :
    (forall b, forallRefinesF F kphi1 (observe (kphi2 b))) ->
    forallRefinesF F kphi1 (VisF (Spec_forall B) kphi2)
  | forallRefines_forallL phi (a : A) :
    refinesF RPre RPost RR F (observe (kphi1 a)) phi ->
    forallRefinesF F kphi1 phi
  | forallRefines_existsR B kphi2 (b : B) :
    (forallRefinesF F kphi1 (observe (kphi2 b))) ->
    forallRefinesF F kphi1 (VisF (Spec_exists B) kphi2)
  | forallRefines_TauR phi2 :
    forallRefinesF F kphi1 (observe phi2) ->
    forallRefinesF F kphi1 (TauF phi2).

(* A version of refinesF specialized to an exists on the left *)
Inductive existsRefinesF (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          (kphi2 : A -> itree_spec E2 R2) : itree_spec' E1 R1 -> Prop :=
  | existsRefines_existsR phi a :
    refinesF RPre RPost RR F phi (observe (kphi2 a)) ->
    existsRefinesF F kphi2 phi
  | existsRefines_forallL B (kphi1 : B -> itree_spec E1 R1) (b : B):
    existsRefinesF F kphi2 (observe (kphi1 b)) ->
    existsRefinesF F kphi2 (VisF (@Spec_forall E1 B) kphi1)
  | existsRefines_existsL B (kphi1 : B -> itree_spec E1 R1) :
    (forall b, existsRefinesF F kphi2 (observe (kphi1 b))) ->
    existsRefinesF F kphi2 (VisF (@Spec_exists E1 B) kphi1)
  | existsRefines_TauL phi1 :
    existsRefinesF F kphi2 (observe phi1) ->
    existsRefinesF F kphi2 (TauF phi1).
End refinesF_inv.

Lemma refinesF_Vis_existsR
  {E1 E2 R1 R2} (A : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
  : forall F (t : itree_spec' E1 R1) (k : A -> itree_spec E2 R2),
    refinesF RPre RPost RR F t (VisF (@Spec_exists E2 A) k) ->
    existsRefinesF A RPre RPost RR F k t.
Proof.
  intros. remember (VisF (Spec_exists A) k) as t1.
  induction H; try discriminate.
  - constructor. eauto.
  - inversion Heqt1. subst. inj_existT. subst. econstructor.
    eauto.
  - eapply existsRefines_forallL. eauto.
  - cbn.
    constructor. eauto.
Qed.

Lemma refinesF_Vis_forallL {E1 E2 R1 R2} (A : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
  : forall F (t : itree_spec' E2 R2) (k : A -> itree_spec E1 R1),
    refinesF RPre RPost RR F (VisF (@Spec_forall E1 A) k) t ->
    forallRefinesF A RPre RPost RR F k t.
Proof.
  intros. remember (VisF (Spec_forall A) k) as t1.
  induction H; try discriminate.
  - constructor. auto.
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

Lemma refines_TauL_inv : forall phi1 phi2,
    refines RPre RPost RR (Tau phi1) phi2 -> refines RPre RPost RR phi1 phi2.
Proof.
  pcofix CIH. intros. pstep. red. punfold H0. red in H0.
  cbn in *. remember (TauF phi1) as x.
  hinduction H0 before RPre; intros; inv Heqx; pclearbot; eauto with itree_spec.
  constructor. pstep_reverse. eapply paco2_mon; try apply H. intros. contradiction.
  eapply monotone_refinesF. 2 : eauto. intros. pclearbot. left.
  eapply paco2_mon; try apply PR. intros. contradiction.
Qed.

Lemma refines_TauR_inv : forall phi1 phi2,
    refines RPre RPost RR phi1 (Tau phi2) -> refines RPre RPost RR phi1 phi2.
Proof.
  intros. pstep. red. punfold H. red in H.
  cbn in *. remember (TauF phi2) as x.
  hinduction H before RPre; intros; inv Heqx; pclearbot; eauto with itree_spec.
  constructor. pstep_reverse.
Qed.

Lemma refinesF_TauR_inv : forall phi1 phi2,
      refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (observe phi1) (TauF phi2) ->
      refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (observe phi1) (observe phi2).
Proof.
  intros. pstep_reverse. apply refines_TauR_inv. pstep. auto.
Qed.

Lemma refinesF_TauL_inv : forall phi1 phi2,
      refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (TauF phi1) (observe phi2) ->
      refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (observe phi1) (observe phi2).
Proof.
  intros. pstep_reverse. apply refines_TauL_inv. pstep. auto.
Qed.

Lemma refinesF_Vis_existsR_Tau_inv {A} : forall t (k : A -> _),
    existsRefinesF A RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) k (TauF t) ->
    existsRefinesF A RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) k (observe t).
Proof.
  intros. inv H; auto.
  econstructor. eapply refinesF_TauL_inv. eauto.
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

Lemma refines_eutt_padded_l_tau_aux:
  forall (E1 E2 : Type -> Type) (R2 : Type)
    (R1 : Type) (RPre : prerel E1 E2)
    (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
    (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
    (m1 m2 : itree_spec E1 R1) (t3 : itree_spec E2 R2),
    (forall (t1 t2 : itree_spec E1 R1) (t4 : itree_spec E2 R2),
        padded t2 ->
        padded t4 -> t1 ≈ t2 -> refines RPre RPost RR t1 t4 -> r t2 t4) ->
    paco2 (eqit_ eq true true id) bot2 m1 m2 ->
    paddedF (upaco1 padded_ bot1) (TauF m2) ->
    paddedF (upaco1 padded_ bot1) (observe t3) ->
    refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2)
             (TauF m1) (observe t3) ->
    refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) r)
             (TauF m2) (observe t3).
Proof.
  intros E1 E2 R2 R1 RPre RPost RR r m1 m2 t3 CIH REL Hpad2 Hpad3 Href.
  remember (observe t3) as ot3. clear Heqot3 t3.
  assert (HDEC : (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4)).
  { destruct ot3; eauto; right; repeat intro; discriminate. }
  destruct HDEC as [ [t4 Ht4] |  Ht3]; subst.
  {
    constructor. right. eapply CIH; eauto. inv Hpad2. pclearbot. auto.
    inv Hpad3. pclearbot. auto.
    apply refines_TauL_inv. apply refines_TauR_inv. pstep. auto.
  }
  destruct ot3; try (exfalso; eapply Ht3; eauto; fail); try destruct e.
  + inv Href. constructor. punfold REL. red in REL.
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
  + inv Href. constructor.
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
      -- constructor. eapply IHREL; eauto.
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
    inv Hpad2. pclearbot. eapply refines_TauR_inv.
    set (fun a => Tau (k1 a)) as k2'. assert (Tau (k1 a) = k2' a). auto.
    rewrite H.
    apply refines_Vis_forallR. unfold k2'. apply refines_TauL_inv. pstep. auto.
  + inv Hpad3. inj_existT. subst.
    assert ( refinesF RPre RPost RR
                      (upaco2 (refines_ RPre RPost RR) bot2)
                      (observe m1)
                      (VisF (Spec_exists A) (fun a => Tau (k1 a))) ).
    { rewrite itree_eta'. pstep_reverse. apply refines_TauL_inv. pstep. auto. }
    clear Href. rename H into Href. pclearbot.
    eapply refinesF_Vis_existsR in Href. punfold REL. red in REL.
    hinduction Href before r; intros; eauto.
    * eapply refinesF_existsR. constructor. right.
      eapply CIH; eauto with solve_padded. pstep. Unshelve. 3 : exact a.
      3: {
        apply go.
        apply phi.
      }
      red. auto. red. apply refines_TauR_inv. pstep. auto.
    * inv Hpad2. pclearbot. punfold H1. red in H1.
      remember (VisF (Spec_forall B) kphi1) as x. remember (observe m2) as om2.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      -- inv H1. inj_existT. subst. constructor. rewrite <- Heqom2.
         eapply refinesF_forallL. Unshelve. 2 : exact b. eapply IHHref; eauto.
         pclearbot. pstep_reverse. rewrite <- (tau_eutt (k1 b)). auto.
         constructor. auto.
      -- constructor. rewrite <- Heqom2. inv H1. pclearbot. punfold H2.
    * inv Hpad2. pclearbot. punfold H3. red in H3.
      remember (VisF (Spec_exists B) kphi1) as x. remember (observe m2) as om2.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      -- inv H3. inj_existT. subst. constructor. intros.
         rewrite <- Heqom2. constructor. intros. eapply H0; eauto. Unshelve. all : auto.
         pclearbot. pstep_reverse.  setoid_rewrite tau_eutt in REL. auto.
         constructor. auto.
      -- constructor. rewrite <- Heqom2.
         eapply IHREL; eauto. inv H3. pclearbot. pstep_reverse.
    * eapply IHHref; eauto. pstep_reverse. rewrite <- (tau_eutt phi1). pstep. auto.
Qed.

Lemma refines_eutt_padded_r_tau_aux:
  forall (E1 E2 : Type -> Type) (R2 : Type)
    (R1 : Type) (RPre : prerel E1 E2)
    (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
    (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
    (m1 m2 : itree_spec E2 R2) (t1 : itree_spec E1 R1),
    refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2)
             (observe t1) (TauF m1) ->
    paddedF (upaco1 padded_ bot1) (TauF m2) ->
    paddedF (upaco1 padded_ bot1) (observe t1) ->
    paco2 (eqit_ eq true true id) bot2 m1 m2 ->
    (forall (t2 : itree_spec E1 R1) (t3 t4 : itree_spec E2 R2),
        padded t2 ->
        padded t4 -> t3 ≈ t4 -> refines RPre RPost RR t2 t3 -> r t2 t4) ->
    refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) r)
             (observe t1) (TauF m2).
Proof.
  intros E1 E2 R2 R1 RPre RPost RR r m1 m2 t1 Href Hpad3 Hpad1 REL CIH.
  remember (observe t1) as ot1. clear Heqot1 t1.
  assert (HDEC : (exists t4, ot1 = TauF t4) \/ (forall t4, ot1 <> TauF t4)).
  { destruct ot1; eauto; right; repeat intro; discriminate. }
  destruct HDEC as [ [t4 Ht4] | Ht1]; subst.
  { constructor. right. eapply CIH; eauto. inv Hpad1. pclearbot. auto.
    inv Hpad3. pclearbot. auto. apply refines_TauL_inv.
    apply refines_TauR_inv. pstep. auto. }
  destruct ot1; try (exfalso; eapply Ht1; eauto; fail); try destruct e.
  - inv Href. constructor. remember (RetF r0) as x.
    punfold REL. red in REL. hinduction H1 before r; intros; inv Heqx; subst.
    + remember (RetF r2) as x. hinduction REL before r; intros; inv Heqx; subst; eauto with solve_padded.
    + eapply IHrefinesF; eauto. pstep_reverse. rewrite <- (tau_eutt t2).
      pstep. auto.
    + inv Hpad3. pclearbot. punfold H2. red in H2.
      remember (VisF (Spec_forall A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; pclearbot.
      constructor. intros. eapply H0; eauto.  inv H2. inj_existT.
      subst. constructor. left. pstep. constructor. auto.
      pstep_reverse. constructor. eapply IHREL; eauto. inv H2. pclearbot. punfold H3.
    + inv Hpad3. pclearbot. punfold H0. red in H0.
      remember (VisF (Spec_exists A) k) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst; pclearbot.
      econstructor. Unshelve. all : auto. intros. eapply IHrefinesF; eauto.  inv H0. inj_existT.
      subst. constructor. left. pstep. constructor. auto.
      pstep_reverse. constructor. eapply IHREL; eauto. inv H0. pclearbot. pstep_reverse.
  - inv Href. constructor. remember (VisF (Spec_vis e) k) as x.
    inv Hpad3. pclearbot. punfold H0. red in H0. punfold REL. red in REL.
    remember (VisF (Spec_vis e) k) as x.
    hinduction H1 before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
    + remember (VisF (Spec_vis e2) k2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * constructor; auto. intros. eapply H0 in H2. right. pclearbot.
        eapply CIH; eauto with solve_padded.
        apply REL.
      * constructor. eapply IHREL; eauto. inv H1. pclearbot. pstep_reverse.
    + eapply IHrefinesF; eauto. pstep_reverse. setoid_rewrite <- (tau_eutt t2).
      pstep. auto.
   + remember (VisF (Spec_forall A) k) as x.
     hinduction REL before r; intros; inv Heqx; inj_existT; subst.
     * constructor; intros. eapply H0; eauto. pclearbot. pstep_reverse.
       inv H1. inj_existT. subst. constructor. auto.
     * constructor. eapply IHREL; eauto. inv H1. pclearbot. pstep_reverse.
   + remember (VisF (Spec_exists A) k) as x.
     hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded.
     econstructor; intros. Unshelve. all : auto. eapply IHrefinesF; eauto with solve_padded.
     pclearbot. pstep_reverse.
  - inv Hpad1. inj_existT. subst.
    assert (refines RPre RPost RR (Vis (Spec_forall A) (fun a => Tau (k1 a))) m1).
    { apply refines_TauR_inv. pstep. auto. }
    clear Href. rename H into Href.
    punfold Href. red in Href. inv Hpad3. pclearbot. punfold H1. red in H1.
    apply refinesF_Vis_forallL in Href. punfold REL. red in REL.
    hinduction Href before r; intros; pclearbot.
    + constructor. remember (VisF (Spec_forall B) kphi2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * inv H2. inj_existT. subst. constructor. intros. eapply H0; auto.
        Unshelve. all : auto. pclearbot. setoid_rewrite tau_eutt in REL. pstep_reverse.
        pclearbot. pstep_reverse.
      * constructor. eapply IHREL; eauto. inv H2. pclearbot. pstep_reverse.
    + eapply refinesF_forallL. Unshelve. all : auto. constructor.
      right. eapply CIH; eauto with solve_padded.
      rewrite (itree_eta' phi) in REL. pstep. red. eauto.
      apply refines_TauL_inv. pstep. auto.
    + constructor. remember (VisF (Spec_exists B) kphi2) as x.
      hinduction REL before r; intros; inv Heqx; inj_existT; subst.
      * inv H1. inj_existT. subst. eapply refinesF_existsR.
        Unshelve. all : auto. cbn. eapply IHHref; eauto.
        pclearbot. setoid_rewrite tau_eutt in REL.
        pstep_reverse. pclearbot. pstep_reverse.
      * constructor. eapply IHREL; eauto. inv H1. pclearbot.
        pstep_reverse.
    + eapply IHHref; eauto. pstep_reverse. setoid_rewrite <- (tau_eutt phi2).
      pstep. auto.
  - inv Hpad1. inj_existT. subst.
    apply refinesF_existsL. intros. constructor. right. eapply CIH; eauto with solve_padded.
    pclearbot. apply H0. inv Hpad3. pclearbot. auto.
    set (fun a => Tau (k1 a)) as k2'.
    apply refines_TauL_inv.
    assert (k2' a = Tau (k1 a)). auto. rewrite <- H.
    eapply refines_existsL. unfold k2'. apply refines_TauR_inv. pstep. auto.
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
      eapply refinesF_Vis_forallL in Href.
      induction Href.
      * constructor. intros. eapply H1. eauto with solve_padded.
      * econstructor. Unshelve. all : auto.
        rewrite itree_eta'.
        eapply refines_eutt_padded_l_tau_aux; eauto.
        setoid_rewrite tau_eutt in REL. auto. constructor. left. auto.
        constructor. auto.
      * eapply refinesF_existsR. eapply IHHref; eauto with solve_padded.
      * constructor. eapply IHHref. inv Hpad3. pclearbot. pstep_reverse.
    + inv Hpad2. inj_existT. subst.
      (* this should be fine, exists L is invertible and then I just
         further invert Href until I learn more about t3
       *)
      constructor. intros.
      assert (forall a, refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (observe (k1 a)) (observe t3)).
      intros. pstep_reverse. eapply refines_existsL. pstep. auto.
      clear Href. rename H into Href. specialize (Href a).
      eapply refines_eutt_padded_l_tau_aux; eauto.
      setoid_rewrite tau_eutt in REL. auto.
      constructor. auto. constructor. auto.
  - eapply IHHeutt; eauto.
    pstep_reverse. apply refines_TauL_inv. pstep. auto.
  - constructor. eapply IHHeutt; eauto with solve_padded.
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
      constructor. pstep_reverse. apply refines_Vis_forallR. pstep. auto.
      constructor. auto. setoid_rewrite tau_eutt in REL. auto.
    + eapply refinesF_Vis_existsR in Href.
      hinduction Href before r; intros; eauto.
      * econstructor. inv Hpad3. inj_existT. subst.
        Unshelve. all : auto. cbn.
        rewrite itree_eta' at 1.
        eapply refines_eutt_padded_r_tau_aux; auto. eauto.
        constructor. eauto.
        constructor. auto. setoid_rewrite tau_eutt in REL. auto.
      * eapply refinesF_forallL. eapply IHHref; eauto.
        inv Hpad1. inj_existT. subst. constructor. auto.
      * apply refinesF_existsL. intros. eapply H0; eauto.
        inv Hpad1. inj_existT. subst. constructor. auto.
      * constructor. eapply IHHref; eauto. inv Hpad1. pclearbot. pstep_reverse.
  - eapply IHHeutt; eauto. pstep_reverse. apply refines_TauR_inv. pstep. auto.
  - constructor. eapply IHHeutt; eauto. inv Hpad3. pclearbot. pstep_reverse.
Qed.

Lemma Spec_vis_inv:
  forall (E1 : Type -> Type) (R1 : Type) (E2 : Type -> Type) (R2 : Type)
    (RPre1 : prerel E1 E2) (RPost1 : postrel E1 E2) (RR1 : R1 -> R2 -> Prop) (e3 : E2 R2)
    (k1 : R2 -> itree_spec E2 R2) (e0 : E1 R1) (k0 : R1 -> itree_spec E1 R1),
    padded ((Vis (Spec_vis e0) k0)) -> padded (Vis (Spec_vis e3) k1 : itree_spec E2 R2) ->
    refinesF RPre1 RPost1 RR1 (upaco2 (refines_ RPre1 RPost1 RR1) bot2) (VisF (Spec_vis e0) k0)
             (VisF (Spec_vis e3) k1) ->
    forall (a : R1) (c : R2),
      RPost1 _ _ e0 a e3 c -> refines RPre1 RPost1 RR1 (k0 a) (k1 c).
Proof.
  intros E1 R1 E2 R2 RPre1 RPost1 RR1 e3 k1 e0 k0 Hpad1 Hpad2 Href a c H6.
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

(* Variant RComposePostRel {E1 E2 E3} `{EncodingType E1} `{EncodingType E2} `{EncodingType E3} *)
(*   (RPre1 : Rel E1 E2) (RPre2 : Rel E2 E3) (RPost1 : PostRel E1 E2) (RPost2 : PostRel E2 E3) : PostRel E1 E3 := *)
(*   | RComposePostRel_intro (e1 : E1) (e3 : E3) a c :  *)
(*     (forall e2, RPre1 e1 e2 -> RPre2 e2 e3 -> exists b, RPost1 e1 e2 a b /\ RPost2 e2 e3 b c) -> *)
(*     RComposePostRel RPre1 RPre2 RPost1 RPost2 e1 e3 a c. *)

Variant RComposePostRel {E1 E2 E3}
  (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2) (RPost2 : postrel E2 E3) : postrel E1 E3 :=
  | RComposePostRel_intro {A C} (e1 : E1 A) (e3 : E3 C) a c :
    (forall B (e2 : E2 B), RPre1 A B e1 e2 -> RPre2 B C e2 e3 -> exists b, RPost1 A B e1 a e2 b /\ RPost2 B C e2 b e3 c) ->
    RComposePostRel RPre1 RPre2 RPost1 RPost2 A C e1 a e3 c.

Variant RComposePreRel {E1 E2 E3}
  (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) : prerel E1 E3 :=
  | RComposePreRel_intro {A C} (e1 : E1 A) (e3 : E3 C) :
    forall {B} e2, RPre1 A B e1 e2 -> RPre2 B C e2 e3 ->
    @RComposePreRel E1 E2 E3 RPre1 RPre2 A C e1 e3.

Lemma refinesTrans_aux:
  forall (E3 : Type -> Type) (R3 : Type) (E1 : Type -> Type) (R1 : Type) (E2 : Type -> Type) (R2 : Type)
    (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2)
    (RPost2 : postrel E2 E3) (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (r : itree_spec E1 R1 -> itree_spec E3 R3 -> Prop) (t1 : itree_spec E1 R1) (t0 : itree_spec E2 R2)
    X (e : SpecEvent E3 X) (k1 : X -> itree (SpecEvent E3) R3),
    (forall (t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) (t4 : itree_spec E3 R3),
        padded t2 ->
        padded t3 -> padded t4 -> refines RPre1 RPost1 RR1 t2 t3 -> refines RPre2 RPost2 RR2 t3 t4 -> r t2 t4) ->
    paco2 (refines_ RPre1 RPost1 RR1) bot2 t1 t0 ->
    paddedF (upaco1 padded_ bot1) (TauF t1) ->
    paddedF (upaco1 padded_ bot1) (TauF t0) ->
    refinesF RPre2 RPost2 RR2 (upaco2 (refines_ RPre2 RPost2 RR2) bot2) (TauF t0)
             (VisF e (fun a : _ => Tau (k1 a))) ->
    (forall a : _, upaco1 padded_ bot1 (k1 a)) ->
    refinesF (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2)
             (upaco2 (refines_ (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2)) r)
             (TauF t1) (VisF e (fun a : _ => Tau (k1 a))).
Proof.
  intros E3 R3 E1 R1 E2 R2 RPre1 RPre2 RPost1 RPost2 RR1 RR2 r t1 t0 X e k1.
  (* Pad names... *)
  pose proof True as H.
  pose proof True as H1.
  pose proof True as H0.
  intros CIH Ht10 Ht1 Ht0 Ht23 Hk1.
  destruct e.
  - inv Ht23. rename H3 into Ht23. constructor.
    punfold Ht10. red in Ht10.
    assert (Hy : padded (Vis (Spec_vis e) (fun a : X => Tau (k1 a)))).
    pstep. constructor. auto. punfold Hy. red in Hy. cbn in *.
    remember ((fun a => Tau (k1 a))) as k1'. assert (forall a, padded (k1' a)).
    pclearbot. auto. pstep. red. cbn. subst. constructor. auto.
    clear Heqk1' Hk1 k1. rename k1' into k1.
    inv Ht1. inv Ht0. pclearbot. punfold H4. punfold H5. red in H4. red in H5.
    remember (VisF (Spec_vis e) k1) as y. (* at this point need to prove that go _ _ y is padded*)
    hinduction Ht23 before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded.
    + assert (refines RPre2 RPost2 RR2 (Vis (Spec_vis e1) k1) (Vis (Spec_vis e) k0)).
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
    + eapply IHHt23; eauto with solve_padded. apply refinesF_TauR_inv. auto.
    + eapply IHHt23; eauto with solve_padded. pstep_reverse. eapply refines_Vis_forallR. pstep. auto.
    + eapply refinesF_Vis_existsR in Ht10. assert (Hk : forall a, padded (k a)). inv H6. inj_existT.
      subst. intros. pstep. constructor. auto.
      induction Ht10.
      * rewrite itree_eta' at 1. eapply H0; eauto with solve_padded.
      * econstructor. eapply IHHt10; eauto. inv H5. inj_existT. subst. constructor. auto.
      * constructor. intros. eapply H8; eauto with solve_padded.
      * constructor. eauto with solve_padded.
  - apply refinesF_forallR. intros. constructor. right. eapply CIH; eauto with solve_padded.
    pclearbot. apply Hk1. apply refines_TauL_inv. apply refines_TauR_inv.
    set (fun a => Tau (k1 a)) as k'. assert (Tau (k1 a) = k' a). auto. rewrite H2.
    apply refines_Vis_forallR. pstep. auto.
  - rewrite itree_eta' in Ht23. apply refinesF_TauL_inv in Ht23. cbn in Ht23.
    punfold Ht10. red in Ht10. inv Ht1. inv Ht0. pclearbot.
    punfold H3. punfold H4. red in H3. red in H4. eapply refinesF_Vis_existsR in Ht23.
    remember (observe t1) as ot1. remember (observe t0) as ot0.
    remember (fun a => Tau (k1 a)) as k'.
    hinduction Ht23 before r; intros; subst.
    + eapply refinesF_existsR. Unshelve. all : auto. constructor.
      right. eapply CIH; eauto with solve_padded. pstep. auto.
      apply refines_TauR_inv. pstep. auto.
    + inv H4. inj_existT. subst. pclearbot. cbn in Ht23.
      assert (Hk2 : forall a, refinesF RPre1 RPost1 RR1  (upaco2 (refines_ RPre1 RPost1 RR1) bot2) (observe t1) (observe (k0 a)) ).
      { cbn. intros. eapply refinesF_TauR_inv. set (fun a => Tau (k0 a)) as k2'.
        assert (TauF (k0 a) = observe (k2' a)). auto. rewrite H2.
        pstep_reverse. eapply refines_Vis_forallR. pstep. auto. }
      apply refinesF_Vis_existsR_Tau_inv in Ht23.
      specialize (Hk2 b). specialize (H5 b). punfold H5. red in H5.
      eapply IHHt23; eauto with solve_padded.
    + inv H5. inj_existT. subst. pclearbot.
      apply refinesF_Vis_existsR in Ht10.
      assert (Hk2 : forall b, existsRefinesF A RPre2 RPost2 RR2 (upaco2 (refines_ RPre2 RPost2 RR2) bot2)
         (fun a : A => Tau (k1 a)) (observe ((k0 b)))).
      {
        intros. apply refinesF_Vis_existsR_Tau_inv.
        eauto.
      }
      clear H2.
      remember (observe t1) as ot1. pclearbot.
      remember (fun a => Tau (k1 a)) as k'.
      assert (go ot1 ≈ t1). subst. rewrite <- itree_eta. reflexivity.
      assert (Ht1 : padded t1). pstep. red. rewrite <- Heqot1. auto.
      clear Heqot1.
      hinduction Ht10 before r; intros; subst.
      * eapply H1; eauto with solve_padded. Unshelve. all : auto.
        pstep_reverse. eapply refines_eutt_padded_l; eauto with solve_padded.
        pstep. constructor. auto.
        pstep. auto. pstep_reverse. constructor. auto.
      * inv H4. inj_existT. subst. pclearbot. constructor.
        punfold H2. red in H2. cbn in *.
        punfold Ht1. red in Ht1.
        remember (VisF (Spec_forall _) (fun a => Tau (k2 a)) : itree_spec' E1 R1) as x.
        cbn in Heqx. setoid_rewrite <- Heqx in H2.
        remember (observe t1) as ot1. clear Heqot1 t1. pclearbot.
        remember (fun a => Tau (k2 a)) as k3'.
        hinduction H2 before r; intros; try (exfalso; inv Heqx; fail).
        -- pclearbot. subst. inv Heqx. inj_existT. subst.
           inv Ht1. inj_existT. subst.
           eapply refinesF_forallL. Unshelve. all : auto.
           eapply IHHt10; eauto with solve_padded.
           constructor. auto. clear - REL.
           specialize (REL b).
           rewrite <- (tau_eutt (k1 b)).
           apply REL.
           pclearbot. apply H4.
        -- constructor. eapply IHeqitF; eauto with solve_padded.
      * inv H5. inj_existT. subst. constructor. punfold H6. red in H6.
        cbn in H6. punfold Ht1. red in Ht1.
        remember (VisF (Spec_exists _) (fun a => Tau (k2 a)) : itree_spec' E1 R1) as x.
        cbn in Heqx. setoid_rewrite <- Heqx in H6.
        remember (fun a : _ => Tau (k2 a)) as k3'.
        hinduction H6 before r; intros; inv Heqx; inj_existT; subst.
        -- inv Ht1. inj_existT. subst. constructor. cbn. intros.
           eapply H0; eauto with solve_padded. Unshelve. all : auto.
           constructor. auto. cbn. pclearbot.
           rewrite <- (tau_eutt (k1 a)).
           apply REL.
           pclearbot. apply H6.
        -- constructor. eapply IHeqitF; eauto with solve_padded. auto.
      * eapply IHHt10; eauto with solve_padded. rewrite <- itree_eta. rewrite <- H2.
        rewrite tau_eutt. reflexivity.
    + eapply IHHt23; eauto with solve_padded. apply refinesF_TauR_inv. auto.
Qed.

Theorem refinesTrans {E1 E2 E3 R1 R2 R3} RPre1 RPre2 RPost1 RPost2
        (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) (t3 : itree_spec E3 R3):
  padded t1 -> padded t2 -> padded t3 ->
  refines RPre1 RPost1 RR1 t1 t2 -> refines RPre2 RPost2 RR2 t2 t3 ->
  refines (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2)
          (rcompose RR1 RR2) t1 t3.
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
      apply refines_TauL_inv. apply refines_TauR_inv. pstep. auto.
    + destruct ot3; try (exfalso; eapply Ht4; eauto; fail).
      * constructor. inv Ht23. clear Ht2 Ht3.
        inv Ht1. pclearbot. punfold H2.
        red in H2.
        punfold H. red in H. remember (RetF r0) as y.
        remember (observe t0) as ot0.
        hinduction H1 before r; intros; inv Heqy; eauto with solve_padded.
        -- remember (RetF r1) as y.
           remember (observe t1) as ot1. clear Heqot1.
           hinduction H0 before r; intros; inv Heqy; eauto with solve_padded.
        -- eapply IHrefinesF; eauto.
           pstep_reverse. apply refines_TauR_inv. pstep. auto.
        -- eapply IHrefinesF; eauto. pstep_reverse.
           eapply refines_Vis_forallR. pstep. auto.
        -- eapply refinesF_Vis_existsR in H1.
           induction H1; eauto with solve_padded.
           rewrite itree_eta' at 1. eapply H0; eauto with solve_padded.
      * inv Ht3. inj_existT. subst.
        eapply refinesTrans_aux; eauto.
  - assert (Href : refines RPre1 RPost1 RR1 (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2)).
    pstep. red. constructor. auto. auto. punfold Href. red in Href. cbn in *.
    remember (VisF (Spec_vis e2) k2) as x.
    (*k2 is getting captured in a weird way here from H3,
      need to ter
     *)

    hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
    + (*k1 and k3 are the same thing here *)
      constructor.
      econstructor; eauto.
      intros a b H3.
      inv H3; inj_existT; subst.
      specialize (H11 _ e3 H1 H) as [c [? ?]].
      right. eapply CIH; (* k3 vs k1?, might be an artifact of my recursion *) eauto with solve_padded. inv Ht1. inj_existT. subst.
      pclearbot.
      eapply H2; eauto.
      pclearbot.
      eapply H0; eauto.
    + constructor. eapply IHHt23; eauto with solve_padded.
    + pclearbot. constructor. intros. eapply H0; eauto with solve_padded.
    + econstructor. eapply IHHt23; eauto with solve_padded.
  - constructor. eapply IHHt12; eauto with solve_padded.
  - eapply IHHt12; eauto with solve_padded.
    rewrite itree_eta'.
    apply refinesF_TauL_inv. auto.
  - apply refinesF_Vis_forallL in Ht23.
    induction Ht23.
    + constructor. intros. eauto with solve_padded.
    + eapply H0; eauto with solve_padded.
    + econstructor. eapply IHHt23; eauto with solve_padded.
    + constructor. eapply IHHt23; eauto with solve_padded.
  - eapply IHHt12; eauto with solve_padded. rewrite itree_eta'.
    pstep_reverse. apply refines_existsL.
    pstep. auto.
  - econstructor. eapply IHHt12; eauto with solve_padded.
  - constructor. intros. eapply H0; eauto with solve_padded.
Qed.

Definition padded_refines {E1 E2 : Type -> Type}
           {R1 R2 : Type} (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop)
           (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) :=
  refines RPre RPost RR (pad t1) (pad t2).

Section refines_monot.
Context (E1 E2 : Type -> Type).
Context (R1 R2: Type).
Context (RPre1 RPre2 : prerel E1 E2) (RPost1 RPost2 : postrel E1 E2) (RR1 RR2 : R1 -> R2 -> Prop).

Lemma refines_monot :
  (forall A B, RPre1 A B <2= RPre2 A B) ->
  (forall A B e1 e2, (fun a b => RPost2 A B e1 a e2 b) <2= (fun a b => RPost1 A B e1 a e2 b)) ->
  RR1 <2= RR2 ->
  forall phi1 phi2,
    refines RPre1 RPost1 RR1 phi1 phi2 ->
    refines RPre2 RPost2 RR2 phi1 phi2.
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

Lemma padded_refines_monot :
  (forall A B, RPre1 A B <2= RPre2 A B) ->
  (forall A B e1 e2, (fun a b => RPost2 A B e1 a e2 b) <2= (fun a b => RPost1 A B e1 a e2 b)) ->
  RR1 <2= RR2 ->
  forall phi1 phi2,
    padded_refines RPre1 RPost1 RR1 phi1 phi2 ->
    padded_refines RPre2 RPost2 RR2 phi1 phi2.
Proof.
  intros. apply refines_monot; auto.
Qed.

End refines_monot.

Theorem padded_refines_trans (E1 E2 E3 : Type -> Type)
        (R1 R2 R3 : Type) (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2)
        (RPost2 : postrel E2 E3) (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) t1 t2 t3:
  padded_refines RPre1 RPost1 RR1 t1 t2 ->
  padded_refines RPre2 RPost2 RR2 t2 t3 ->
  padded_refines (RComposePreRel RPre1 RPre2) (RComposePostRel RPre1 RPre2 RPost1 RPost2) (rcompose RR1 RR2) t1 t3.
Proof.
  unfold padded_refines. intros. eapply refinesTrans; eauto; apply pad_is_padded.
Qed.


Global Instance padded_refines_proper_eutt {E1 E2 R1 R2} RPre RPost RR : Proper (eutt eq ==> eutt eq ==> flip impl)  (@padded_refines E1 E2 R1 R2 RPre RPost RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34 Href. red. red in Href.
  eapply refines_eutt_padded_r; try apply pad_is_padded.
  setoid_rewrite pad_eutt in Ht34.
  symmetry. eauto.
  eapply refines_eutt_padded_l; try apply pad_is_padded.
  setoid_rewrite pad_eutt in Ht12.
  symmetry. eauto. auto.
Qed.

Global Instance padded_refines_proper_eq_itree {E1 E2 R1 R2} RPre RPost RR : Proper (eq_itree eq ==> eq_itree eq ==> flip impl)  (@padded_refines E1 E2 R1 R2 RPre RPost RR).
Proof.
  repeat intro. eapply padded_refines_proper_eutt; eauto.
  rewrite H. reflexivity. rewrite H0. reflexivity.
Qed.

Variant PostRelEq {E : Type -> Type} : postrel E E :=
  | PostRelEq_intro A e a : @PostRelEq E A A e a e a.

Import EqdepFacts.

Definition eq_prerel {E} : prerel E E.
  intros A B e1 e2.
  apply (eq_dep _ E A e1 B e2).
Defined.

(* Definition eq_prerel {E} : prerel E E :=
  (fun (A B : Type) e1 e2 => @JMeq (E A) e1 (E B) e2). *)

Definition strict_refines {E R} : itree_spec E R -> itree_spec E R -> Prop :=
  padded_refines eq_prerel PostRelEq eq.

#[global] Instance strict_refines_proper {E1 E2 R1 R2}
       (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) :
  Proper (strict_refines ==> flip strict_refines ==> Basics.flip Basics.impl) (padded_refines RPre RPost RR).
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

Lemma refines_refl {E R} (RPre : prerel E E) (RPost : postrel E E)
      (RR : R -> R -> Prop) :
  ReflexivePreRel RPre -> ReflexivePostRel RPost -> Reflexive RR ->
  forall t, padded t ->
  refines RPre RPost RR t t.
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
      (RR : R -> R -> Prop) :
  ReflexivePreRel RPre -> ReflexivePostRel RPost -> Reflexive RR ->
  Reflexive (padded_refines RPre RPost RR).
Proof.
  repeat intro. apply refines_refl; auto. apply pad_is_padded.
Qed.

#[global] Instance strict_refines_refl {E R} : Reflexive (@strict_refines E R).
Proof.
  apply padded_refines_refl; auto. red. intros.
  constructor.
  repeat red.
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

Lemma refines_padded_refines :
  forall E1 E2 R1 R2 in_rel in_post_rel RR t1 t2,
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2 ->
    @padded_refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR t1 t2 REF.
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
    constructor.
    punfold H0.
  - econstructor.
    cbn.
    constructor.
    punfold IHREF.
  - econstructor.
    cbn.
    constructor.
    punfold IHREF.
  - constructor; eauto.
    intros a.
    specialize (H0 a).
    cbn.
    constructor.
    punfold H0.
Qed.
