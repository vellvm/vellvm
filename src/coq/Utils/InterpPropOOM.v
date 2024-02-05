(* begin hide *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Core.ITreeMonad
     CategoryKleisli
     CategoryKleisliFacts
     Eq.Eqit.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     RelationClasses
     Strings.String
     Logic
     Morphisms
     Relations
     List
     Program.Tactics Program.Equality.
From ITree Require Import
     Basics.Monad
     Eq.EqAxiom.

From Vellvm Require Import
     Utils.PropT.

Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

(* Definition 5.3: Handler Correctness *)
  Definition handler_correct {E F} (h_spec: E ~> PropT F) (h: E ~> itree F) :=
    (forall T e ta, ta ≈ h T e -> h_spec T e ta).

#[global] Instance void1_unit {E} : void1 -< E.
  repeat intro; contradiction.
Qed.

Section interp_prop_oom.

  Context {E F OOM : Type -> Type} `{OOME: OOM -< E} `{OOMF: OOM -< F}.
  Context (h_spec : E ~> PropT F) {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop).

  Definition k_spec_correct : Prop
    := forall T (R2 : Type) e k2 t2 ta,
      h_spec _ e ta ->
      t2 ≈ bind ta k2 ->
      k_spec T R2 e ta k2 t2.

  (* Well-formedness conditions for k_specs *)
  Class k_spec_WF := {
      k_spec_Proper : forall {A R2} e ta k2,
        Proper (eutt eq  ==>  iff) (@k_spec A R2 e ta k2);
      k_spec_Correct : k_spec_correct;
    }.

  Context (k_spec_wellformed : k_spec_WF).

  Inductive interp_prop_oomTF
            (b1 b2 : bool) (o1 o2 : bool) (sim : itree E R1 -> itree F R2 -> Prop)
            : itree' E R1 -> itree' F R2 -> Prop :=
  | Interp_Prop_OomT_Ret : forall r1 r2 (REL: RR r1 r2),
      interp_prop_oomTF b1 b2 o1 o2 sim (RetF r1) (RetF r2)

  | Interp_Prop_OomT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_prop_oomTF b1 b2 o1 o2 sim (TauF t1) (TauF t2)

  | Interp_Prop_OomT_TauL : forall t1 t2
                          (CHECK: is_true b1)
                          (HS: interp_prop_oomTF b1 b2 o1 o2 sim (observe t1) t2),
      interp_prop_oomTF b1 b2 o1 o2 sim (TauF t1) t2

  | Interp_Prop_OomT_TauR : forall t1 t2
                          (CHECK: is_true b2)
                          (HS: interp_prop_oomTF b1 b2 o1 o2 sim t1 (observe t2)),
      interp_prop_oomTF b1 b2 o1 o2 sim t1 (TauF t2)

  | Interp_Prop_OomT_Vis_OOM_L : forall A (e : OOM A) k1 t1 t2
                                   (CHECK: is_true o1)
                                   (HT1: t1 ≅ Vis (subevent A e) k1),
      interp_prop_oomTF b1 b2 o1 o2 sim (observe t1) t2

  | Interp_Prop_OomT_Vis_OOM_R : forall A (e : OOM A) k2 t1 t2
                                   (CHECK: is_true o2)
                                   (HT1: t2 ≅ Vis (subevent A e) k2),
      interp_prop_oomTF b1 b2 o1 o2 sim t1 (observe t2)

  | Interp_Prop_OomT_Vis : forall A e k1 k2 (ta t2 : itree F _)
                  (HK : forall (a : A), Returns a ta -> sim (k1 a) (k2 a))
                  (HSPEC : h_spec _ e ta)
                  (* k_spec => t2 ≈ bind ta k2 *)
                  (* k_spec => True *)
                  (KS : k_spec A R2 e ta k2 t2), 
      interp_prop_oomTF b1 b2 o1 o2 sim (VisF e k1) (observe t2).

  Hint Constructors interp_prop_oomTF : core.

  Lemma interp_prop_oomTF_mono b1 b2 o1 o2 x0 x1 sim sim'
        (IN: interp_prop_oomTF b1 b2 o1 o2 sim x0 x1)
        (LE: sim <2= sim'):
    interp_prop_oomTF b1 b2 o1 o2 sim' x0 x1.
  Proof using.
    intros. induction IN; eauto.
  Qed.

  Hint Resolve interp_prop_oomTF_mono : paco.

  Definition interp_prop_oomT_ b1 b2 o1 o2 sim (t0 : itree _ R1) (t1 : itree _ R2) :=
    interp_prop_oomTF b1 b2 o1 o2 sim (observe t0) (observe t1).
  Hint Unfold interp_prop_oomT_ : core.

  Lemma interp_prop_oomT__mono b1 b2 o1 o2 : monotone2 (interp_prop_oomT_ b1 b2 o1 o2).
  Proof using.
    do 2 red. intros. eapply interp_prop_oomTF_mono; eauto.
  Qed.
  Hint Resolve interp_prop_oomT__mono : paco.

  Lemma interp_prop_oomT_idclo_mono: monotone2 (@id (itree E R1 -> itree F R2 -> Prop)).
  Proof using. unfold id. eauto. Qed.
  Hint Resolve interp_prop_oomT_idclo_mono : paco.

  (* Definition 5.2 *)
  Definition interp_prop_oom' b1 b2 o1 o2 :
    itree _ R1 -> PropT _ R2 :=
    paco2 (interp_prop_oomT_ b1 b2 o1 o2) bot2.

  Definition interp_prop_oom_r :
    itree _ R1 -> PropT _ R2 :=
    interp_prop_oom' true true false true.

  Definition interp_prop_oom_l :
    itree _ R1 -> PropT _ R2 :=
    interp_prop_oom' true true true false.

  #[global] Instance interp_prop_oom_eq_itree_Proper_impl_ :
    forall (x : _ R1), Proper (eq ==> eq ==> eq ==> eq ==> eq_itree eq ==> impl) (fun b1 b2 o1 o2 => interp_prop_oom' b1 b2 o1 o2 x).
  Proof using.
    repeat intro; subst. eapply bisimulation_is_eq in H3; subst; eauto.
  Qed.

  #[global] Instance interp_prop_oom_eq_itree_Proper_impl :
    Proper (eq ==> eq ==> eq ==> eq ==> eq_itree eq ==> eq_itree eq ==> impl) interp_prop_oom'.
  Proof using.
    repeat intro; subst.
    eapply bisimulation_is_eq in H3, H4; subst; eauto.
  Qed.

  #[global] Instance interp_prop_oom_eq_itree_Proper :
    Proper (eq ==> eq ==> eq ==> eq ==> eq_itree eq ==> eq_itree eq ==> iff) interp_prop_oom'.
  Proof using.
    split; intros; subst; [rewrite <- H3, <- H4 | rewrite H3, H4]; auto.
  Qed.

  #[global] Instance interp_prop_oom_eq_itree_Proper_flip_impl :
    Proper (eq ==> eq ==> eq ==> eq ==> eq_itree eq ==> eq_itree eq ==> flip impl) interp_prop_oom'.
  Proof using.
    pose proof interp_prop_oom_eq_itree_Proper as PROP.
    unfold Proper, respectful in *.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2 x3 y3 H3 x4 y4 H4; subst.
    do 2 red. intros INTERP.
    eapply PROP; eauto.
  Qed.

  Lemma interp_prop_oom_inv_tau_r (t0 : _ R1) t1 b2 o1 o2:
    interp_prop_oom' true b2 o1 o2 t0 (Tau t1) ->
    interp_prop_oom' true b2 o1 o2 t0 t1.
  Proof using All.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t0).
    remember (observe t0); remember (TauF t1).
    revert t0 Heqi t1 Heqi0.
    induction H; intros; inv Heqi0; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_prop_oomTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_prop_oomTF.
      punfold IHinterp_prop_oomTF.
    - rewrite <- itree_eta. pstep; auto.
    - apply bisimulation_is_eq in HT1.
      subst.
      cbn.
      pstep; red; cbn.
      observe_vis.
      eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
      reflexivity.
    - rewrite itree_eta in HT1.
      rewrite H0 in HT1.
      pinversion HT1; cbn in *; subst.
      inv CHECK0.
    - pstep; eapply Interp_Prop_OomT_Vis; eauto.
      destruct k_spec_wellformed.
      eapply k_spec_Proper0.
      setoid_rewrite <- tau_eutt.
      rewrite <- H0.
      reflexivity.
      rewrite <- itree_eta_.
      auto.
  Qed.

  Lemma interp_prop_oom_inv_tau_l (t0 : _ R1) t1 b1 o1 o2:
    interp_prop_oom' b1 true o1 o2 (Tau t0) t1 ->
    interp_prop_oom' b1 true o1 o2 t0 t1.
  Proof using.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t1).
    remember (TauF t0); remember (observe t1).
    revert t0 Heqi t1 Heqi0.
    induction H; intros; inv Heqi; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - rewrite <- itree_eta. pstep; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_prop_oomTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_prop_oomTF.
      punfold IHinterp_prop_oomTF.
    - rewrite itree_eta in HT1; rewrite H0 in HT1; eapply eqit_inv in HT1; contradiction.
    - apply eqitree_inv_Vis_r in HT1 as [k' [VIS K]].
      rewrite VIS.
      pstep; red; cbn.
      change (VisF (subevent A e) k') with (observe (Vis (subevent A e) k')).
      eapply Interp_Prop_OomT_Vis_OOM_R; auto.
      reflexivity.
  Qed.

  Lemma interp_prop_oom_inv_tau (t0 : _ R1) t1 o1 o2:
    interp_prop_oom' true true o1 o2 (Tau t0) (Tau t1) ->
    interp_prop_oom' true true o1 o2 t0 t1.
  Proof using All.
    intros H.
    apply interp_prop_oom_inv_tau_l in H.
    apply interp_prop_oom_inv_tau_r in H; auto.
  Qed.

End interp_prop_oom.

Arguments interp_prop_oom_r {_ _ _ _ _} _ {_ _}.
Arguments interp_prop_oom_l {_ _ _ _ _} _ {_ _}.
Arguments interp_prop_oom' {_ _ _ _ _} _ {_ _}.

Hint Constructors interp_prop_oomTF : core.
Hint Resolve interp_prop_oomTF_mono : paco.
Hint Unfold interp_prop_oomT_ : core.
Hint Resolve interp_prop_oomT__mono : paco.
Hint Resolve interp_prop_oomT_idclo_mono : paco.

Ltac observe_vis_r :=
  match goal with
  | |- interp_prop_oomTF _ _ _ _ _ _ _ _ _ (VisF ?e ?k) =>
      change (VisF e k) with (observe (Vis e k))
  end.

Hint Constructors interp_prop_oomTF : INTERP_PROP_OOM.
Hint Extern 1 (Vis _ _ ≅ Vis _ _) => reflexivity : INTERP_PROP_OOM.
Hint Extern 5 (interp_prop_oomTF _ _ _ _ _ _ _ _
                 _ (VisF _ _)) => observe_vis : INTERP_PROP_OOM.

Ltac solve_interp_prop_oom :=
  eauto with INTERP_PROP_OOM.
#[global] Instance interp_prop_oom_Proper_eq :
    forall (E F OOM : Type -> Type) (h_spec : forall T : Type, E T -> PropT F T) (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop)
      `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    R (RR : R -> R -> Prop) (HR: Reflexive RR) (HT : Transitive RR) `{OOM -< E} `{OOM -< F},
    Proper (eq ==> eq ==> @eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_prop_oom' E F OOM _ _ h_spec _ _ RR k_spec true true).
Proof using.
  intros E F OOM h_spec k_spec KSWF R RR REFL TRANS OOME OOMF.
  intros o1 o1' O1 o2 o2' O2 y y' EQ x x' EQ' H. subst.
  punfold H; punfold EQ; red in H; red in EQ; cbn in *.
  revert_until o2'.
  pcofix CIH.
  intros x x' EQ y H.
  remember (observe x); remember (observe y).
  pstep. red. genobs_clear x' ox'.
  revert x Heqi y Heqi0 EQ.
  (* induct on interp_prop_oom *)
  rename i into xo, i0 into yo.
  induction H; subst; pclearbot; intros.
  - rewrite <- Heqi0.
    remember (RetF (E:= E) r1).
    hinduction EQ before REL; intros; inv Heqi1; inv Heqi; intros.
    + constructor; eauto.
    + constructor; eauto.

  - rewrite <- Heqi0.
    rewrite <- Heqi. rename xo into ot3.
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }

    rename EQ into INR.
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 H]; rewrite H.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      rewrite H in INR.
      assert (eutt RR (Tau m3) (Tau t1)) by (pstep; eauto).
      2 : punfold HS.
      eapply eqit_inv_Tau in H0. punfold H0.

    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      punfold HS. red in HS.
      pclearbot.
      hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * subst. remember (RetF r2) as ot.
        hinduction HS before r1; intros; inv Heqot.
        -- econstructor; eauto.
        -- econstructor; eauto.
        -- rewrite itree_eta in HT1; rewrite H0 in HT1; apply eqit_inv in HT1; inv HT1.
        -- pinversion HT1; subst_existT.
           ++ change (VisF (subevent A e) k3) with (observe (Vis (subevent A e) k3)).
              eapply Interp_Prop_OomT_Vis_OOM_R; auto.
              reflexivity.
           ++ inv CHECK1.
      * remember (VisF e k2) as ot.
        hinduction HS before CIH; intros; try discriminate; eauto.
        -- inv CHECK.
           rewrite itree_eta in HT1.
           rewrite Heqot in HT1.
           punfold HT1; red in HT1; cbn in HT1.
           dependent induction HT1.
           observe_vis; solve_interp_prop_oom.
        -- pose proof @Interp_Prop_OomT_Vis.
           inversion Heqot; repeat subst_existT.
           eapply H; eauto.
           intros. right.
           eapply CIH; eauto.
           specialize (REL a). pclearbot. punfold REL.
           specialize (HK _ H0). pclearbot.
           punfold HK.
      * eapply IHREL; eauto. pstep_reverse.
        assert (@interp_prop_oom' E F OOM OOME OOMF h_spec R R RR k_spec true true o1' o2' (Tau t2) t0) by (pstep; auto).
        apply interp_prop_oom_inv_tau_l in H. punfold H.
  - specialize (IHinterp_prop_oomTF _ Heqi _ Heqi0).
    assert (eutt RR (go xo) t1).
    { rewrite <- (tau_eutt t1); pstep; auto. }
    punfold H0.
  - rewrite <- Heqi0.
    constructor; auto.
  - inv CHECK.
    punfold HT1; red in HT1; cbn in HT1.
    dependent induction HT1; subst.
    rewrite <- x in EQ.
    dependent induction EQ.
    + rewrite <- x.
      observe_vis; solve_interp_prop_oom.
    + rewrite <- x.
      solve_interp_prop_oom.
  - rewrite <- Heqi0. rewrite itree_eta in HT1. rewrite <- Heqi.
    clear x Heqi.
    pinversion HT1; subst_existT.
    + change (VisF (subevent A e) k3) with (observe (Vis (subevent A e) k3)).
      eapply Interp_Prop_OomT_Vis_OOM_R; auto.
      reflexivity.
    + inv CHECK0.
  - rewrite Heqi in EQ.
    remember (VisF e k1).
    hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; inv Heqi.
    + dependent destruction H2.
      eapply Interp_Prop_OomT_Vis; eauto.
      intros. specialize (HK _ H); pclearbot.
      right; eapply CIH; [ | punfold HK].
      specialize (REL a).
      punfold REL.

      eapply KSWF.
      rewrite itree_eta.
      rewrite <- Heqi0.
      rewrite <- itree_eta.
      reflexivity.
      auto.
    + econstructor; eauto.
Qed.

#[global] Instance interp_prop_oom_eutt_Proper_impl_ :
  forall {E F OOM h_spec R1 R2 RR o1 o2}
    {k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop}
    `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    `{OOME: OOM -< E} `{OOMF: OOM -< F} (x : _ R1), Proper (eutt eq ==> impl) (@interp_prop_oom' E F OOM OOME OOMF h_spec R1 R2 RR k_spec true true o1 o2 x).
Proof using.
  repeat intro. red in H0.
  punfold H; punfold H0; red in H; cbn in *.
  revert_until OOMF.
  pcofix CIH.
  intros x y y' EQ H.
  red in H.
  pstep. red.
  remember (observe x); remember (observe y).
  revert x Heqi y Heqi0 EQ.
  (* induct on interp_prop_oom *)
  rename i into xo, i0 into yo.
  induction H; subst; pclearbot; intros.
  - remember (RetF (E:= F) r2).
    induction EQ; inv Heqi1; intros.
    + constructor; auto.
    + constructor; auto.

  - remember (observe y') as ot3.
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }

    rename EQ into INR.
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; rewrite H.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      rewrite H in INR.
      assert (Tau t2 ≈ Tau m3). pstep; auto.
      eapply eqit_inv_Tau in H0. punfold H0.
      punfold HS.

    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      punfold HS. red in HS.
      pclearbot.
      hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * subst. remember (RetF r2) as ot.
        eapply interp_prop_oomTF_mono; eauto.
        intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
      * remember (VisF e k1) as ot.
        hinduction HS before CIH; intros; try discriminate; eauto.
        -- rewrite itree_eta in HT1.
           rewrite Heqot in HT1.
           pinversion HT1; repeat subst_existT.
           change (VisF (subevent A e) k0) with (observe (Vis (subevent A e) k0)).
           eapply Interp_Prop_OomT_Vis_OOM_R; auto.
           reflexivity.
        -- change (VisF e0 k3) with (observe (Vis e0 k3)).
           eapply Interp_Prop_OomT_Vis; eauto.
           intros.
           left. specialize (HK _ H). pclearbot.
           eapply paco2_mon; eauto. intros; inv PR.
           eapply KSWF in KS.
           2: {
             rewrite itree_eta.
             rewrite Heqot.
             assert (Vis e0 k3 ≈ Vis e0 k0).
             { pstep; red; cbn.
               constructor.
               intros v.
               specialize (REL v).
               red.
               pclearbot.
               left.
               eapply Symmetric_eqit_eq;
                 auto.
             }
             apply H1.
           }

           eauto.
      * eapply IHREL; eauto. pstep_reverse.
        assert (@interp_prop_oom' E F OOM OOME OOMF h_spec R1 R2 RR k_spec true true o1 o2 t0 (Tau t1)) by (pstep; auto).
        apply interp_prop_oom_inv_tau_r in H. punfold H.
        eauto.
  - constructor; auto.
    specialize (IHinterp_prop_oomTF _ eq_refl _ Heqi0 EQ). auto.
  - remember (TauF t2) as ot. clear Heqi0 y.
    hinduction EQ before CIH; intros; try inversion Heqot; pclearbot; subst; eauto.
    punfold REL.
    eapply IHinterp_prop_oomTF; eauto.
    constructor; eauto.
    assert (Tau t0 ≈ t2). { pstep; auto. }
    apply eqit_inv_Tau_l in H1; punfold H1.
    eapply IHinterp_prop_oomTF; eauto.
    constructor; eauto.
  - econstructor; eauto.
  - rewrite itree_eta in HT1.
    generalize dependent OOM.
    dependent induction EQ; intros; subst.
    + try rewrite <- x1 in HT1;
        pinversion HT1; repeat subst_existT.
    + try rewrite <- x1 in HT1;
        pinversion HT1; repeat subst_existT.
      inv CHECK0.
    + rewrite <- x.
      rewrite <- x1 in HT1.
      pinversion HT1; repeat subst_existT.
      change (VisF (subevent A e0) k0) with (observe (Vis (subevent A e0) k0)).
      eapply Interp_Prop_OomT_Vis_OOM_R; auto.
      reflexivity.
    + try rewrite <- x in HT1.
      (* Not sure why, but pinversion HT1 loops here *)
      apply eqitree_inv_Vis_r in HT1 as [k' [VIS K]].
      cbn in VIS.
      inversion VIS.
    + rewrite <- x.
      red in HT1; cbn in HT1.
      constructor; auto.
      eapply IHEQ; eauto.
  - rewrite Heqi0 in EQ.
    eapply KSWF in KS.
    2: {
      rewrite itree_eta.
      rewrite Heqi0.
      rewrite <- itree_eta.
      reflexivity.
    }

    eapply Interp_Prop_OomT_Vis; eauto.
    intros; eauto.
    specialize (HK _ H). pclearbot.
    left. eapply paco2_mon; intros; eauto.
    inv PR. assert (y ≈ y') by (pstep; auto).
    eapply KSWF.
    rewrite <- H. reflexivity.
    eauto.
Qed.

#[global] Instance interp_prop_oom_eutt_Proper_impl :
  forall {E F OOM h_spec R1 R2 RR}
    (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop)
    `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    `{OOME: OOM -< E} `{OOMF: OOM -< F},
  Proper (eq ==> eq ==> eutt eq ==> eutt eq ==> impl) (@interp_prop_oom' E F OOM OOME OOMF h_spec R1 R2 RR k_spec true true).
Proof using.
  intros E F OOM h_spec R1 R2 RR k_spec KSWF OOME OOMF.
  intros o1 o1' O1 o2 o2' O2' y y' EQ x x' EQ' H; subst.
  rewrite <- EQ'. clear x' EQ'.
  punfold H; punfold EQ; red in H; red in EQ; cbn in *.
  revert_until o2'.
  pcofix CIH.
  intros x x' EQ y H.
  remember (observe x); remember (observe y).
  pstep. red. genobs_clear x' ox'.
  revert x Heqi y Heqi0 EQ.
  (* induct on interp_prop_oom *)
  rename i into xo, i0 into yo.
  induction H; subst; pclearbot; intros.
  - rewrite <- Heqi0.
    remember (RetF (E:= E) r1).
    induction EQ; inv Heqi1; intros.
    + constructor; auto.
    + constructor; auto.

  - rewrite <- Heqi0.
    rename ox' into ot3.
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros; inv H. }

    rename EQ into INR.
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; rewrite H.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      rewrite H in INR.
      assert (Tau t1 ≈ Tau m3). pstep; auto.
      eapply eqit_inv_Tau in H0. punfold H0.
      punfold HS.

    + inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor; eauto.
      punfold HS. red in HS.
      pclearbot.
      hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * subst. remember (RetF r2) as ot.
        eapply interp_prop_oomTF_mono; eauto.
        intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
      * remember (VisF e k1) as ot.
        hinduction HS before CIH; intros; try discriminate; eauto.
        -- inv CHECK.
           rewrite itree_eta in HT1.
           rewrite Heqot in HT1.
           punfold HT1; red in HT1; cbn in HT1.
           dependent induction HT1; subst.
           observe_vis; solve_interp_prop_oom.
        -- inv Heqot.
           dependent destruction H1.
           eapply Interp_Prop_OomT_Vis; eauto.
           intros. right.
           eapply CIH; eauto.
           specialize (REL a). pclearbot. punfold REL.
           specialize (HK _ H). pclearbot.
           punfold HK.
      * eapply IHREL; eauto. pstep_reverse.
        assert (@interp_prop_oom' E F OOM OOME OOMF h_spec R1 R2 RR k_spec true true o1' o2' (Tau t0) t2) by (pstep; auto).
        apply interp_prop_oom_inv_tau_l in H. punfold H.
  - specialize (IHinterp_prop_oomTF _ eq_refl _ Heqi0).
    assert (t1 ≈ go ox').
    { rewrite <- tau_eutt; pstep; auto. }
    punfold H0.
  - rewrite <- Heqi0.
    constructor; auto. eapply IHinterp_prop_oomTF; eauto.
  - inv CHECK.
    punfold HT1; red in HT1; cbn in HT1.
    dependent induction HT1; subst.
    rewrite <- x in EQ.
    dependent induction EQ.
    + observe_vis; solve_interp_prop_oom.
    + solve_interp_prop_oom.
  - rewrite <- Heqi0. rewrite itree_eta in HT1.
    clear x Heqi.
    pinversion HT1; subst_existT.
    + change (VisF (subevent A e) k3) with (observe (Vis (subevent A e) k3)).
      eapply Interp_Prop_OomT_Vis_OOM_R; auto.
      reflexivity.
    + inv CHECK0.
  - rewrite Heqi in EQ.
    hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; inv Heqi.
    + dependent destruction H1.
      eapply Interp_Prop_OomT_Vis; eauto.
      intros. specialize (HK _ H); pclearbot.
      right; eapply CIH; [ | punfold HK].
      specialize (REL a).
      punfold REL.
      eapply KSWF.
      rewrite itree_eta, <- Heqi0, <- itree_eta.
      reflexivity.
      auto.
    + econstructor; eauto.
Qed.

#[global] Instance interp_prop_oom_eutt_Proper :
  forall {E F OOM h_spec R1 R2 RR}
    (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop)
    `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    `{OOME: OOM -< E} `{OOMF: OOM -< F},
  Proper (eq ==> eq ==> eutt eq ==> eutt eq ==> iff) (@interp_prop_oom' E F OOM OOME OOMF h_spec R1 R2 RR k_spec true true).
Proof using.
  split; intros; subst; [rewrite <- H1, <- H2 | rewrite H1, H2]; auto.
Qed.

#[global] Instance interp_prop_oom_l_eutt_Proper :
  forall {E F OOM h_spec R1 R2 RR}
    (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop)
    `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    `{OOME: OOM -< E} `{OOMF: OOM -< F},
    Proper (eutt eq ==> eutt eq ==> iff) (@interp_prop_oom_l E F OOM OOME OOMF h_spec R1 R2 RR k_spec).
Proof using.
  split; intros; subst.
  - eapply interp_prop_oom_eutt_Proper.
    6: apply H1.
    all: eauto; symmetry; eauto.
  - eapply interp_prop_oom_eutt_Proper.
    6: apply H1.
    all: eauto; symmetry; eauto.
Qed.

#[global] Instance interp_prop_oom_r_eutt_Proper :
  forall {E F OOM h_spec R1 R2 RR}
    (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop)
    `{KSWF : @k_spec_WF _ _ h_spec k_spec}
    `{OOME: OOM -< E} `{OOMF: OOM -< F},
    Proper (eutt eq ==> eutt eq ==> iff) (@interp_prop_oom_r E F OOM OOME OOMF h_spec R1 R2 RR k_spec).
Proof using.
  split; intros; subst.
  - eapply interp_prop_oom_eutt_Proper.
    6: apply H1.
    all: eauto; symmetry; eauto.
  - eapply interp_prop_oom_eutt_Proper.
    6: apply H1.
    all: eauto; symmetry; eauto.
Qed.

Section interp_prop_oom_extra.

  Context {E F OOM : Type -> Type} `{OOME: OOM -< E} `{OOMF: OOM -< F}.
  Context (h : E ~> PropT F).
  Context {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (k_spec : forall T R2, E T -> itree F T -> (T -> itree F R2) -> itree F R2 -> Prop).
  Context `{KSWF : @k_spec_WF _ _ h k_spec}.

  (* TODO: This got broken with k_spec *)
  (* Lemma interp_prop_oom_clo_bind {U} b1 b2 o1 o2 t1 t2 k1 k2 *)
  (*       (EQT: @interp_prop_oom' E F OOM _ _ h U _ eq k_spec b1 b2 o1 o2 t1 t2) *)
  (*       (EQK: forall u1 u2, eq u1 u2 -> @interp_prop_oom' E F OOM _ _ h _ _ eq k_spec b1 b2 o1 o2 (k1 u1) (k2 u2)): *)
  (*   @interp_prop_oom' E F OOM _ _ h _ _ eq k_spec b1 b2 o1 o2 (ITree.bind t1 k1) (ITree.bind (U := U) t2 k2). *)
  (* Proof using. *)
  (*   revert_until o2. *)

  (*   pcofix CIH. *)
  (*   intros. *)
  (*   punfold EQT. *)
  (*   red in EQT. *)

  (*   assert (ITree.bind t1 k1 = *)
  (*             match observe t1 with *)
  (*             | RetF r => k1 r *)
  (*             | TauF t0 => Tau (ITree.bind t0 k1) *)
  (*             | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k1) *)
  (*             end). *)
  (*   { apply bisimulation_is_eq; rewrite unfold_bind; reflexivity. } *)
  (*   rewrite H; clear H. *)

  (*   assert (ITree.bind t2 k2 = *)
  (*             match observe t2 with *)
  (*             | RetF r => k2 r *)
  (*             | TauF t0 => Tau (ITree.bind t0 k2) *)
  (*             | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k2) *)
  (*             end). *)
  (*   { apply bisimulation_is_eq; rewrite unfold_bind; reflexivity. } *)
  (*   rewrite H; clear H. *)

  (*   pstep. *)
  (*   induction EQT; eauto; pclearbot. *)
  (*   - specialize (EQK _ _ REL). *)
  (*     punfold EQK. *)
  (*     eapply interp_prop_oomTF_mono. 1 : eapply EQK. all : eauto. *)
  (*     intros. pclearbot. left. *)
  (*     eapply paco2_mon; eauto. *)
  (*     intros; contradiction. *)
  (*   - constructor. right. *)
  (*     specialize (CIH _ _ _ _ HS EQK). *)
  (*     eauto. *)
  (*   - econstructor; auto. *)
  (*   - econstructor; auto. *)
  (*   - inv CHECK. *)
  (*     punfold HT1; red in HT1; cbn in HT1. *)
  (*     dependent induction HT1; subst. *)
  (*     rewrite <- x. *)
  (*     red. *)
  (*     solve_interp_prop_oom. *)
  (*   - pinversion HT1; subst_existT. *)
  (*     + eapply Interp_Prop_OomT_Vis_OOM_R; auto. *)
  (*       reflexivity. *)
  (*     + inv CHECK0. *)
  (*   - eapply Interp_Prop_OomT_Vis; eauto. *)
  (*     intros; eauto. right. eapply CIH; eauto. *)
  (*     specialize (HK _ H). pclearbot. eapply HK; eauto. *)
  (*     eapply KSWF. *)
  (*     rewrite <- unfold_bind. *)
  (*     eapply eutt_clo_bind; eauto. intros; eauto. subst; reflexivity. *)
  (*     intros u1 u2 H; subst. *)
  (*     reflexivity. *)
  (*     destruct KSWF. *)
  (*     eapply k_spec_Correct0; eauto. *)
  (*     setoid_rewrite <- Eqit.bind_bind. *)
  (*     eapply eutt_clo_bind; eauto. *)
  (*     intros; eauto. subst; reflexivity. *)
  (*     setoid_rewrite <- bind_bind. *)
  (* Qed. *)

  Lemma interp_prop_oom_mono:
    forall (R : Type)
      RR RR' b1 b2 o1 o2 t1 t2,
      (RR <2= RR') ->
      interp_prop_oom' h RR k_spec b1 b2 o1 o2 t1 t2 (OOME:=OOME) ->
      interp_prop_oom' h (F := F) (R1 := R1) (R2 := R2) RR' k_spec b1 b2 o1 o2 t1 t2 (OOME:=OOME).
  Proof using.
    intros ? ? ? ? ? ? ?.
    pcofix self. pstep. intros u v ? euv. punfold euv.
    red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
    eapply Interp_Prop_OomT_Vis; eauto.
    intros. specialize (HK _ H). pclearbot.
    right. eapply self; eauto.
  Qed.

  (* Not true anymore because things get flipped by eq1 and OOM_R *)
  (* (* Figure 7: Interpreter law for Ret *) *)
  (* Lemma interp_prop_oom_ret : *)
  (*   forall R (r : R), *)
  (*     (interp_prop_oom (F := F) (OOME:=OOME) h eq (ret r) ≈ ret r)%monad. *)
  (* Proof using. *)
  (*   intros. *)
  (*   repeat red. *)
  (*   split; [| split]. *)
  (*   - intros. split; intros. *)
  (*     + punfold H0. red in H0; cbn in H0. *)
  (*       punfold H; red in H. *)
  (*       remember (RetF r); remember (observe x). *)
  (*       revert x Heqi0 H Heqi. *)
  (*       dependent induction H0; intros; try inv Heqi; subst; auto. *)
  (*       * intros; subst; cbn. *)
  (*         symmetry; pstep; auto. *)
  (*       * eapply IHinterp_prop_oomTF; eauto. *)
  (*         assert (Tau t2 ≈ y) by (pstep; auto). rewrite tau_eutt in H1. *)
  (*         punfold H1; auto. *)
  (*       * rewrite itree_eta in HT1; rewrite H1 in HT1; apply eqit_inv in HT1; contradiction. *)
  (*       * cbn. *)
  (*         red. *)
  (*         red. *)
  (*         pinversion HT1; subst_existT. *)
  (*         -- rewrite <- H1 in H. *)
  (*            inversion H; subst_existT. *)
  (*            ++ red in HT1. *)
  (*               rewrite <- H1 in HT1. *)
  (*               cbn in HT1. inversion HT1; subst_existT. *)
  (*               exfalso. *)
  (*         pstep; red. *)
  (*         rewrite itree_eta in HT1. *)
  (*         inversion H; subst; *)
  (*           try rewrite <- H1 in HT1. *)
  (*         -- pinversion HT1. *)
  (*         -- apply eqitree_inv_Vis_r in HT1 as [k' [VIS K]]. *)
  (*            inv VIS. *)
  (*         -- pinversion HT1. repeat subst_existT. *)
  (*            exfalso. *)
  (*            cbn. *)

             
  (*            eapply Interp_Prop_OomT_Vis_OOM_L; auto. *)
  (*           apply eq_itree_inv_vis_r in HT1. *)
  (*         inv  *)
  (*         constructor. *)
          
  (*     + do 2 red in H0. rewrite <- H in H0. clear H. *)
  (*       punfold H0; red in H0; cbn in H0. *)
  (*       pstep; red; cbn. *)
  (*       remember (observe x); remember (RetF r). *)
  (*       revert x r Heqi Heqi0. clear y. *)
  (*       induction H0; intros; try inv Heqi0; subst; auto. *)
  (*       constructor; auto; eapply IHeqitF; eauto. *)
  (*   - do 3 red. intros; split; intros; [rewrite <- H | rewrite H]; auto. *)
  (*   - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption. *)
  (* Qed. *)

  (* TODO: broken with k_spec *)
  (* Lemma interp_prop_oom_bind_refine: *)
  (*     forall o1 o2  (t : itree E R1) (k : R1 -> itree E R2) (y : itree F R2), *)
  (*       (x0 <- interp_prop_oom' (OOME:=OOME) h eq k_spec true true o1 o2 t;; interp_prop_oom' (OOME:=OOME) h eq k_spec true true o1 o2 (k x0)) y -> *)
  (*       interp_prop_oom' (OOME:=OOME) h eq k_spec true true o1 o2 (x <- t;; k x) y. *)
  (* Proof using. *)
  (*   intros o1 o2 t k y H0. *)
  (*   destruct H0 as (x0&x1&?&?&?). *)
  (*   rewrite H0. clear H0 y. *)
  (*   rename x0 into t', x1 into k'. *)
  (*   setoid_rewrite unfold_bind. *)
  (*   match goal with *)
  (*   | |- interp_prop_oom' _ _ _ _ _ _ _ ?l ?r => remember l; remember r *)
  (*   end. *)
  (*   revert_until o2. pcofix CIH. intros. *)
  (*   red in H0. *)
  (*   punfold H0; red in H0; cbn in H0. *)
  (*   remember (observe t); remember (observe t'). *)
  (*   setoid_rewrite (itree_eta t') in H1. *)
  (*   revert t t' k k' Heqi1 Heqi2 H1 i i0 Heqi Heqi0. *)
  (*   induction H0; intros. *)

  (*   - subst; eauto. *)
  (*     assert (Returns r2 t'). *)
  (*     { rewrite itree_eta; rewrite <- Heqi2; constructor; reflexivity. } *)
  (*     setoid_rewrite <- itree_eta in H1. *)
  (*     specialize (H1 _ H). eapply paco2_mon. punfold H1. *)
  (*     intros; inv PR. *)

  (*   - (* coinductive tau *) *)
  (*     pstep. subst. constructor. right. eapply CIH. eauto. pclearbot. *)
  (*     3,4:eapply bisimulation_is_eq; rewrite unfold_bind; reflexivity. *)
  (*     pclearbot. punfold HS. pstep. eapply HS. *)
  (*     intros; eapply H1. rewrite (itree_eta t'). *)
  (*     rewrite <- Heqi2. eapply ReturnsTau; eauto. reflexivity. *)
  (*   - rewrite Heqi. pstep. constructor; auto. *)
  (*     specialize (IHinterp_prop_oomTF t1 t' k k' eq_refl Heqi2 H1 (bind t1 k)). *)

  (*     assert (H' : x <- t1;; k x = *)
  (*                 match observe t1 with *)
  (*                 | RetF r => k r *)
  (*                 | TauF t => Tau (ITree.bind t k) *)
  (*                 | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k) *)
  (*                 end). *)
  (*     { *)
  (*       apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. *)
  (*     } *)
  (*     specialize (IHinterp_prop_oomTF i0 H' Heqi0). *)
  (*     punfold IHinterp_prop_oomTF. *)
  (*   - rewrite Heqi0. pstep. constructor; auto. *)

  (*     specialize (IHinterp_prop_oomTF _ _ k k' Heqi1 eq_refl). *)

  (*     assert (forall a , Returns a t2 -> interp_prop_oom' (OOME:=OOME) h eq k_spec true true o1 o2 (k a) (k' a)). *)
  (*     { intros; eapply H1. rewrite (itree_eta t'); rewrite <- Heqi2. *)
  (*       rewrite tau_eutt; auto. rewrite <- itree_eta; auto. } *)

  (*     setoid_rewrite <- itree_eta in IHinterp_prop_oomTF. *)
  (*     specialize (IHinterp_prop_oomTF H). *)

  (*     assert (H' : x <- t2;; k' x = *)
  (*                 match observe t2 with *)
  (*                 | RetF r => k' r *)
  (*                 | TauF t => Tau (ITree.bind t k') *)
  (*                 | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k') *)
  (*                 end). *)
  (*     { *)
  (*       apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. *)
  (*     } *)
  (*     specialize (IHinterp_prop_oomTF _ _ Heqi H'). *)
  (*     punfold IHinterp_prop_oomTF. *)

  (*   - inv CHECK. *)
  (*     punfold HT1; red in HT1; cbn in HT1. *)
  (*     dependent induction HT1; subst. *)
  (*     rewrite <- x. *)
  (*     solve_interp_prop_oom. *)

  (*   - subst. *)
  (*     punfold HT1. *)
  (*     red in HT1. cbn in HT1. *)
  (*     remember (VisF (subevent A e) k2). *)
  (*     hinduction HT1 before e; intros; inv Heqi. *)
  (*     + dependent destruction H2. *)
  (*       pclearbot. pstep. *)
  (*       eapply Interp_Prop_OomT_Vis_OOM_R; eauto. *)
  (*       reflexivity. *)
  (*     + inv CHECK.  *)
  (*   - rewrite Heqi, Heqi0; clear Heqi Heqi0. *)
  (*     pstep. eapply Interp_Prop_OomT_Vis; eauto. *)
  (*     intros. specialize (HK _ H); pclearbot. right. *)
  (*     eapply CIH; eauto. *)
  (*     intros; eapply H1; eauto. *)
  (*     rewrite <- Heqi2. rewrite <- itree_eta. *)
  (*     rewrite H0. eapply Returns_bind; eauto. *)
  (*     apply bisimulation_is_eq; rewrite <- unfold_bind; reflexivity. *)
  (*     apply bisimulation_is_eq; setoid_rewrite <- unfold_bind; reflexivity. *)
  (*     setoid_rewrite <- unfold_bind. rewrite H0. setoid_rewrite Eqit.bind_bind; reflexivity. *)
  (* Qed. *)

  Lemma interp_prop_oom_ret_pure :
    forall {T} b1 b2 o1 o2 (RR : relation T) `{REF: Reflexive _ RR} (x : T),
      interp_prop_oom' (F := F) (OOME:=OOME) h RR k_spec b1 b2 o1 o2 (ret x) (ret x).
  Proof using.
    intros.
    generalize dependent x.
    pcofix CIH.
    intros x.
    pstep.
    cbn.
    econstructor.
    reflexivity.
  Qed.
 
  Lemma interp_prop_oom_ret_refine :
    forall {T} b1 b2 o1 o2 (RR : relation T) (x y : T),
      RR x y ->
      interp_prop_oom' (F := F) (OOME:=OOME) h RR k_spec b1 b2 o1 o2 (ret x) (ret y).
  Proof using.
    intros.
    generalize dependent y.
    generalize dependent x.
    pcofix CIH.
    intros x y RRxy.
    pstep.
    cbn.
    econstructor; eauto.
  Qed.

  (* Lemma 5.4: interp_prop_oom_correct - note that the paper presents a slightly simpler formulation where t = t' *)
  Lemma interp_prop_oom_correct_exec:
    forall {R} o1 o2 RR `{Reflexive _ RR} (t : _ R) t' (f : (forall T : Type, E T -> itree F T))
      (HC : handler_correct h f),
      t ≈ t' ->
      interp_prop_oom' (OOME:=OOME) h RR k_spec true true o1 o2 t (interp f t').
  Proof using E F KSWF OOM OOME OOMF h k_spec.
    intros R o1 o2 RR0 H t t' f HC H1.
    setoid_rewrite unfold_interp.
    remember (_interp f (observe t')).
    assert (i ≅ _interp f (observe t')). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    revert t t' i H1 H0.
    pcofix CIH.
    intros t t' i eq ?.
    pstep.
    red.
    punfold eq. red in eq.
    genobs t ot; genobs t' ot'.
    revert i H2 t t' Heqot Heqot'.
    induction eq; intros; subst; pclearbot; auto.
    - punfold H2; inv H2; try inv CHECK.
      constructor; auto.
    - punfold H2; inv H2; try inv CHECK.
      constructor; auto.
      right; eauto. eapply CIH; pclearbot; eauto.
      rewrite <- unfold_interp; auto.
    - cbn in H2.
      eapply Interp_Prop_OomT_Vis; eauto; cycle 1.
      apply HC; reflexivity.

      eapply KSWF.
      rewrite H2; reflexivity.
      destruct KSWF.
      unfold k_spec_correct in *.
      eapply k_spec_Correct0.
      red in HC.
      eapply HC; reflexivity.
      cbn.
      reflexivity.

      intros; subst.
      right. eapply CIH with (t':=Tau (k2 a)).
      rewrite tau_eutt.
      apply REL.
      reflexivity.
    - constructor; auto; eapply IHeq; eauto.
    - cbn in H2.
      apply eqitree_inv_Tau_r in H2.
      destruct H2 as (?&?&?). rewrite unfold_interp in H1.
      specialize (IHeq _ H1 _ _ eq_refl eq_refl).
      rewrite H0. constructor; auto.
  Qed.

  (* Figure 7: interp Trigger law *)
  (* morally, we should only work with "proper" triggers everywhere *)
  (* Lemma interp_prop_oom_trigger : *)
  (*   forall R (e : E R) (h : E ~> PropT (itree F)) (HProper: forall A e, Proper (eutt eq ==> iff) (h A e)), *)
  (*     (interp_prop_oom h eq (trigger e) ≈ h _ e)%monad. *)
  (* Proof using. *)
  (*   intros; red. *)
  (*   split; [| split]; cycle 1. *)
  (*   { do 3 red. intros; split; intros; [rewrite <- H | rewrite H] ; auto. } *)
  (*   { do 3 red. intros. split; intros; cbn in *. *)
  (*     rewrite <- H. assumption. rewrite H; assumption. } *)

  (*   intros; split; intros; *)
  (*     [rewrite <- H | rewrite <- H in H0]; clear H y. *)
  (*   - unfold trigger in H0. red in H0. *)
  (*     punfold H0. red in H0. cbn in H0. *)
  (*     unfold subevent, resum, ReSum_id, Id_IFun, id_ in H0. *)
  (*     remember (VisF e (fun x => Ret x)). *)
  (*     rewrite itree_eta. *)
  (*     remember (observe x). *)
  (*     revert Heqi x Heqi0. *)
      (* induction H0; intros; inv Heqi. *)
      (* + rewrite tau_eutt; rewrite (itree_eta). eapply IHinterp_prop_oomTF; eauto. *)
      (* + dependent destruction H1. *)
      (*   assert (x <- ta ;; k2 x ≈ ta). *)
      (*   { rewrite <- (Eqit.bind_ret_r ta). *)
      (*     apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta). *)
      (*     rewrite Eqit.bind_ret_r. apply eutt_Returns. *)
      (*     intros. destruct H; eauto. subst. specialize (HK _ H0). *)
      (*     pclearbot. *)
      (*     punfold HK; red in HK; cbn in HK. *)
      (*     symmetry. *)
      (*     pstep. red. cbn. *)
      (*     remember (RetF u2); remember (observe (k2 u2)). *)
      (*     assert (go i0 ≈ k2 u2). *)
      (*     { rewrite Heqi1, <- itree_eta; reflexivity. } *)
      (*     clear Heqi0. clear x H. clear k2 KS Heqi1. *)
      (*     revert u2 Heqi H0. *)
      (*     revert ta HTA t2. *)
      (*     induction HK; intros; inv Heqi. *)
      (*     - constructor; auto. *)
      (*     - constructor; eauto. } *)
      (*   rewrite <- H in HTA. red in HC, KC. symmetry in H. *)
      (*   rewrite <- H in HTA. *)
      (*   eapply k_spec_WF_respects_h_spec; eauto. *)
      (*   eapply k_spec_WF_Proper; eauto. rewrite <- itree_eta; reflexivity. *)
      (* - unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_. *)
      (*   red. pstep. eapply Interp_Prop_OomT_Vis with (k2 := (fun x : R => Ret x)); eauto. *)
      (*   + intros; left; pstep; constructor; auto. *)
      (*   + red in KC. eapply KC. eapply HC in H0. eauto. *)
      (*     rewrite bind_ret_r; reflexivity. *)
  (* Admitted. *)

  Lemma interp_prop_oom_ret_inv:
    forall  r1 (t : itree F _) b1 b2 o1 o2,
      interp_prop_oom' (F := F) (OOME:=OOME) h RR k_spec b1 b2 o1 o2 (ret r1) t ->
      (exists r2 , RR r1 r2 /\ t ≈ ret r2) \/
        (exists A (e : OOM A) k, t ≈ vis e k)%type.
  Proof using.
    intros r1 t b1 b2 o1 o2 INTERP.
    punfold INTERP.
    red in INTERP.
    setoid_rewrite itree_eta with (t:=t).
    remember (observe (ret r1)); remember (observe t).
    clear Heqi0.
    induction INTERP; subst; pclearbot; intros.
    - left.
      exists r2.
      cbn in Heqi.
      inv Heqi.
      split; auto.
      cbn.
      reflexivity.
    - inv Heqi.
    - inv Heqi.
    - cbn in INTERP.
      inv INTERP.
      + apply simpobs in H.
        left.
        exists r2; split; auto.
        rewrite H.
        rewrite tau_eutt.
        reflexivity.
      + specialize (IHINTERP eq_refl).
        destruct IHINTERP as [[r2 [RRr1r2 EQ]] | [A [e [k EUTT]]]].
        2: {
          right.
          setoid_rewrite tau_eutt.
          rewrite <- itree_eta in EUTT.
          exists A. exists e. exists k.
          auto.
        }

        left.
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        rewrite tau_eutt.
        reflexivity.
      + setoid_rewrite tau_eutt.
        specialize (IHINTERP eq_refl).
        destruct IHINTERP as [[r2 [RRr1r2 EQ]] | [A' [e' [k' EUTT]]]].
        2: {
          right.
          rewrite <- itree_eta in EUTT.
          exists A'. exists e'. exists k'.
          auto.
        }

        left.
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        reflexivity.
      + setoid_rewrite tau_eutt.
        specialize (IHINTERP eq_refl).
        destruct IHINTERP as [[r2 [RRr1r2 EQ]] | [A' [e' [k' EUTT]]]].
        2: {
          right.
          rewrite <- itree_eta in EUTT.
          exists A'. exists e'. exists k'.
          auto.
        }

        left.
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        reflexivity.
    - inv Heqi.
      rewrite itree_eta in HT1; rewrite H0 in HT1; apply eqit_inv in HT1; contradiction.
    - right.
      setoid_rewrite <- itree_eta.
      exists A. exists e. exists k2.
      rewrite HT1.
      reflexivity.
    - inv Heqi.
  Qed.

  Lemma interp_prop_oom_l_ret_inv:
    forall  r1 (t : itree F _),
      interp_prop_oom_l (F := F) (OOME:=OOME) h RR k_spec (ret r1) t ->
      (exists r2 , RR r1 r2 /\ t ≈ ret r2).
  Proof using.
    intros r1 t INTERP.
    punfold INTERP.
    red in INTERP.
    setoid_rewrite itree_eta with (t:=t).
    remember (observe (ret r1)); remember (observe t).
    clear Heqi0.
    induction INTERP; subst; pclearbot; intros.
    - exists r2.
      cbn in Heqi.
      inv Heqi.
      split; auto.
      cbn.
      reflexivity.
    - inv Heqi.
    - inv Heqi.
    - cbn in INTERP.
      inv INTERP.
      + apply simpobs in H.
        exists r2; split; auto.
        rewrite H.
        rewrite tau_eutt.
        reflexivity.
      + specialize (IHINTERP eq_refl).
        destruct IHINTERP as [r2 [RRr1r2 EQ]].
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        rewrite tau_eutt.
        reflexivity.
      + setoid_rewrite tau_eutt.
        specialize (IHINTERP eq_refl).
        destruct IHINTERP as [r2 [RRr1r2 EQ]].
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        reflexivity.
      + setoid_rewrite tau_eutt.
        specialize (IHINTERP eq_refl).
        destruct IHINTERP as [r2 [RRr1r2 EQ]].
        exists r2; split; auto.
        rewrite <- itree_eta in EQ.
        rewrite EQ.
        reflexivity.
    - inv Heqi.
      rewrite itree_eta in HT1; rewrite H0 in HT1; apply eqit_inv in HT1; contradiction.
    - discriminate.
    - inv Heqi.
  Qed.

End interp_prop_oom_extra.
