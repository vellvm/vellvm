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
     Eq.Eq.

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
     Basics.Monad.

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

Section interp_prop.

  (* Definition 5.3: Handler Correctness *)
  Definition handler_correct {E F} (h_spec: E ~> PropT F) (h: E ~> itree F) :=
    (forall T e ta, ta ≈ h T e <-> h_spec T e ta).

  Lemma case_prop_handler_correct:
    forall {E1 E2 F}
      (h1_spec: E1 ~> PropT F)
      (h2_spec: E2 ~> PropT F)
      (h1: E1 ~> itree F)
      (h2: E2 ~> itree F)
      (C1: handler_correct h1_spec h1)
      (C2: handler_correct h2_spec h2),
      handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
  Proof.
    intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
    unfold handler_correct in *.
    intros T e.
    destruct e. apply C1. apply C2.
  Qed.

  Definition k_spec_correct
             {E F}
             (h: E ~> itree F)
             (k_spec : forall T R (RR: relation R), E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop) : Prop
    := forall T R RR e k2 t2 ta, ta ≈ h _ e -> eutt RR t2 (bind ta k2) -> k_spec T R RR e ta k2 t2.

  Context {E F : Type -> Type}.
  Context {R : Type} (RR : R -> R -> Prop).
  Context (h_spec : E ~> PropT F).
  Context (k_spec : forall T R (RR: relation R), E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop).

  Class k_spec_Proper := {
    k_spec_Proper_ : forall {A R} RR ta k e,
      Proper (eutt eq ==> iff) (k_spec A R RR e ta k);
  }.

  Class k_spec_respects_h_spec := {
    k_spec_respects_h_spec_ : forall {A} RR (ta : itree F _) (k : _ -> itree F _) e x,
      ta ≈ x <- ta ;; k x ->
      k_spec A _ RR e ta k x ->
      h_spec _ e ta ->
      h_spec _ e x }.

  Class k_spec_bind := {
      k_spec_bind_ : forall {A R1 R2} RR UU ta k2 (t2 : itree F _) e (k' : R1 -> itree F R2),
        k_spec A _ UU e ta k2 t2 ->
        k_spec A _ RR e ta (fun x => bind (k2 x) k') (x <- t2 ;; k' x) }.

  Class k_spec_mono := {
      k_spec_mono_ : forall A R RR RR',
        RR <2= RR' ->
        k_spec A R RR <4= k_spec A _ RR' }.

  (* Well-formedness conditions for k_specs *)
  Class k_spec_WF := {
      k_spec_WF_bind: k_spec_bind;
      k_spec_WF_Proper : k_spec_Proper;
      k_spec_WF_respects_h_spec : k_spec_respects_h_spec;
      k_spec_WF_mono : k_spec_mono
    }.

  Context `{k_spec_wellformed : k_spec_WF}.

  Inductive interp_PropTF
            (b1 b2 : bool)
            (vclo : (itree E R -> itree F R -> Prop) -> itree E R -> itree F R -> Prop)
            (sim : itree E R -> itree F R -> Prop)
            : itree' E R -> itree' F R -> Prop :=
  | Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2),
      interp_PropTF b1 b2 vclo sim (RetF r1) (RetF r2)

  | Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_PropTF b1 b2 vclo sim (TauF t1) (TauF t2)

  | Interp_PropT_TauL : forall t1 t2
                          (CHECK: is_true b1)
                          (HS: interp_PropTF b1 b2 vclo sim (observe t1) t2),
      interp_PropTF b1 b2 vclo sim (TauF t1) t2

  | Interp_PropT_TauR : forall t1 t2
                          (CHECK: is_true b2)
                          (HS: interp_PropTF b1 b2 vclo sim t1 (observe t2)),
      interp_PropTF b1 b2 vclo sim t1 (TauF t2)

  | Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R) ta
                         (t2 : itree F R)

                         (k2 : A -> itree F R)

                         (HTA: h_spec A e ta)
                         (HK : forall (a : A), Returns a ta -> vclo sim (k1 a) (k2 a))

                         (KS : k_spec A R RR e ta k2 t2),
      interp_PropTF b1 b2 vclo sim (VisF e k1) (observe t2).

  Hint Constructors interp_PropTF : core.

  Lemma interp_PropTF_mono b1 b2 x0 x1 vclo vclo' sim sim'
        (IN: interp_PropTF b1 b2 vclo sim x0 x1)
        (MON: monotone2 vclo)
        (LEc: vclo <3= vclo')
        (LE: sim <2= sim'):
    interp_PropTF b1 b2 vclo' sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Hint Resolve interp_PropTF_mono : paco.

  Definition interp_PropT_ b1 b2 vclo sim (t0 : itree E R) (t1 : itree F R) :=
    interp_PropTF b1 b2 vclo sim (observe t0) (observe t1).
  Hint Unfold interp_PropT_ : core.

  Lemma interp_PropT__mono b1 b2 vclo (MON: monotone2 vclo) : monotone2 (interp_PropT_ b1 b2 vclo).
  Proof.
    do 2 red. intros. eapply interp_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_PropT__mono : paco.

  Lemma interp_PropT_idclo_mono: monotone2 (@id (itree E R -> itree F R -> Prop)).
  Proof. unfold id. eauto. Qed.
  Hint Resolve interp_PropT_idclo_mono : paco.

  (* Definition 5.2 *)
  Definition interp_prop' b1 b2 :
    itree E R -> PropT F R :=
    paco2 (interp_PropT_ b1 b2 id) bot2.

  Definition interp_prop :
    itree E R -> PropT F R :=
    interp_prop' true true.

  #[global] Instance interp_prop_eq_itree_Proper_impl_ :
    forall (x : _ R ), Proper (eq_itree eq ==> impl) (interp_prop x).
  Proof.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until k_spec_wellformed.
    pcofix CIH.
    intros x y y' EQ H.
    remember (observe x); remember (observe y).
    revert x Heqi y y' Heqi0 EQ.
    (* induct on interp_prop *)
    induction H; subst; pclearbot; intros.
    - inv EQ; [ | inv CHECK].
      pstep. red. rewrite <- Heqi, <- H.
      eauto.
    - inv EQ; try inv CHECK; pclearbot.
      pstep. red. rewrite <- Heqi, <- H.
      constructor. right. eapply CIH; eauto.
      punfold REL. punfold HS.
    - pstep. red. rewrite <- Heqi. constructor; auto.
      specialize (IHinterp_PropTF _ eq_refl _ _ Heqi0 EQ).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi.
      inv EQ; try inv CHECK0; pclearbot.
      constructor; auto. punfold REL.
      specialize (IHinterp_PropTF _ eq_refl _ m2 eq_refl REL).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi.
      econstructor; eauto; cycle 1.
      eapply k_spec_WF_Proper. symmetry.
      assert (t2 ≅ y') by (pstep; auto).
      rewrite <- H. reflexivity. eauto.
      intros. specialize (HK _ H). pclearbot.
      left. eapply paco2_mon; intros; eauto.
      inv PR.
  Qed.

  #[global] Instance interp_prop_eq_itree_Proper_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> impl) interp_prop.
  Proof.
    repeat intro.
    rewrite <- H0. clear H0.
    clear y0. rename H1 into H0. rename y into x'. rename x0 into y.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until k_spec_wellformed.
    pcofix CIH.
    intros x x' EQ y H.
    remember (observe x); remember (observe y).
    revert x x' Heqi y Heqi0 EQ.
    (* induct on interp_prop *)
    induction H; subst; pclearbot; intros.
    - inv EQ; [ | inv CHECK].
      pstep. red. rewrite <- Heqi0, <- H.
      eauto.
    - inv EQ; try inv CHECK; pclearbot.
      pstep. red. rewrite <- Heqi0, <- H.
      constructor. right. eapply CIH; eauto.
      punfold REL. punfold HS.
    - pstep. red. rewrite <- Heqi0.
      inv EQ; try inv CHECK0; pclearbot.
      constructor; auto. punfold REL.
      specialize (IHinterp_PropTF _ _ eq_refl _ eq_refl REL).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi0. constructor; auto.
      specialize (IHinterp_PropTF _ _ Heqi _ eq_refl EQ).
      punfold IHinterp_PropTF.
    - pstep.
      assert (Vis e k1 ≅ x') by (pstep; auto).
      eapply eqit_inv in H. cbn in H.
      destruct (_observe x') eqn: Hx'; inv H.
      red. unfold observe at 1. rewrite Hx'.
      destruct H0. red in H. subst.
      red in H0.
      econstructor; eauto; cycle 1.
      assert (t2 ≈ y).
      { rewrite itree_eta; rewrite Heqi0; rewrite <- itree_eta; reflexivity. }
      eapply k_spec_WF_Proper.
      symmetry in H; apply H.
      exact KS.
      intros. specialize (HK _ H). pclearbot.
      punfold HK.
      right. eapply CIH; eauto.
      specialize (H0 a). punfold H0.
  Qed.

  #[global] Instance interp_prop_eq_itree_Proper :
    Proper (eq_itree eq ==> eq_itree eq ==> iff) interp_prop.
  Proof.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.

  #[global] Instance interp_prop_eq_itree_Proper_flip_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl) interp_prop.
  Proof.
    pose proof interp_prop_eq_itree_Proper as PROP.
    unfold Proper, respectful in *.
    intros x y H x0 y0 H0.
    do 2 red. intros INTERP.
    eapply PROP; eauto.
  Qed.

  Lemma interp_prop_inv_tau_r (t0 : _ R) t1:
    interp_prop t0 (Tau t1) ->
    interp_prop t0 t1.
  Proof.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t0).
    remember (observe t0); remember (TauF t1).
    revert t0 Heqi t1 Heqi0.
    induction H; intros; inv Heqi0; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_PropTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_PropTF.
      punfold IHinterp_PropTF.
    - rewrite <- itree_eta. pstep; auto.
    - pstep; econstructor; eauto. eapply k_spec_WF_Proper; eauto.
      rewrite (itree_eta t2); rewrite H0.
      rewrite tau_eutt; reflexivity.
  Qed.

  Lemma interp_prop_inv_tau_l (t0 : _ R) t1:
    interp_prop (Tau t0) t1 ->
    interp_prop t0 t1.
  Proof.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t1).
    remember (TauF t0); remember (observe t1).
    revert t0 Heqi t1 Heqi0.
    induction H; intros; inv Heqi; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - rewrite <- itree_eta. pstep; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_PropTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_PropTF.
      punfold IHinterp_PropTF.
  Qed.

  Lemma interp_prop_inv_tau (t0 : _ R) t1:
    interp_prop (Tau t0) (Tau t1) ->
    interp_prop t0 t1.
  Proof.
    intros H.
    apply interp_prop_inv_tau_l in H.
    apply interp_prop_inv_tau_r in H; auto.
  Qed.

  #[global] Instance interp_prop_eutt_Proper_impl_ :
    forall (x : _ R), Proper (eutt eq ==> impl) (interp_prop x).
  Proof.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until k_spec_wellformed.
    pcofix CIH.
    intros x y y' EQ H.
    remember (observe x); remember (observe y).
    pstep. red.
    revert x Heqi y Heqi0 EQ.
    (* induct on interp_prop *)
    rename i into xo, i0 into yo.
    induction H; subst; pclearbot; intros.
    - rewrite <- Heqi.
      remember (RetF (E:= F) r2).
      induction EQ; inv Heqi1; intros.
      + constructor; auto.
      + constructor; auto.

    - rewrite <- Heqi.
      remember (observe y') as ot3.
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
          eapply interp_PropTF_mono; eauto.
          intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
        * remember (VisF e k1) as ot.
          hinduction HS before CIH; intros; try discriminate; eauto.
          pose proof @Interp_PropT_Vis.
          change (VisF e0 k3) with (observe (Vis e0 k3)).
          eapply H; eauto.
          intros.
          left. specialize (HK _ H0). pclearbot.
          eapply paco2_mon; eauto. intros; inv PR.
          eapply k_spec_WF_Proper. eapply eqit_Vis. symmetry. pclearbot. eauto.
          eapply k_spec_WF_Proper. Unshelve.
          3 : exact t2.
          rewrite (itree_eta t2), Heqot. eapply eqit_Vis; reflexivity.
          eauto.
        * eapply IHREL; eauto. pstep_reverse.
          assert (interp_prop t0 (Tau t1)) by (pstep; auto).
          apply interp_prop_inv_tau_r in H. punfold H.
    - rewrite <- Heqi. constructor; auto.
      specialize (IHinterp_PropTF _ eq_refl _ Heqi0 EQ). auto.
    - rewrite <- Heqi.
      remember (TauF t2) as ot. clear Heqi0 y.
      hinduction EQ before CIH; intros; try inversion Heqot; pclearbot; subst; eauto.
      punfold REL.
      eapply IHinterp_PropTF; eauto.
      constructor; eauto.
      assert (Tau t0 ≈ t2). { pstep; auto. }
      apply eqit_inv_Tau_l in H1; punfold H1.
    - rewrite <- Heqi.
      econstructor; eauto; cycle 1.
      eapply k_spec_WF_Proper. rewrite Heqi0 in EQ.
      symmetry. pstep; red; eauto.
      eapply k_spec_WF_Proper. 2 : eauto. rewrite itree_eta; rewrite <- Heqi0; rewrite <- itree_eta; reflexivity.
      intros. specialize (HK _ H). pclearbot.
      left. eapply paco2_mon; intros; eauto.
      inv PR.
  Qed.

  #[global] Instance interp_prop_eutt_Proper_impl :
    Proper (eutt eq ==> eutt eq ==> impl) (interp_prop).
  Proof.
    intros y y' EQ x x' EQ' H.
    rewrite <- EQ'. clear x' EQ'.
    punfold H; punfold EQ; red in H; red in EQ; cbn in *.
    revert_until k_spec_wellformed.
    pcofix CIH.
    intros x x' EQ y H.
    remember (observe x); remember (observe y).
    pstep. red. genobs_clear x' ox'.
    revert x Heqi y Heqi0 EQ.
    (* induct on interp_prop *)
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
          eapply interp_PropTF_mono; eauto.
          intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
        * remember (VisF e k1) as ot.
          hinduction HS before CIH; intros; try discriminate; eauto.
          pose proof @Interp_PropT_Vis.
          inversion Heqot. dependent destruction H3.
          eapply H; eauto.
          intros. right. eapply CIH; eauto.
          specialize (REL a). pclearbot. punfold REL.
          specialize (HK _ H0). pclearbot.
          punfold HK.
        * eapply IHREL; eauto. pstep_reverse.
          assert (interp_prop (Tau t0) t2) by (pstep; auto).
          apply interp_prop_inv_tau_l in H. punfold H.
    - specialize (IHinterp_PropTF _ eq_refl _ Heqi0).
      assert (t1 ≈ go ox').
      { rewrite <- tau_eutt; pstep; auto. }
      punfold H0.
    - rewrite <- Heqi0.
      constructor; auto. eapply IHinterp_PropTF; eauto.
    - rewrite <- Heqi0.
      remember (VisF e k1). clear x Heqi.

      hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; subst; eauto.
      dependent destruction H1.
      econstructor; eauto.
      intros; specialize (HK _ H); pclearbot.
      right; eapply CIH; [ | punfold HK].
      specialize (REL a).
      punfold REL.
  Qed.

  #[global] Instance interp_prop_eutt_Proper :
    Proper (eutt eq ==> eutt eq ==> iff) interp_prop.
  Proof.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.
End interp_prop.

Hint Constructors interp_PropTF : core.
Hint Resolve interp_PropTF_mono : paco.
Hint Unfold interp_PropT_ : core.
Hint Resolve interp_PropT__mono : paco.
Hint Resolve interp_PropT_idclo_mono : paco.

#[global] Instance interp_prop_Proper_eq :
  forall (E F : Type -> Type) (h_spec : forall T : Type, E T -> PropT F T)
    (k_spec : forall T R REL,
        E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop)
    R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR),
    Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (interp_prop RR h_spec k_spec).
Proof.
Admitted.

Lemma interp_prop_eqit_clo_wcompat {E R RR h_spec k_spec b1 b2 vclo}
    `{k_spec_WF _ _ h_spec k_spec}
  (MON: monotone2 vclo)
  (CMP: compose (eqitC eq b1 b2) vclo <3= compose vclo (eqitC eq b1 b2)):
  wcompatible2 (@interp_PropT_ E E R RR h_spec k_spec b1 b2 vclo) (eqitC eq b1 b2).
Proof.
  econstructor.
  pmonauto.
  intros.
  destruct PR.
  punfold EQVl.
  punfold EQVr.
  unfold_eqit. red in REL.
  hinduction REL before r; intros; clear t1' t2'; red.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
    constructor. specialize (LERR1 _ _ _ REL0 eq_refl). subst.
    specialize (LERR2 _ _ _ REL eq_refl). subst. auto.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. econstructor. gclo.
    econstructor; eauto with paco.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. constructor; punfold REL.
    eapply IHREL; eauto.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot;constructor; punfold REL.
    eapply IHREL; eauto.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try discriminate Heqx; eauto; inv_Vis.
    pclearbot.
    econstructor; intros; cycle 1.
    eapply MON; cycle 1.
    + intros. apply gpaco2_clo, PR.
    + apply CMP. econstructor. 1, 2, 3: eauto. reflexivity.
      eauto. intros; subst; eauto.
    + assert (t0 ≈ t2).
      { eapply eqit_mon. 4 : pstep; eapply EQVr.
        1, 2: eauto. intros. specialize (LERR2 _ _ _ PR eq_refl). auto. }
      eapply k_spec_WF_Proper; eauto.
    + eauto.
Qed.

Hint Resolve interp_prop_eqit_clo_wcompat : paco.

Inductive interp_prop_Returns_bind_clo {E} {R1 R2} h_spec k_spec b1 b2 (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| pbc_intro_h U (RU : U -> U -> Prop) t1 t2 k1 k2
      (EQV: interp_prop' RU h_spec k_spec b1 b2 t1 t2)
      (REL: forall u1, Returns u1 t1 -> r (k1 u1) (k2 u1))
  : interp_prop_Returns_bind_clo h_spec k_spec b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors interp_prop_Returns_bind_clo: core.

Lemma interp_prop_Returns_clo_bind {E R} (RS : R -> R -> Prop) h_spec k_spec b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
      (ID: id <3= vclo):
  interp_prop_Returns_bind_clo h_spec k_spec b1 b2 <3= gupaco2 (eqit_ (E := E) RS b1 b2 vclo) (eqitC RS b1 b2).
Proof.
Admitted.

Lemma interp_prop_clo_bind {E} R (RR : R -> R -> Prop) h_spec k_spec {U UU} t1 t2 k1 k2
      `{k_spec_WF _ _ h_spec k_spec}
      (EQT: @interp_prop E E U UU h_spec k_spec t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> interp_prop RR h_spec k_spec (k1 u1) (k2 u2)):
  interp_prop RR h_spec k_spec (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  revert_until UU.

  ginit. gcofix CIH.
  intros.
  punfold EQT.
  red in EQT.
  gclo.
  econstructor.
  rewrite unfold_bind; reflexivity.
  rewrite unfold_bind; reflexivity. 2,3: intros; subst; eauto.

  gstep.
  induction EQT; eauto; pclearbot.
  - specialize (EQK _ _ REL).
    punfold EQK.
    eapply interp_PropTF_mono; eauto.
    intros; eauto. pclearbot.
    gfinal. right.
    eapply paco2_mon; eauto.
    intros; contradiction.
  - constructor. gfinal. left.
    specialize (CIH _ _ _ _ H0 HS EQK).
    eauto.
  - econstructor; auto.
  - econstructor; auto.
  - econstructor; eauto.
    + intros. gbase; eapply CIH; eauto.
      specialize (HK _ H). pclearbot; eauto.
    + eapply k_spec_WF_Proper; cycle 1.
      * rewrite <- unfold_bind. reflexivity.
      * pose proof @k_spec_WF_bind as Hbind.
        specialize (Hbind _ _ h_spec k_spec _).
        destruct Hbind.
        eapply k_spec_bind_0; eauto.
      * eauto.
Qed.

From ITree Require Import Eq.EqAxiom.

Lemma interp_prop_clo_bind' {E F} R (RR : R -> R -> Prop) h_spec k_spec {U UU} t1 t2 k1 k2
      `{k_spec_WF _ _ h_spec k_spec}
      (EQT: @interp_prop E F U UU h_spec k_spec t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> interp_prop RR h_spec k_spec (k1 u1) (k2 u2)):
  interp_prop RR h_spec k_spec (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  revert_until UU.

  pcofix CIH.
  intros.
  punfold EQT.
  red in EQT.

  pose proof @unfold_bind.
  specialize (H _ _ _ t1 k1).
  apply bisimulation_is_eq in H. rewrite H; clear H.

  pose proof @unfold_bind.
  specialize (H _ _ _ t2 k2).
  apply bisimulation_is_eq in H. rewrite H; clear H.

  pstep.
  induction EQT; eauto; pclearbot.
  - specialize (EQK _ _ REL).
    punfold EQK.
    eapply interp_PropTF_mono; eauto.
    intros; eauto. pclearbot.
    left.
    eapply paco2_mon; eauto.
    intros; contradiction.
  - constructor. right.
    specialize (CIH _ _ _ _ H0 HS EQK).
    eauto.
  - econstructor; auto.
  - econstructor; auto.
  - econstructor; eauto.
    + intros. right; eapply CIH; eauto.
      specialize (HK _ H). pclearbot; eauto.
    + eapply k_spec_WF_Proper; cycle 1.
      * rewrite <- unfold_bind. reflexivity.
      * pose proof @k_spec_WF_bind as Hbind.
        specialize (Hbind _ _ h_spec k_spec _).
        eapply Hbind; eauto.
      * eauto.
Qed.

Section interp_prop_extra.

  Context {E F : Type -> Type}.
  Context {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  Context (h_spec : E ~> PropT F).
  Context (k_spec : forall T R (REL:relation R), E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop).
  Context `{k_spec_wellformed : @k_spec_WF _ _ h_spec k_spec}.

  (* Figure 7: Interpreter law for Ret *)
  Lemma interp_prop_ret :
    forall R (r : R),
      (interp_prop eq h_spec k_spec (ret r) ≈ ret r)%monad.
  Proof.
    intros.
    repeat red.
    split; [| split].
    - intros. split; intros.
      + punfold H0. red in H0; cbn in H0.
        punfold H; red in H.
        remember (RetF r); remember (observe x).
        revert x Heqi0 H Heqi.
        induction H0; intros; try inv Heqi; subst; auto.
        * intros; subst; cbn.
          symmetry; pstep; auto.
        * eapply IHinterp_PropTF; eauto.
          assert (Tau t2 ≈ y) by (pstep; auto). rewrite tau_eutt in H1.
          punfold H1; auto.
      + do 2 red in H0. rewrite <- H in H0. clear H.
        punfold H0; red in H0; cbn in H0.
        pstep; red; cbn.
        remember (observe x); remember (RetF r).
        revert x r Heqi Heqi0. clear y.
        induction H0; intros; try inv Heqi0; subst; auto.
        constructor; auto; eapply IHeqitF; eauto.
    - do 3 red. intros; split; intros; [rewrite <- H | rewrite H]; auto.
    - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption.
  Qed.

  Lemma interp_prop_mono:
    forall (R : Type) RR RR' t1 t2,
      (RR <2= RR') ->
      interp_prop RR h_spec k_spec t1 t2 ->
      interp_prop (R := R) RR' h_spec k_spec t1 t2.
  Proof.
    intros ? ? ?.
    pcofix self. pstep. intros u v ? euv. punfold euv.
    red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
    econstructor; eauto.
    intros. specialize (HK _ H). pclearbot.
    right. eapply self; eauto.
    eapply k_spec_WF_mono; eauto.
  Qed.

  Lemma interp_prop_bind_refine:
      forall (R : Type) (t : itree E R) (k : R -> itree E R) (y : itree F R),
        (x0 <- interp_prop eq h_spec k_spec t;; interp_prop eq h_spec k_spec (k x0)) y ->
        interp_prop eq h_spec k_spec (x <- t;; k x) y.
  Proof.
    intros R t k y H0.
    destruct H0 as (x0&x1&?&?&?).
    rewrite H0. clear H0. clear y.
    setoid_rewrite unfold_bind.
    match goal with
    | |- interp_prop _ _ _ ?l ?r => remember l; remember r
    end.
    revert_until R. pcofix CIH. intros.
    red in H0.
    punfold H0; red in H0; cbn in H0.
    (* clear x. *)
    rename t into x, x2 into x'.
    rename x3 into k', i0 into i'.
    remember (observe x); remember (observe x').
    revert_until H0. revert x x' Heqi1 Heqi2.
    induction H0; intros.
    - subst; eauto. setoid_rewrite (itree_eta x') in H1.
      rewrite <- Heqi2 in H1.
      assert (Returns (E := F) r2 (Ret r2)) by (econstructor; reflexivity).
      specialize (H1 _ H). eapply paco2_mon. punfold H1.
      intros; inv PR.
    - (* coinductive tau *)
      pstep. subst. constructor. right. eapply CIH. eauto. pclearbot.
      3,4:eapply bisimulation_is_eq; rewrite unfold_bind; reflexivity.
      pclearbot. punfold HS. pstep. eapply HS.
      intros; eapply H1. rewrite (itree_eta x').
      rewrite <- Heqi2. eapply ReturnsTau; eauto. reflexivity.
    - rewrite Heqi. pstep. constructor; auto.
      specialize (IHinterp_PropTF t1 x' eq_refl Heqi2 H1 (bind t1 k)).

      assert (H' : x <- t1;; k x =
                  match observe t1 with
                  | RetF r => k r
                  | TauF t => Tau (ITree.bind t k)
                  | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
                  end).
      {
        apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity.
      }
      specialize (IHinterp_PropTF H' _ Heqi0).
      punfold IHinterp_PropTF.
    - rewrite Heqi0. pstep. constructor; auto.
      specialize (IHinterp_PropTF _ t2 Heqi1 eq_refl).
      assert (forall a : R, Returns a t2 -> interp_prop eq h_spec k_spec (k a) (k' a)).
      { intros; eapply H1. rewrite (itree_eta x'); rewrite <- Heqi2.
        rewrite tau_eutt; auto. }
      specialize (IHinterp_PropTF H _ Heqi (bind t2 k')).

      assert (H' : x <- t2;; k' x =
                  match observe t2 with
                  | RetF r => k' r
                  | TauF t => Tau (ITree.bind t k')
                  | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k')
                  end).
      {
        apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity.
      }
      specialize (IHinterp_PropTF H').
      punfold IHinterp_PropTF.
    - rewrite Heqi. pstep. econstructor; [ eauto | ..].
      + intros.
        pclearbot.
        right. eapply CIH; [ auto | ..].
        3,4 :eapply bisimulation_is_eq; setoid_rewrite <- unfold_bind; reflexivity.
        eauto. specialize (HK _ H). pclearbot. eapply HK.
        intros; eapply H1. rewrite (itree_eta x'). rewrite <- Heqi2.
        admit.
        (* eapply k_spec_Returns. 3 : exact H. 3 : exact H0. *)
        (* eauto. eapply k_spec_Proper; eauto. rewrite <- itree_eta; reflexivity. *)
      + match goal with
        | |- k_spec _ _ _ _ _ ?l _ => remember l
        end.
        assert (i0 = (fun a => k2 a >>= k')). {
          apply FunctionalExtensionality.functional_extensionality.
          intros; apply bisimulation_is_eq. rewrite Heqi3.
          rewrite <- unfold_bind; reflexivity.
        }
        assert (i' = t2 >>= k'). {
          apply bisimulation_is_eq. rewrite Heqi0.
          setoid_rewrite unfold_bind; reflexivity.
        }
        eapply k_spec_WF_Proper; eauto.
        rewrite itree_eta; rewrite H0; rewrite <- itree_eta; reflexivity.
        rewrite H.
        eapply k_spec_bind_; eauto.
  Admitted.

  Lemma interp_prop_ret_pure :
    forall {T} (RR : relation T) `{REF: Reflexive _ RR} (x : T),
      interp_prop RR h_spec k_spec (ret x) (ret x).
  Proof.
    intros.
    generalize dependent x.
    pcofix CIH.
    intros x.
    pstep.
    cbn.
    econstructor.
    reflexivity.
  Qed.
 
  Lemma interp_prop_ret_refine :
    forall {T} (RR : relation T) (x y : T),
      RR x y ->
      interp_prop RR h_spec k_spec (ret x) (ret y).
  Proof.
    intros.
    generalize dependent y.
    generalize dependent x.
    pcofix CIH.
    intros x y RRxy.
    pstep.
    cbn.
    econstructor; eauto.
  Qed.

  (* Lemma 5.4: interp_prop_correct - note that the paper presents a slightly simpler formulation where t = t' *)
  Lemma interp_prop_correct_exec:
    forall (h: E ~> itree F)
      (HC : handler_correct h_spec h)
      (KC : k_spec_correct h k_spec),
      forall R RR `{Reflexive _ RR} (t : _ R) t', t ≈ t' -> interp_prop RR h_spec k_spec t (interp h t').
  Proof.
    intros h HC KC R RR' H t t' H1.
    setoid_rewrite unfold_interp.
    remember (_interp h (observe t')).
    assert (i ≅ _interp h (observe t')). {
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
    - econstructor.
      apply HC; reflexivity.
      intros; right; eapply CIH; eauto.
      Unshelve.
      3 : exact (fun x => _interp h (observe (k2 x))).
      reflexivity.
      red in KC. apply KC.
      intros; try reflexivity. rewrite H2. cbn.
      eapply eutt_clo_bind; [ reflexivity | intros; subst; rewrite tau_eutt, unfold_interp; reflexivity].
    - constructor; auto; eapply IHeq; eauto.
    - cbn in H2.
      apply eqitree_inv_Tau_r in H2.
      destruct H2 as (?&?&?). rewrite unfold_interp in H1.
      specialize (IHeq _ H1 _ _ eq_refl eq_refl).
      rewrite H0. constructor; auto.
  Qed.

  (* Figure 7: interp Trigger law *)
  (* morally, we should only work with "proper" triggers everywhere *)
  Lemma interp_prop_trigger :
    forall R (e : E R) (HProper: Proper (eutt eq ==> iff) (h_spec _ e)) h
      (HC : handler_correct h_spec h)
      (KC : k_spec_correct h k_spec),
      (interp_prop eq h_spec k_spec (trigger e) ≈ h_spec _ e)%monad.
  Proof.
    intros; red.
    split; [| split]; cycle 1.
    { do 3 red. intros; split; intros; [rewrite <- H | rewrite H] ; auto. }
    { do 3 red. intros. split; intros; cbn in *.
      rewrite <- H. assumption. rewrite H; assumption. }

    intros; split; intros;
      [rewrite <- H | rewrite <- H in H0]; clear H y.
    - unfold trigger in H0. red in H0.
      punfold H0. red in H0. cbn in H0.
      unfold subevent, resum, ReSum_id, Id_IFun, id_ in H0.
      remember (VisF e (fun x => Ret x)).
      rewrite itree_eta.
      remember (observe x).
      revert Heqi x Heqi0.
      induction H0; intros; inv Heqi.
      + rewrite tau_eutt; rewrite (itree_eta). eapply IHinterp_PropTF; eauto.
      + dependent destruction H1.
        assert (x <- ta ;; k2 x ≈ ta).
        { rewrite <- (Eq.bind_ret_r ta).
          apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta).
          rewrite Eq.bind_ret_r. apply eutt_Returns.
          intros. destruct H; eauto. subst. specialize (HK _ H0).
          pclearbot.
          punfold HK; red in HK; cbn in HK.
          symmetry.
          pstep. red. cbn.
          remember (RetF u2); remember (observe (k2 u2)).
          assert (go i0 ≈ k2 u2).
          { rewrite Heqi1, <- itree_eta; reflexivity. }
          clear Heqi0. clear x H. clear k2 KS Heqi1.
          revert u2 Heqi H0.
          revert ta HTA t2.
          induction HK; intros; inv Heqi.
          - constructor; auto.
          - constructor; eauto. }
        rewrite <- H in HTA. red in HC, KC. symmetry in H.
        rewrite <- H in HTA.
        eapply k_spec_WF_respects_h_spec; eauto.
        eapply k_spec_WF_Proper; eauto. rewrite <- itree_eta; reflexivity.
      - unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_.
        red. pstep. eapply Interp_PropT_Vis with (k2 := (fun x : R => Ret x)); eauto.
        + intros; left; pstep; constructor; auto.
        + red in KC. eapply KC. eapply HC in H0. eauto.
          rewrite bind_ret_r; reflexivity.
  Qed.

End interp_prop_extra.

Lemma interp_prop_ret_inv:
  forall (E F : Type -> Type) (h_spec : forall T : Type, E T -> PropT F T)
    (k_spec : forall T R REL,
        E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop) 
    (R : Type) (RR : Relation_Definitions.relation R) (r1 : R) (t : itree F R),
    interp_prop RR h_spec k_spec (ret r1) t -> exists r2 : R, RR r1 r2 /\ t ≈ ret r2.
Proof.
  intros E F h_spec k_spec R RR r1 t INTERP.
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
  - inv Heqi.
Qed.

Section interp_refl.

  Lemma interp_prop_refl_h :
    forall {T E} (RR : relation T) `{REF: Reflexive _ RR} (t1 t2 : itree E T)
      (h : E ~> PropT E)
      (k_spec : forall T R REL, E T -> itree E T -> (T -> itree E R) -> itree E R -> Prop),
      (forall {X : Type} (e : E X), h X e (trigger e)) ->
      (k_spec_correct (fun T e => trigger e) k_spec) ->
      t1 ≈ t2 ->
      interp_prop RR h k_spec t1 t2.
  Proof.
  Admitted.

  Lemma interp_prop_refl :
    forall {T E} (RR : relation T) `{REF: Reflexive _ RR} (t : itree E T)
      (h : forall X : Type, E X -> PropT E X)
      (k_spec : forall T R REL, E T -> itree E T -> (T -> itree E R) -> itree E R -> Prop),
      (forall {X : Type} (e : E X), h X e (trigger e)) ->
      (k_spec_correct (fun T e => trigger e) k_spec) ->
      interp_prop RR h k_spec t t.
  Proof.
    intros T E0 RR REF t h k_spec H_SPEC K_SPEC.
    apply interp_prop_refl_h; eauto.
    reflexivity.
  Qed.

End interp_refl.

