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

Section interp_prop.

  Context {E F OOM : Type -> Type} {OOME: OOM -< E}.
  Context (h_spec : E ~> PropT F) {R : Type} (RR : R -> R -> Prop).

  Inductive interp_PropTF
            (b1 b2 : bool) (sim : itree E R -> itree F R -> Prop)
            : itree' E R -> itree' F R -> Prop :=
  | Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2),
      interp_PropTF b1 b2 sim (RetF r1) (RetF r2)

  | Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_PropTF b1 b2 sim (TauF t1) (TauF t2)

  | Interp_PropT_TauL : forall t1 t2
                          (CHECK: is_true b1)
                          (HS: interp_PropTF b1 b2 sim (observe t1) t2),
      interp_PropTF b1 b2 sim (TauF t1) t2

  | Interp_PropT_TauR : forall t1 t2
                          (CHECK: is_true b2)
                          (HS: interp_PropTF b1 b2 sim t1 (observe t2)),
      interp_PropTF b1 b2 sim t1 (TauF t2)

  | Interp_PropT_Vis_OOM : forall A (e : OOM A) k1 t1 t2
                         (HT1: t1 ≅ vis e k1),
      interp_PropTF b1 b2 sim (observe t1) t2

  | Interp_PropT_Vis : forall A e k1 k2 (ta t2 : itree F _)
                  (HK : forall (a : A), Returns a ta -> sim (k1 a) (k2 a)),
        h_spec _ e ta ->
        t2 ≈ ta >>= k2 ->
        interp_PropTF b1 b2 sim (VisF e k1) (observe t2).

  Hint Constructors interp_PropTF : core.

  Lemma interp_PropTF_mono b1 b2 x0 x1 sim sim'
        (IN: interp_PropTF b1 b2 sim x0 x1)
        (LE: sim <2= sim'):
    interp_PropTF b1 b2 sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Hint Resolve interp_PropTF_mono : paco.

  Definition interp_PropT_ b1 b2 sim (t0 : itree _ R) (t1 : itree _ R) :=
    interp_PropTF b1 b2 sim (observe t0) (observe t1).
  Hint Unfold interp_PropT_ : core.

  Lemma interp_PropT__mono b1 b2 : monotone2 (interp_PropT_ b1 b2).
  Proof.
    do 2 red. intros. eapply interp_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_PropT__mono : paco.

  Lemma interp_PropT_idclo_mono: monotone2 (@id (itree E R -> itree F R -> Prop)).
  Proof. unfold id. eauto. Qed.
  Hint Resolve interp_PropT_idclo_mono : paco.

  (* Definition 5.2 *)
  Definition interp_prop' b1 b2 :
    itree _ R -> PropT _ R :=
    paco2 (interp_PropT_ b1 b2) bot2.

  Definition interp_prop :
    itree _ R -> PropT _ R :=
    interp_prop' true true.

  #[global] Instance interp_prop_eq_itree_Proper_impl_ :
    forall (x : _ R), Proper (eq_itree eq ==> impl) (interp_prop x).
  Proof.
    repeat intro. eapply bisimulation_is_eq in H; subst; eauto.
  Qed.

  #[global] Instance interp_prop_eq_itree_Proper_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> impl) interp_prop.
  Proof.
    repeat intro.
    repeat intro. eapply bisimulation_is_eq in H, H0; subst; eauto.
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
    - rewrite HT1, <- itree_eta; pstep; econstructor; reflexivity.
    - pstep; eapply Interp_PropT_Vis; eauto.
      rewrite (itree_eta t2) in H0.
      rewrite H2 in H0. rewrite tau_eutt in H0; eauto.
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
    - rewrite itree_eta in HT1; rewrite H0 in HT1; eapply eqit_inv in HT1; contradiction.
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
    revert_until RR.
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
          (* pose proof @Interp_PropT_Vis. *)
          (* change (VisF e0 k3) with (observe (Vis e0 k3)). *)
          (* eapply H; eauto. *)
          (* intros. *)
          (* left. specialize (HK _ H0). pclearbot. *)
          (* eapply paco2_mon; eauto. intros; inv PR. *)
    (*       eapply k_spec_WF_Proper. eapply eqit_Vis. symmetry. pclearbot. eauto. *)
    (*       eapply k_spec_WF_Proper. Unshelve. *)
    (*       3 : exact t2. *)
    (*       rewrite (itree_eta t2), Heqot. eapply eqit_Vis; reflexivity. *)
    (*       eauto. *)
    (*     * eapply IHREL; eauto. pstep_reverse. *)
    (*       assert (interp_prop t0 (Tau t1)) by (pstep; auto). *)
    (*       apply interp_prop_inv_tau_r in H. punfold H. *)
    (* - rewrite <- Heqi. constructor; auto. *)
    (*   specialize (IHinterp_PropTF _ eq_refl _ Heqi0 EQ). auto. *)
    (* - rewrite <- Heqi. *)
    (*   remember (TauF t2) as ot. clear Heqi0 y. *)
    (*   hinduction EQ before CIH; intros; try inversion Heqot; pclearbot; subst; eauto. *)
    (*   punfold REL. *)
    (*   eapply IHinterp_PropTF; eauto. *)
    (*   constructor; eauto. *)
    (*   assert (Tau t0 ≈ t2). { pstep; auto. } *)
    (*   apply eqit_inv_Tau_l in H1; punfold H1. *)
    (* - rewrite <- Heqi. *)
    (*   econstructor; eauto; cycle 1. *)
    (*   eapply k_spec_WF_Proper. rewrite Heqi0 in EQ. *)
    (*   symmetry. pstep; red; eauto. *)
    (*   eapply k_spec_WF_Proper. 2 : eauto. rewrite itree_eta; rewrite <- Heqi0; rewrite <- itree_eta; reflexivity. *)
    (*   intros. specialize (HK _ H). pclearbot. *)
    (*   left. eapply paco2_mon; intros; eauto. *)
          (*   inv PR. *)
  Admitted.

  #[global] Instance interp_prop_eutt_Proper_impl :
    Proper (eutt eq ==> eutt eq ==> impl) (interp_prop).
  Proof.
    intros y y' EQ x x' EQ' H.
    rewrite <- EQ'. clear x' EQ'.
    punfold H; punfold EQ; red in H; red in EQ; cbn in *.
    (* revert_until k_spec_wellformed. *)
    (* pcofix CIH. *)
    (* intros x x' EQ y H. *)
    (* remember (observe x); remember (observe y). *)
    (* pstep. red. genobs_clear x' ox'. *)
    (* revert x Heqi y Heqi0 EQ. *)
    (* (* induct on interp_prop *) *)
    (* rename i into xo, i0 into yo. *)
    (* induction H; subst; pclearbot; intros. *)
    (* - rewrite <- Heqi0. *)
    (*   remember (RetF (E:= E) r1). *)
    (*   induction EQ; inv Heqi1; intros. *)
    (*   + constructor; auto. *)
    (*   + constructor; auto. *)

    (* - rewrite <- Heqi0. *)
    (*   rename ox' into ot3. *)
    (*   assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)). *)
    (*   { destruct ot3; eauto; right; red; intros; inv H. } *)

    (*   rename EQ into INR. *)
    (*   destruct DEC as [EQ | EQ]. *)
    (*   + destruct EQ as [m3 ?]; rewrite H. *)
    (*     econstructor. right. pclearbot. eapply CIH; eauto with paco. *)
    (*     rewrite H in INR. *)
    (*     assert (Tau t1 ≈ Tau m3). pstep; auto. *)
    (*     eapply eqit_inv_Tau in H0. punfold H0. *)
    (*     punfold HS. *)

    (*   + inv INR; try (exfalso; eapply EQ; eauto; fail). *)
    (*     econstructor; eauto. *)
    (*     punfold HS. red in HS. *)
    (*     pclearbot. *)
    (*     hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail). *)
    (*     * subst. remember (RetF r2) as ot. *)
    (*       eapply interp_PropTF_mono; eauto. *)
    (*       intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0. *)
    (*     * remember (VisF e k1) as ot. *)
    (*       hinduction HS before CIH; intros; try discriminate; eauto. *)
    (*       pose proof @Interp_PropT_Vis. *)
    (*       inversion Heqot. dependent destruction H3. *)
    (*       eapply H; eauto. *)
    (*       intros. right. eapply CIH; eauto. *)
    (*       specialize (REL a). pclearbot. punfold REL. *)
    (*       specialize (HK _ H0). pclearbot. *)
    (*       punfold HK. *)
    (*     * eapply IHREL; eauto. pstep_reverse. *)
    (*       assert (interp_prop (Tau t0) t2) by (pstep; auto). *)
    (*       apply interp_prop_inv_tau_l in H. punfold H. *)
    (* - specialize (IHinterp_PropTF _ eq_refl _ Heqi0). *)
    (*   assert (t1 ≈ go ox'). *)
    (*   { rewrite <- tau_eutt; pstep; auto. } *)
    (*   punfold H0. *)
    (* - rewrite <- Heqi0. *)
    (*   constructor; auto. eapply IHinterp_PropTF; eauto. *)
    (* - rewrite <- Heqi0. *)
    (*   remember (VisF e k1). clear x Heqi. *)

    (*   hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; subst; eauto. *)
    (*   dependent destruction H1. *)
    (*   econstructor; eauto. *)
    (*   intros; specialize (HK _ H); pclearbot. *)
    (*   right; eapply CIH; [ | punfold HK]. *)
    (*   specialize (REL a). *)
    (*   punfold REL. *)
  Admitted.

  #[global] Instance interp_prop_eutt_Proper :
    Proper (eutt eq ==> eutt eq ==> iff) interp_prop.
  Proof.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.
End interp_prop.

Arguments interp_prop {_ _ _ _} _ {_}.
Arguments interp_prop' {_ _ _ _} _ {_}.

Hint Constructors interp_PropTF : core.
Hint Resolve interp_PropTF_mono : paco.
Hint Unfold interp_PropT_ : core.
Hint Resolve interp_PropT__mono : paco.
Hint Resolve interp_PropT_idclo_mono : paco.

Section interp_prop_extra.

  Context {E F OOM : Type -> Type} {OOME: OOM -< E}.
  Context (h : E ~> PropT F).
  Context {R : Type} (RR : R -> R -> Prop).

  Lemma interp_prop_clo_bind {U} t1 t2 k1 k2
        (EQT: @interp_prop E F OOM _ h U eq t1 t2)
        (EQK: forall u1 u2, eq u1 u2 -> @interp_prop E F OOM _ h _ eq (k1 u1) (k2 u2)):
    @interp_prop E F OOM _ h _ eq (ITree.bind t1 k1) (ITree.bind (U := U) t2 k2).
  Proof.
    revert_until U.

    pcofix CIH.
    intros.
    punfold EQT.
    red in EQT.

    assert (ITree.bind t1 k1 =
              match observe t1 with
              | RetF r => k1 r
              | TauF t0 => Tau (ITree.bind t0 k1)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k1)
              end).
    { apply bisimulation_is_eq; rewrite unfold_bind; reflexivity. }
    rewrite H; clear H.

    assert (ITree.bind t2 k2 =
              match observe t2 with
              | RetF r => k2 r
              | TauF t0 => Tau (ITree.bind t0 k2)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k2)
              end).
    { apply bisimulation_is_eq; rewrite unfold_bind; reflexivity. }
    rewrite H; clear H.

    pstep.
    induction EQT; eauto; pclearbot.
    - specialize (EQK _ _ REL).
      punfold EQK.
      eapply interp_PropTF_mono. 1 : eapply EQK. all : eauto.
      intros. pclearbot. left.
      eapply paco2_mon; eauto.
      intros; contradiction.
    - constructor. right.
      specialize (CIH _ _ _ _ HS EQK).
      eauto.
    - econstructor; auto.
    - econstructor; auto.
    - eapply Interp_PropT_Vis_OOM with (e := e).
      punfold HT1; red in HT1. remember (observe (vis e k0)).
      hinduction HT1 before U; intros; inv Heqi; try inv CHECK.
      dependent destruction H1. unfold subevent.
      eapply eqit_Vis.
      Unshelve.
      2 : exact (fun a => bind (k0 a) k1).
      intros. cbn.
      eapply eq_itree_clo_bind; pclearbot; eauto. intros; subst; reflexivity.
    - eapply Interp_PropT_Vis; eauto.
      intros; eauto. right. eapply CIH; eauto.
      specialize (HK _ H1). pclearbot. eapply HK; eauto.
      rewrite <- unfold_bind.
      setoid_rewrite <- Eq.bind_bind.
      eapply eutt_clo_bind; eauto. intros; eauto. subst; reflexivity.
  Qed.

  Lemma interp_prop_mono:
    forall (R : Type) RR RR' t1 t2,
      (RR <2= RR') ->
      interp_prop h RR t1 t2 ->
      interp_prop h (F := F) (R := R) RR' t1 t2.
  Proof.
    intros ? ? ?.
    pcofix self. pstep. intros u v ? euv. punfold euv.
    red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
    econstructor; eauto.
    intros. specialize (HK _ H2). pclearbot.
    right. eapply self; eauto.
  Qed.

  (* Figure 7: Interpreter law for Ret *)
  Lemma interp_prop_ret :
    forall R (r : R),
      (interp_prop (F := F) h eq (ret r) ≈ ret r)%monad.
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
        * rewrite itree_eta in HT1; rewrite H1 in HT1; apply eqit_inv in HT1; contradiction.
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

  Lemma interp_prop_bind_refine:
      forall (t : itree E R) (k : R -> itree E R) (y : itree F R),
        (x0 <- interp_prop h eq t;; interp_prop h eq (k x0)) y ->
        interp_prop h eq (x <- t;; k x) y.
  Proof.
    intros t k y H0.
    destruct H0 as (x0&x1&?&?&?).
    rewrite H0. clear H0 y.
    rename x0 into t', x1 into k'.
    setoid_rewrite unfold_bind.
    match goal with
    | |- interp_prop _ _ ?l ?r => remember l; remember r
    end.
    revert_until RR. pcofix CIH. intros.
    red in H0.
    punfold H0; red in H0; cbn in H0.
    remember (observe t); remember (observe t').
    setoid_rewrite (itree_eta t') in H1.
    revert t t' k k' Heqi1 Heqi2 H1 i i0 Heqi Heqi0.
    induction H0; intros.

    - subst; eauto.
      assert (Returns r2 t').
      { rewrite itree_eta; rewrite <- Heqi2; constructor; reflexivity. }
      setoid_rewrite <- itree_eta in H1.
      specialize (H1 _ H). eapply paco2_mon. punfold H1.
      intros; inv PR.

    - (* coinductive tau *)
      pstep. subst. constructor. right. eapply CIH. eauto. pclearbot.
      3,4:eapply bisimulation_is_eq; rewrite unfold_bind; reflexivity.
      pclearbot. punfold HS. pstep. eapply HS.
      intros; eapply H1. rewrite (itree_eta t').
      rewrite <- Heqi2. eapply ReturnsTau; eauto. reflexivity.
    - rewrite Heqi. pstep. constructor; auto.
      specialize (IHinterp_PropTF t1 t' k k' eq_refl Heqi2 H1 (bind t1 k)).

      assert (H' : x <- t1;; k x =
                  match observe t1 with
                  | RetF r => k r
                  | TauF t => Tau (ITree.bind t k)
                  | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
                  end).
      {
        apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity.
      }
      specialize (IHinterp_PropTF i0 H' Heqi0).
      punfold IHinterp_PropTF.
    - rewrite Heqi0. pstep. constructor; auto.

      specialize (IHinterp_PropTF _ _ k k' Heqi1 eq_refl).

      assert (forall a : R, Returns a t2 -> interp_prop h eq (k a) (k' a)).
      { intros; eapply H1. rewrite (itree_eta t'); rewrite <- Heqi2.
        rewrite tau_eutt; auto. rewrite <- itree_eta; auto. }

      setoid_rewrite <- itree_eta in IHinterp_PropTF.
      specialize (IHinterp_PropTF H).

      assert (H' : x <- t2;; k' x =
                  match observe t2 with
                  | RetF r => k' r
                  | TauF t => Tau (ITree.bind t k')
                  | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k')
                  end).
      {
        apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity.
      }
      specialize (IHinterp_PropTF _ _ Heqi H').
      punfold IHinterp_PropTF.

    - subst.
      punfold HT1.
      red in HT1. cbn in HT1.
      remember (VisF (subevent A e) k1).
      hinduction HT1 before e; intros; inv Heqi.
      + dependent destruction H2.
        pclearbot. pstep.
        eapply Interp_PropT_Vis_OOM; eauto.
        reflexivity.
      + pstep. constructor; eauto.

        assert (t0 >>= k =
                  match observe t0 with
                  | RetF r => k r
                  | TauF t0 => Tau (ITree.bind t0 k)
                  | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
                  end). {
          intros; apply bisimulation_is_eq.
          rewrite <- unfold_bind; reflexivity. }
        setoid_rewrite H.

        specialize (IHHT1 _ eq_refl _ _ _ _ eq_refl H1).
        punfold IHHT1.

    - rewrite Heqi, Heqi0; clear Heqi Heqi0.
      pstep. eapply Interp_PropT_Vis; eauto.
      intros. specialize (HK _ H2); pclearbot. right.
      eapply CIH; eauto.
      intros; eapply H1; eauto.
      rewrite <- Heqi2. rewrite <- itree_eta.
      rewrite H0. eapply Returns_bind; eauto.
      apply bisimulation_is_eq; rewrite <- unfold_bind; reflexivity.
      apply bisimulation_is_eq; setoid_rewrite <- unfold_bind; reflexivity.
      setoid_rewrite <- unfold_bind. rewrite H0. setoid_rewrite Eq.bind_bind; reflexivity.
  Qed.

  Lemma interp_prop_ret_pure :
    forall {T} (RR : relation T) `{REF: Reflexive _ RR} (x : T),
      interp_prop (F := F) h RR (ret x) (ret x).
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
      interp_prop (F := F) h RR (ret x) (ret y).
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
  (* Lemma interp_prop_correct_exec: *)
  (*   forall *)
  (*     `{Reflexive _ RR} (t : _ R) t', t ≈ t' -> interp_prop h RR t (interp h t'). *)
  (* Proof. *)
  (*   intros H t t' H1. *)
  (*   setoid_rewrite unfold_interp. *)
  (*   remember (_interp h (observe t')). *)
  (*   assert (i ≅ _interp h (observe t')). { *)
  (*     rewrite Heqi. reflexivity. *)
  (*   } clear Heqi. *)
  (*   revert t t' i H1 H0. *)
  (*   pcofix CIH. *)
  (*   intros t t' i eq ?. *)
  (*   pstep. *)
  (*   red. *)
  (*   punfold eq. red in eq. *)
  (*   genobs t ot; genobs t' ot'. *)
  (*   revert i H2 t t' Heqot Heqot'. *)
  (*   induction eq; intros; subst; pclearbot; auto. *)
  (*   - punfold H2; inv H2; try inv CHECK. *)
  (*     constructor; auto. *)
  (*   - punfold H2; inv H2; try inv CHECK. *)
  (*     constructor; auto. *)
  (*     right; eauto. eapply CIH; pclearbot; eauto. *)
  (*     rewrite <- unfold_interp; auto. *)
  (*   - cbn in H2. *)
  (*   (*   eapply Interp_PropT_Vis; eauto; cycle 1. *) *)
  (*   (*   rewrite H2. eapply eutt_clo_bind; try reflexivity. *) *)
  (*   (*   intros; subst; setoid_rewrite tau_eutt at 2. *) *)
  (*   (*   Unshelve. 3 : exact (fun x => interp h (k2 x)). reflexivity. *) *)
  (*   (*   intros. right; eapply CIH; eauto. *) *)
  (*   (*   rewrite <- unfold_interp; reflexivity. *) *)
  (*   (* - constructor; auto; eapply IHeq; eauto. *) *)
  (*   (* - cbn in H2. *) *)
  (*   (*   apply eqitree_inv_Tau_r in H2. *) *)
  (*   (*   destruct H2 as (?&?&?). rewrite unfold_interp in H1. *) *)
  (*   (*   specialize (IHeq _ H1 _ _ eq_refl eq_refl). *) *)
  (*   (*   rewrite H0. constructor; auto. *) *)
  (*     (* Qed. *) *)
  (* Admitted. *)

  (* Figure 7: interp Trigger law *)
  (* morally, we should only work with "proper" triggers everywhere *)
  (* Lemma interp_prop_trigger : *)
  (*   forall R (e : E R) (h : E ~> PropT (itree F)) (HProper: forall A e, Proper (eutt eq ==> iff) (h A e)), *)
  (*     (interp_prop h eq (trigger e) ≈ h _ e)%monad. *)
  (* Proof. *)
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
      (* + rewrite tau_eutt; rewrite (itree_eta). eapply IHinterp_PropTF; eauto. *)
      (* + dependent destruction H1. *)
      (*   assert (x <- ta ;; k2 x ≈ ta). *)
      (*   { rewrite <- (Eq.bind_ret_r ta). *)
      (*     apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta). *)
      (*     rewrite Eq.bind_ret_r. apply eutt_Returns. *)
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
      (*   red. pstep. eapply Interp_PropT_Vis with (k2 := (fun x : R => Ret x)); eauto. *)
      (*   + intros; left; pstep; constructor; auto. *)
      (*   + red in KC. eapply KC. eapply HC in H0. eauto. *)
      (*     rewrite bind_ret_r; reflexivity. *)
  (* Admitted. *)

  Lemma interp_prop_ret_inv:
    forall (r1 : R) (t : itree F R),
      interp_prop (F := F) h RR (ret r1) t -> exists r2 : R, RR r1 r2 /\ t ≈ ret r2.
  Proof.
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
    - inv Heqi.
      rewrite itree_eta in HT1; rewrite H0 in HT1; apply eqit_inv in HT1; contradiction.
    - inv Heqi.
  Qed.

End interp_prop_extra.

Section interp_refl.

  (* Lemma interp_prop_refl : *)
  (*   forall {T E OOM} `{OOM -< E} (RR : relation T) `{REF: Reflexive _ RR} (t : itree E T) h, *)
  (*     @interp_prop E E OOM _ h _ RR t (interp h t). *)
  (* Proof. *)
  (*   intros T E OOM H RR REFL t h. revert t. *)
  (*   pcofix CIH. intros t. *)
  (*   assert (interp h t = _interp h (observe t)). { *)
  (*     apply bisimulation_is_eq; rewrite unfold_interp; reflexivity. *)
  (*   } *)
  (*   rewrite H0. *)
  (*   assert (t ≅ t) by reflexivity. *)
  (*   punfold H1; red in H1; intros. *)
  (*   pstep; red. *)
  (*   hinduction H1 before t; try solve [constructor; auto]; try inv CHECK; intros. *)
  (*   cbn. *)
  (*   eapply Interp_PropT_Vis. *)
  (* (*   intros; right. eapply CIH. *) *)
  (* (*   eapply eutt_clo_bind; [ reflexivity | intros; subst]. *) *)
  (* (*   rewrite tau_eutt. reflexivity. *) *)
  (*   (* Qed. *) *)
  (* Admitted. *)

End interp_refl.

