(* begin hide *)
From Coq Require Import
     Relations
     String
     RelationClasses
     Morphisms
     Program.Equality.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.RefineProp
     Utils.InterpPropOOM
     Utils.Error
     Utils.Tactics
     Utils.InterpProp
     Semantics.LLVMEvents.

From ITree Require Import
     ITree
     Eq.Eqit
     Eq.EqAxiom.

From Paco Require Import paco.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Handler for out of memory
  Definition of the propositional and executable handlers for out of memory (abort).
*)

From Vellvm Require Import
     Utils.PropT.

(* TODO: Move and use in interp_prop_oom / interp_memory_prop *)
Ltac observe_vis :=
  match goal with
  | |- context [VisF ?e ?k] =>
      change (VisF e k) with (observe (Vis e k))
  end.

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

Section PARAMS_MODEL.
  Variable (E: Type -> Type).
  Context `{O : OOME -< E}.
  Notation Effin := E.
  Notation Effout := E.

  Definition refine_OOM_handler : Effin ~> PropT Effout
    := fun _ e x => x ≈ trigger e.

  Definition refine_OOM_k_spec
    {T R : Type}
    (e : Effin T)
    (ta : itree Effout T)
    (k2 : T -> itree Effout R)
    (t2 : itree Effout R) : Prop
    := eutt eq t2 (bind ta k2).

  #[global] Instance k_spec_WF_refine_OOM_k_spec : k_spec_WF refine_OOM_handler (@refine_OOM_k_spec).
  Proof using.
    split.
    - intros A R2 e ta k2.
      unfold Proper, respectful.
      intros x y H.
      unfold refine_OOM_k_spec.
      rewrite H.
      reflexivity.
    - unfold refine_OOM_k_spec.
      red.
      intros T R2 e k2 t2 ta H H0.
      auto.
  Defined.

  Definition refine_OOM_h_flip {T} (RR : relation T) (target source : itree Effout T) : Prop
    := @interp_prop_oom_l Effin Effout OOME _ _ refine_OOM_handler _ _ RR (@refine_OOM_k_spec) target source.

  Arguments refine_OOM_h_flip /.

  Definition refine_OOM_h {T} (RR : relation T) (source target : itree Effout T) : Prop
    := refine_OOM_h_flip (flip RR) target source.

  Definition refine_OOM {T} (RR : relation T) (sources : PropT Effout T) (target : itree Effout T) : Prop
    := exists source, sources source /\ refine_OOM_h RR source target.

  Ltac abs :=
    match goal with
    | [ H : ?t ≅ _ , H' : observe ?t = _ |- _] =>
        rewrite (itree_eta t) in H; rewrite H' in H;
        try solve [eapply eqit_inv in H; contradiction]
    end.

  #[global] Instance refine_OOM_h_flip_transitive {R} {RR : relation R} `{Transitive _ RR} : Transitive (refine_OOM_h_flip RR).
  Proof using.
    unfold Transitive.

    unfold refine_OOM_h_flip.
    pcofix CIH. intros x y z EQl EQr.
    punfold EQl; punfold EQr; red in EQl, EQr.
    pose proof (itree_eta x) as HX; apply bisimulation_is_eq in HX; rewrite HX; clear HX.
    pose proof (itree_eta z) as HZ; apply bisimulation_is_eq in HZ; rewrite HZ; clear HZ.

    hinduction EQl before x; intros.
    - remember (RetF r2).
      hinduction EQr before x; intros; inv Heqi; pstep; try constructor; eauto; try abs.
      specialize (IHEQr y _ _ REL eq_refl). punfold IHEQr.
      punfold HT1. red in HT1. cbn in HT1.
      dependent induction HT1.
    - (* tau tau *)
      assert (DEC: (exists m3, observe z= TauF m3) \/ (forall m3, observe z <> TauF m3)).
      { destruct (observe z); eauto; right; red; intros; inv H0. }
      destruct DEC as [EQ | EQ].
      + destruct EQ as [m3 ?]; subst.
        pstep. rewrite H0. econstructor; eauto. right. pclearbot.
        rewrite H0 in EQr.
        eapply CIH; eauto.
        eapply interp_prop_oom_inv_tau; try typeclasses eauto.
        eauto; pstep; auto.
      + pclearbot.
        inv EQr; try (exfalso; eapply EQ; eauto; fail).
        * clear CHECK.
          pstep; constructor; auto.
          punfold HS. red in HS. cbn.
          hinduction HS0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail); try inv Heqot.
          -- remember (RetF r1) as ot.
             hinduction HS before CIH; intros; try (exfalso; eapply EQ; eauto; fail); inv Heqot.
             ++ constructor. etransitivity; eauto.
             ++ constructor; eauto.
             ++ apply bisimulation_is_eq in HT1. rewrite HT1.
                solve_interp_prop_oom.
             ++ rewrite itree_eta in HT1.
                rewrite H1 in HT1.
                pinversion HT1.
             ++ red in KS, HSPEC.
                rewrite itree_eta in KS.
                rewrite HSPEC in KS.
                setoid_rewrite bind_trigger in KS.
                rewrite H1 in KS.
                eapply eqit_inv in KS; cbn in KS; inv KS.
          -- eapply IHHS0; eauto.
             assert (refine_OOM_h_flip RR t3 (Tau t1)) by (pstep; apply HS).
             eapply interp_prop_oom_inv_tau_r in H0; punfold H0.
             typeclasses eauto.
          -- apply bisimulation_is_eq in HT1. rewrite HT1 in HS.
             cbn in HS. remember (VisF (subevent A e) k1).
             hinduction HS before CIH; intros; try (exfalso; eapply EQ; eauto; fail); inv Heqi; try discriminate.
             ++ constructor; eauto.
             ++ apply bisimulation_is_eq in HT1. rewrite HT1.
                solve_interp_prop_oom.
             ++ red in KS, HSPEC.
                rewrite HSPEC in KS.
                setoid_rewrite bind_trigger in KS.
                rewrite itree_eta, H1 in KS.
                punfold KS; red in KS; cbn in KS.
                dependent induction KS.
                unfold subevent in x.
                unfold resum in x.
                unfold ReSum_id in x.
                unfold id_ in x.
                unfold Id_IFun in x.
                inv x.
                observe_vis; solve_interp_prop_oom.                
          -- punfold HT1. red in HT1. cbn in HT1.
             dependent induction HT1.
          -- red in HSPEC, KS. rewrite HSPEC in KS.
             setoid_rewrite bind_trigger in KS.
             remember (VisF e k1). rewrite itree_eta in KS.
             hinduction HS before CIH; intros; try (exfalso; eapply EQ; eauto; fail); try solve [inv Heqi]; solve_interp_prop_oom.
             ++ punfold HT1. red in HT1. cbn in HT1.
                dependent induction HT1; repeat subst_existT.
             ++ red in KS.
                rewrite itree_eta in KS. rewrite Heqi in KS.
                red in HSPEC. rewrite HSPEC in KS. setoid_rewrite bind_trigger in KS.
                apply eqit_inv in KS. cbn in KS. rewrite <- itree_eta in KS0.
                destruct KS as (?&?&?); subst. cbn in *.
                unfold subevent in KS0.
                unfold subevent, resum, ReSum_id, id_, ReSum_inr, cat, Id_IFun, Cat_IFun, inr_,
                  resum , ReSum_inl , cat, resum, Inr_sum1, inl_, Inl_sum1 in KS0. inv H0.
                eapply Interp_Prop_OomT_Vis. 3 : eauto. 2 : red; reflexivity.

                setoid_rewrite HSPEC in HK.
                intros; right; eapply CIH; pclearbot; eauto.
                specialize (HK _ H0); pclearbot; eauto.
                2: {
                  red.
                  rewrite KS0.
                  setoid_rewrite bind_trigger.
                  reflexivity.
                }

                assert (Returns a ta0).
                { rewrite HSPEC0.
                  rewrite subevent_subevent.
                  auto.
                }
                specialize (HK0 _ H3); pclearbot; eauto.
                specialize (H1 a).
                cbn in H1.
                eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
                rewrite <- H1; reflexivity.
                reflexivity.
                auto.
        * exfalso. rewrite itree_eta in HT1. rewrite H1 in HT1.
          apply eqit_inv in HT1; inv HT1.
        * punfold HT1. red in HT1. cbn in HT1.
          dependent induction HT1.
    - (* tauL *)
      specialize (IHEQl _ EQr).
      pstep; constructor; punfold IHEQl.
    - (* tauR *)
      assert (refine_OOM_h_flip RR (Tau t2) z). { pstep; auto. }
      red in H0. apply interp_prop_oom_inv_tau_l in H0.
      punfold H0.
    - (* oom left *)
      punfold HT1; red in HT1; cbn in HT1.
      dependent induction HT1.
      rewrite <- x.
      pstep; red; cbn.
      observe_vis; solve_interp_prop_oom.
    - (* oom right *)
      discriminate.
    - red in HSPEC, KS.
      rewrite itree_eta in KS.
      hinduction EQr before z; intros; try inv Heqi; pclearbot.
      + rewrite HSPEC in KS. apply eqit_inv in KS; inv KS.
      + pstep; constructor; eauto.
        rewrite HSPEC in KS.
        rewrite tau_eutt in KS. setoid_rewrite bind_vis in KS.
        setoid_rewrite bind_ret_l in KS.
        assert (refine_OOM_h_flip RR t1 t0). do 2 red. apply HS.
        unfold refine_OOM_h_flip in *.
        eapply interp_prop_oom_l_eutt_Proper in H0.
        3: rewrite KS; reflexivity.
        all: try reflexivity; try typeclasses eauto.
        clear HS.
        punfold H0; red in H0; cbn in H0.
        remember (VisF (subevent A e) (fun x : A => k2 x)).
        hinduction H0 before z; intros; try inv Heqi; pclearbot.
        * constructor; auto; eapply IHinterp_prop_oomTF.
        * rewrite itree_eta, H1 in HT1.
          punfold HT1; red in HT1; cbn in HT1.
          dependent induction HT1.
          unfold subevent, resum, ReSum_id, id_, ReSum_inr, cat, Id_IFun, Cat_IFun, inr_,
            resum , ReSum_inl , cat, resum, Inr_sum1, inl_, Inl_sum1 in x.
          inv x.
          solve_interp_prop_oom.
        * rewrite itree_eta in HT1.
          punfold HT1; red in HT1; cbn in HT1.
          dependent induction HT1.
        * dependent destruction H2.
          eapply Interp_Prop_OomT_Vis; eauto.
          red in KS0, HSPEC0. rewrite HSPEC0 in KS0. setoid_rewrite bind_trigger in KS0.
          intros. right; eapply CIH; eauto.
          unfold subevent in HSPEC0.
          unfold subevent, resum, ReSum_id, id_, ReSum_inr, cat, Id_IFun, Cat_IFun, inr_,
            resum , ReSum_inl , cat, resum, Inr_sum1 in HSPEC0.
          rewrite HSPEC0, <- HSPEC in H0.
          specialize (HK _ H0); pclearbot. apply HK.
          specialize (HK0 _ H0); pclearbot. apply HK0.
      + eapply IHEQr. rewrite <- itree_eta. rewrite tau_eutt in KS; auto.
      + specialize (IHEQr KS).
        pstep; constructor; auto. punfold IHEQr.
      + rewrite HSPEC in KS.
        rewrite HT1 in KS.
        cbn in KS.
        rewrite bind_trigger in KS.
        punfold KS; red in KS; cbn in KS.
        dependent induction KS.
        unfold subevent, resum, ReSum_id, id_, ReSum_inr, cat, Id_IFun, Cat_IFun, inr_,
          resum , ReSum_inl , cat, resum, Inr_sum1 in x.
        inv x.
        solve_interp_prop_oom.        
      + punfold HT1; red in HT1; cbn in HT1.
        dependent induction HT1.
      + pstep.
        rewrite HSPEC in KS; setoid_rewrite bind_trigger in KS.
        apply eqit_inv in KS; cbn in KS.
        destruct KS as (?&?&?); subst. cbn in *.
        unfold subevent in H0.
        unfold subevent, resum, ReSum_id, id_, ReSum_inr, cat, Id_IFun, Cat_IFun, inr_,
          resum , ReSum_inl , cat, resum, Inr_sum1, inl_, Inl_sum1 in H0. inv H0.
        cbn in *. red in HSPEC0, KS0.
        eapply Interp_Prop_OomT_Vis; eauto.
        2 : red; rewrite <- itree_eta; eauto.
        intros. right. eapply CIH; eauto.
        rewrite HSPEC0 in H0; setoid_rewrite HSPEC in HK; specialize (HK _ H0); pclearbot; eauto.
        specialize (HK0 _ H0); pclearbot.
        eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
        rewrite <- H1; reflexivity.
        reflexivity.
        eauto.
  Qed.

  #[global] Instance refine_OOM_h_reflexive {R} {RR : relation R} `{Reflexive _ RR} : Reflexive (refine_OOM_h RR).
  Proof using.
    unfold Reflexive.

    pcofix CIH. intros t.
    assert (t ≅ t) by reflexivity.
    punfold H0; red in H0; intros.
    pstep; red.
    hinduction H0 before t; try solve [constructor; auto]; try inv CHECK; intros.
    constructor; reflexivity.

    change (VisF e k2) with (observe (Vis e k2)).
    eapply Interp_Prop_OomT_Vis; eauto. red; reflexivity.
    red.
    setoid_rewrite bind_trigger; reflexivity.
  Qed.

  #[global] Instance refine_OOM_h_transitive {R} {RR : relation R} `{Transitive _ RR} : Transitive (refine_OOM_h RR).
  Proof using.
    unfold refine_OOM_h.
    assert (Transitive (flip RR)).
    { repeat intro. subst. unfold flip in *; etransitivity; eauto. }
    repeat intro. etransitivity; eauto.
  Qed.

End PARAMS_MODEL.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).
  Context `{FailureE -< F}.
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME +' F).

  Definition OOM_exec_fail {E} `{FailureE -< E}: OOME ~> itree E :=
    fun _ e => match e with | ThrowOOM tt => raise ("Abort (OOM)") end.

  Definition OOM_exec {E} `{OOME -< E} : OOME ~> itree E :=
    fun R e => trigger e.

  Definition E_trigger :  E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM :
    itree Effin ~> itree Effout :=
    interp ITree.trigger.

End PARAMS_INTERP.

Lemma eutt_refine_oom_h :
  forall {T} {E F} (RR : relation T) `{REF: Reflexive _ RR} `{TRANS : Transitive _ RR}
    (t1 t2 : itree (E +' OOME +' F) T),
    eutt RR t1 t2 ->
    refine_OOM_h RR t1 t2.
Proof using.
  intros T E F RR REF TRANS t1 t2 H.
  unfold refine_OOM_h.
  pose proof @interp_prop_oom_Proper_eq.
  unfold Proper, respectful in H0.

  eapply H0; eauto.
  all: try typeclasses eauto.
  apply eutt_flip; eauto.
  apply refine_OOM_h_reflexive; auto.
Qed.

Lemma refine_oom_h_raise_oom :
  forall {T} {E F} (RR : relation T)
    `{REF : Reflexive T RR}
    `{TRANS : Transitive T RR}
    (source : itree (E +' OOME +' F) T)
    (oom_msg : string),
    refine_OOM_h RR source (raiseOOM oom_msg).
Proof using.
  intros T E F RR REF TRANS source oom_msg.
  unfold refine_OOM_h.

  unfold raiseOOM.
  red.

  eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
  rewrite bind_trigger.
  all: try reflexivity.

  red.
  pstep; red; cbn.
  observe_vis; solve_interp_prop_oom.
Qed.

#[global] Instance refine_OOM_h_eutt_Proper {T : Type} {RR : relation T} {E F}:
  Proper (eutt eq ==> eutt eq ==> iff) (@refine_OOM_h E F T RR).
Proof using.
  unfold Proper, respectful.
  intros x y XY z w ZW.
  split; intros REF; subst.
  - unfold refine_OOM_h, refine_OOM_h_flip in *.
    eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
    rewrite <- ZW; reflexivity.
    rewrite <- XY; reflexivity.
    auto.
  - unfold refine_OOM_h, refine_OOM_h_flip in *.
    eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
    rewrite ZW; reflexivity.
    rewrite XY; reflexivity.
    auto.
Qed.

#[global] Instance refine_OOM_h_eq_itree {E F T RR} : Proper (eq_itree eq ==> eq_itree eq ==> iff) (@refine_OOM_h E F T RR).
repeat intro. rewrite H, H0.
reflexivity.
Qed.

(* TODO: broken after k_spec changes *)
(* Lemma refine_OOM_h_bind : *)
(*   forall {T R E F} (x y : itree (E +' OOME +' F) T) (RR1 : relation T) (RR2 : relation R) k, *)
(*     (forall r1 r2, RR1 r1 r2 -> refine_OOM_h RR2 (k r1) (k r2)) -> *)
(*     refine_OOM_h RR1 x y -> *)
(*     refine_OOM_h RR2 (a <- x;; k a) (a <- y;; k a). *)
(* Proof using. *)
(*   intros T R E F. *)

(*   unfold refine_OOM_h, refine_OOM_h_flip. *)
(*   intros t1 t2 RR1 RR2. *)

(*   unfold bind, Monad_itree. *)
(*   revert t1 t2. pcofix CIH. *)
(*   intros t1 t2 k HK EQT. *)
(*   punfold EQT. *)
(*   red in EQT. *)

(*   assert (a <- t1 ;; k a = *)
(*             match observe t1 with *)
(*             | RetF r => k r *)
(*             | TauF t0 => Tau (ITree.bind t0 k) *)
(*             | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k) *)
(*             end). *)
(*   { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. } *)
(*   setoid_rewrite H; clear H. *)

(*   assert (a <- t2 ;; k a = *)
(*             match observe t2 with *)
(*             | RetF r => k r *)
(*             | TauF t0 => Tau (ITree.bind t0 k) *)
(*             | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k) *)
(*             end). *)
(*   { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. } *)
(*   setoid_rewrite H; clear H. *)

(*   pstep. *)
(*   induction EQT; eauto; pclearbot; try discriminate. *)
(*   - specialize (HK _ _ REL). *)
(*     punfold HK. *)
(*     eapply interp_prop_oomTF_mono. eapply HK. *)
(*     intros. pclearbot. left. *)
(*     eapply paco2_mon; eauto. *)
(*     intros; contradiction. *)
(*   - constructor. right. *)
(*     eapply CIH; eauto. *)
(*   - econstructor; auto. *)
(*   - econstructor; auto. *)
(*   - punfold HT1; red in HT1; cbn in HT1. *)
(*     dependent induction HT1. *)
(*     rewrite <- x. *)
(*     red. solve_interp_prop_oom. *)
(*   - eapply Interp_Prop_OomT_Vis; eauto. *)
(*     intros; eauto. right. eapply CIH; eauto. *)
(*     specialize (HK0 _ H). pclearbot. eapply HK0; eauto. *)
(*     rewrite <- unfold_bind. *)
(*     setoid_rewrite <- Eqit.bind_bind. *)
(*     eapply eutt_clo_bind; eauto. intros; eauto. *)
(*     subst; reflexivity. *)
(* Qed. *)
