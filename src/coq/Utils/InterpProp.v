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
     Basics.MonadState.

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
    (forall T e, h_spec T e (h T e)).

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
             (k_spec : forall T R, E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop) : Prop
    := forall T R e k2 t2, t2 ≈ bind (h T e) k2 -> k_spec T R e (h T e) k2 t2.

  Context {E F : Type -> Type}.
  Context (h_spec : E ~> PropT F).
  Context (k_spec : forall T R, E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop).

  (* Well-formedness conditions for k_specs *)
  Class k_spec_WF := {
      k_spec_Returns: forall {A R} ta k2 t2 e,
        k_spec A R e ta k2 t2 -> forall a, Returns a ta -> forall a', Returns a' (k2 a) -> Returns a' t2;
      k_spec_bind: forall {A R} ta k2 (t2 : itree F R) e (k' : _ -> itree F R),
        k_spec A R e ta k2 t2 ->
        k_spec A R e ta (fun x => bind (k2 x) k') (bind t2 k');
      k_spec_Proper : forall {A R} ta k e,
        Proper (eutt eq ==> iff) (k_spec A R e ta k)
    }.

  Context (k_spec_wellformed : k_spec_WF).

  Inductive interp_PropTF
            {R : Type} (RR : relation R) (sim : itree E R -> itree F R -> Prop)
            : itree' E R -> itree' F R -> Prop :=
  | Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2),
      interp_PropTF RR sim (RetF r1) (RetF r2)

  | Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_PropTF RR sim (TauF t1) (TauF t2)

  | Interp_PropT_TauL : forall t1 t2 (HS: interp_PropTF RR sim (observe t1) t2),
      interp_PropTF RR sim (TauF t1) t2

  | Interp_PropT_TauR : forall t1 t2 (HS: interp_PropTF RR sim t1 (observe t2)),
      interp_PropTF RR sim t1 (TauF t2)

  | Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R) ta
                         (t2 : itree' F R)

                         (k2 : A -> itree F R)

                         (HTA: h_spec A e ta)
                         (HK : forall (a : A), Returns a ta -> sim (k1 a) (k2 a))

                         (KS : k_spec A R e ta k2 (go t2)),
      interp_PropTF RR sim (VisF e k1) t2.

  Hint Constructors interp_PropTF : core.

  Lemma interp_PropTF_mono R RR (t0 : itree' E R) (t1 : itree' F R) sim sim'
        (IN : interp_PropTF RR sim t0 t1)
        (LE : sim <2= sim') :
    (interp_PropTF RR sim' t0 t1).
  Proof.
    induction IN; eauto.
  Qed.

  Hint Resolve interp_PropTF_mono : paco.

  Definition interp_PropT_ R RR sim (t0 : itree E R) (t1 : itree F R) :=
    interp_PropTF RR sim (observe t0) (observe t1).
  Hint Unfold interp_PropT_ : core.

  Lemma interp_PropT__mono R RR : monotone2 (interp_PropT_ R RR).
  Proof.
    do 2 red. intros. eapply interp_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_PropT__mono : paco.

  (* Definition 5.2 *)
  Definition interp_prop :
    forall R (RR: relation R), itree E R -> PropT F R :=
      fun R (RR: relation R) =>  paco2 (interp_PropT_ R RR) bot2.

  Arguments interp_prop {_}.

  Instance interp_prop_eq_itree_Proper_impl_ :
    forall R (x : _ R), Proper (eq_itree eq ==> impl) (interp_prop eq x).
  Proof.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until R.
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
    - pstep. red. rewrite <- Heqi. constructor.
      specialize (IHinterp_PropTF _ eq_refl _ _ Heqi0 EQ).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi.
      inv EQ; try inv CHECK; pclearbot.
      constructor. punfold REL.
      specialize (IHinterp_PropTF _ eq_refl _ m2 eq_refl REL).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi.
      econstructor; eauto; cycle 1.
      eapply k_spec_Proper. symmetry.
      assert (go t2 ≅ y') by (pstep; auto).
      rewrite <- H. reflexivity. eauto.
      intros. specialize (HK _ H). pclearbot.
      left. eapply paco2_mon; intros; eauto.
      inv PR.
  Qed.

  Instance interp_prop_eq_itree_Proper_impl :
    forall R, Proper (eq_itree eq ==> eq_itree eq ==> impl) (interp_prop (R := R) eq).
  Proof.
    repeat intro.
    rewrite <- H0. clear H0.
    clear y0. rename H1 into H0. rename y into x'. rename x0 into y.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until R.
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
      inv EQ; try inv CHECK; pclearbot.
      constructor. punfold REL.
      specialize (IHinterp_PropTF _ _ eq_refl _ eq_refl REL).
      punfold IHinterp_PropTF.
    - pstep. red. rewrite <- Heqi0. constructor.
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
      intros. specialize (HK _ H). pclearbot.
      punfold HK.
      right. eapply CIH; eauto.
      specialize (H0 a). punfold H0.
  Qed.

  Instance interp_prop_eq_itree_Proper :
    forall R, Proper (eq_itree eq ==> eq_itree eq ==> iff) (interp_prop (R := R) eq).
  Proof.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.

  Lemma interp_prop_inv_tau_r {R} RR (t0 : _ R) t1:
    interp_prop RR t0 (Tau t1) ->
    interp_prop RR t0 t1.
  Proof.
  Admitted.

  Instance interp_prop_eutt_Proper_impl_ :
    forall R (x : _ R), Proper (eutt eq ==> impl) (interp_prop eq x).
  Proof.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until R.
    pcofix CIH.
    intros x y y' EQ H.
    remember (observe x); remember (observe y).
    pstep. red. genobs_clear y' oy'.
    revert x Heqi y Heqi0 EQ.
    (* induct on interp_prop *)
    rename i into xo, i0 into yo.
    induction H; subst; pclearbot; intros.
    - rewrite <- Heqi.
      remember (RetF (E:= F) r2).
      induction EQ; inv Heqi1; intros.
      + constructor; auto.
      + constructor. eapply IHEQ; eauto.

    - rewrite <- Heqi.
      rename oy' into ot3.
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
          specialize (H _ eq (upaco2 (interp_PropT_ R eq) r) A e k1 ta (VisF e0 k3)).
          eapply H; eauto.
          intros.
          left. specialize (HK _ H0). pclearbot.
          eapply paco2_mon; eauto. intros; inv PR.
          eapply k_spec_Proper. eapply eqit_Vis. symmetry. pclearbot. eapply REL.
          eapply k_spec_Proper. Unshelve.
          3 : exact (go t2).
          rewrite Heqot. eapply eqit_Vis; reflexivity.
          auto.
        * eapply IHREL; eauto. pstep_reverse.
          assert (interp_prop eq t0 (Tau t1)) by (pstep; auto).
          apply interp_prop_inv_tau_r in H. punfold H.
    - rewrite <- Heqi. constructor.
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
      eapply k_spec_Proper. rewrite Heqi0 in EQ.
      symmetry. pstep; red; eauto. rewrite Heqi0 in KS.
      eapply k_spec_Proper. 2 : eauto. rewrite <- itree_eta; reflexivity.
      intros. specialize (HK _ H). pclearbot.
      left. eapply paco2_mon; intros; eauto.
      inv PR.
  Qed.

  Instance interp_prop_eutt_Proper_impl :
    forall R, Proper (eutt eq ==> eutt eq ==> impl) (interp_prop (R := R) eq).
  Proof.
  Admitted.

  (* Figure 7: Interpreter law for Ret *)
  Lemma interp_prop_ret :
    forall R (r : R),
      (interp_prop eq (ret r) ≈ ret r)%monad.
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
        constructor; eapply IHeqitF; eauto.
    - do 3 red. intros; split; intros; [rewrite <- H | rewrite H] ; auto.
    - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption.
  Qed.

  From ITree Require Import Eq.EqAxiom.

  Lemma interp_prop_bind_refine:
      forall (R : Type) (t : itree E R) (k : R -> itree E R) (y : itree F R),
        (x0 <- interp_prop eq t;; interp_prop eq (k x0)) y -> interp_prop eq (x <- t;; k x) y.
  Proof.
    intros R t k y H0.
    destruct H0 as (x0&x1&?&?&?).
    rewrite H0. clear H0. clear y.
    setoid_rewrite unfold_bind.
    match goal with
    | |- interp_prop _ ?l ?r => remember l; remember r
    end.
    revert_until R. pcofix CIH. intros.
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
    - rewrite Heqi. pstep. constructor.
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
    - rewrite Heqi0. pstep. constructor.
      specialize (IHinterp_PropTF _ t2 Heqi1 eq_refl).
      assert (forall a : R, Returns a t2 -> interp_prop eq (k a) (k' a)).
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
        eapply k_spec_Returns; eauto.
      + match goal with
        | |- k_spec _ _ _ _ ?l _ => remember l
        end.
        assert (i0 = (fun a => k2 a >>= k')). {
          apply FunctionalExtensionality.functional_extensionality.
          intros; apply bisimulation_is_eq. rewrite Heqi3.
          rewrite <- unfold_bind; reflexivity.
        }
        assert (i' = (go t2) >>= k'). {
          apply bisimulation_is_eq. rewrite Heqi0.
          setoid_rewrite unfold_bind; reflexivity.
        }
        eapply k_spec_Proper.
        rewrite <- itree_eta; reflexivity.
        rewrite H, H0. eapply k_spec_bind; eauto.
  Qed.

  Inductive may_converge {A : Type} (a : A) : itree E A -> Prop :=
  | conv_ret (t : itree E A) : t ≈ Ret a -> may_converge a t
  | conv_vis (t : itree E A ) {B : Type} (e : E B) (k : B -> itree E A):
      t ≈ Vis e k -> (forall b, may_converge a (k b)) -> may_converge a t.
  Hint Constructors may_converge : itree.

  #[global]
  Instance eutt_proper_con_converge {A} {a : A} : Proper (eutt eq ==> iff) (@may_converge _ a).
  Proof.
    intros t1 t2 Ht. split; intros.
    - induction H.
      + apply conv_ret; auto. rewrite <- Ht. auto.
      + eapply conv_vis; eauto. rewrite <- H.
        symmetry. auto.
    - induction H.
      + apply conv_ret; auto. rewrite Ht. auto.
      + eapply conv_vis; eauto. rewrite Ht.
        eauto.
  Qed.

  From Coq Require Import Logic.Classical_Prop.

  Lemma interp_prop_ret_pure :
    forall {T E F} (RR : relation T) `{REF: Reflexive _ RR} (x : T)
      (h : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop),
    interp_prop RR (ret x) (ret x).
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
    forall {T E F} (RR : relation T) (x y : T)
      (h : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop),
      RR x y ->
      interp_prop RR (ret x) (ret y).
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
      forall R RR `{Reflexive _ RR} (t : _ R) t', t ≈ t' -> interp_prop RR t (interp h t').
  Proof.
    intros h HC KC R RR H t t' H1.
    revert t t' H1.
    pcofix CIH.
    intros t t' eq.
    pstep.
    red.
    unfold interp, Basics.iter, MonadIter_itree.
    punfold eq. red in eq.
    (* rewrite (itree_eta t) in eq. *)
    (* destruct (observe t). *)
    (* - rewrite <- eq. econstructor. reflexivity. rewrite <- eq. rewrite unfold_iter. cbn. rewrite Eq.bind_ret_l. cbn.  reflexivity. *)
    (* - econstructor. right. *)
    (*   eapply CIH. rewrite tau_eutt in eq. rewrite eq. reflexivity. *)
    (* - econstructor. *)
    (*   apply HC. *)
    (*   intros a. cbn. *)
    (*   right. *)
    (*   unfold interp, Basics.iter, MonadIter_itree in CIH. unfold fmap, Functor_itree, ITree.map in CIH. *)
    (*   specialize (CIH (k a) (k a)). *)
    (*   apply CIH. *)
    (*   reflexivity. *)

    (*   unfold k_spec_correct in KC. *)

    (*   eapply KC. *)
    (*   rewrite <- eq. *)
    (*   rewrite unfold_iter. *)
    (*   cbn. *)

    (*   rewrite bind_map. *)
    (*   eapply eutt_clo_bind. *)
    (*   reflexivity. *)
    (*   intros u1 u2 H0; subst. *)

    (*   rewrite tau_eutt. *)
    (*   reflexivity. *)
  Admitted.

  (* Figure 7: interp Trigger law *)
  (* morally, we should only work with "proper" triggers everywhere *)
  (* Lemma interp_prop_trigger : *)
  (*   forall E F *)
  (*     (h_spec : E ~> PropT F) *)
  (*     R (e : E R) *)
  (*     (HP : forall T R k t2, Proper (eq ==> Eq1_PropT T) (fun e ift => h_spec T R e ift k t2)) *)
  (*   , (forall k t2, Eq1_PropT _ (interp_prop h_spec k_spec R eq (trigger e)) (fun ifr => h_spec R R R e ifr k t2)). *)
  (* Proof. *)
  (*   intros. *)
  (*   red. *)
  (*   split; [| split]. *)
  (*   - intros; split; intros. *)
  (*     + unfold trigger in H0. red in H0. *)
  (*       pinversion H0; subst. *)
  (*       apply inj_pair2 in H3. apply inj_pair2 in H4. *)
  (*       subst. *)
  (*       unfold subevent, resum, ReSum_id, Id_IFun, id_ in HTA. *)
  (*       rewrite eq2 in H. *)
  (*       assert (x <- ta ;; k2 x ≈ ta). *)
  (*       { rewrite <- (Eq.bind_ret_r ta). *)
  (*         apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta). *)
  (*         rewrite Eq.bind_ret_r. apply eutt_Returns. *)
  (*         intros. destruct H1. subst. specialize (HK u2 H2). pclearbot. pinversion HK. subst. assumption. *)
  (*       } *)
  (*       rewrite H1 in H. *)
  (*       specialize (HP R e e eq_refl).  unfold Eq1_PropT in HP. destruct HP as (P & _ & _). *)
  (*       rewrite P. apply HTA. symmetry. assumption. *)
  (*     + unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_. *)
  (*       red. pstep. eapply Interp_PropT_Vis with (k2 := (fun x : R => Ret x)). *)
  (*       * apply H0. *)
  (*       * unfold bind, Monad_itree. rewrite Eq.bind_ret_r. assumption. *)
  (*       * intros a. left. pstep. red. econstructor. reflexivity.  reflexivity. *)
  (*   - do 4 red. intros; split; intros. *)
  (*     rewrite <- H. assumption. *)
  (*     rewrite H. assumption. *)
  (*   - do 4 red. *)
  (*     intros; split; intros. *)
  (*     specialize (HP R e e eq_refl). destruct HP as (P & _ & _). *)
  (*     rewrite P; eauto. symmetry. assumption. *)
  (*     specialize (HP R e e eq_refl). destruct HP as (P & _ & _). *)
  (*     rewrite P; eauto. *)
  (* Qed. *)

End interp_prop.
