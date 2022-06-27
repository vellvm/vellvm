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
             (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop) : Prop
    := forall T R e k1 k2 t2, t2 ≈ bind (h T e) k2 -> k_spec T R e (h T e) k1 k2 t2.

  Context {E F : Type -> Type}.
  Context (h_spec : E ~> PropT F).
  Context (k_spec : forall T R, E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop).

  (* Well-formedness conditions for k_specs *)
  Class k_spec_WF := {
      k_spec_Returns: forall {A R} ta k2 t2 e,
        k_spec A R e ta k2 t2 -> forall a, Returns a ta -> forall a', Returns a' (k2 a) -> Returns a' t2;
      k_spec_bind: forall {A R} ta k2 (t2 : itree F R) e (k' : _ -> itree F R),
        k_spec A R e ta k2 t2 ->
        k_spec A R e ta (fun x => bind (k2 x) k') (bind t2 k')
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

  | Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R)
                         (t2 : itree F R)

                         (ta :itree F A)
                         (k2 : A -> itree F R)

                         (HTA: h_spec A e ta)
                         (HK : forall (a : A), Returns a ta ->  sim (k1 a) (k2 a))

                         (* k_spec => t2 ≈ bind ta k2 *)
                         (* k_spec => True *)
                         (KS : k_spec A R e ta k2 t2),
      interp_PropTF RR sim (VisF e k1) (observe t2).

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

  Instance interp_prop_Proper_impl :
    forall R (x : _ R), Proper (eutt eq ==> impl) (interp_prop eq x).
  Proof.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    remember (observe x); remember (observe x0); remember (observe y).
    revert_until H. clear Heqi0 x0. revert x.
    pcofix CIH.
    intros; induction H; subst.
    - eapply paco2_mon. pstep; red; try rewrite <- Heqi1; eauto.
      intros; inv PR.
    - pstep; red; rewrite <- Heqi1. inv H1; pclearbot.
      + constructor. right.
  Abort.

  Instance interp_prop_eq_itree_Proper :
    forall R, Proper (eq_itree eq ==> eq_itree eq ==> iff) (interp_prop (R := R) eq).
  Proof.
    repeat intro.
  Admitted.

  Instance interp_prop_eutt_Proper :
    forall R x, Proper (eutt eq ==> iff) (interp_prop (R := R) eq x).
  Proof.
    repeat intro.
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

  Lemma interp_prop_bind_flip_impl:
      forall (R : Type) (t : itree E R) (k : R -> itree E R),
        itree F R ->
        forall y : itree F R, (x0 <- interp_prop eq t;; interp_prop eq (k x0)) y -> interp_prop eq (x <- t;; k x) y.
  Proof.
    intros R t k x y H0.
    destruct H0 as (?&?&?&?&?).
    rewrite H0. clear H0. clear y.
    setoid_rewrite unfold_bind.
    match goal with
    | |- interp_prop _ ?l ?r => remember l; remember r
    end.
    revert_until R. pcofix CIH. intros.
    punfold H0; red in H0; cbn in H0.
    clear x. rename t into x, x2 into x'.
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
      pstep. subst. constructor. right. eapply CIH.
      4,5:eapply bisimulation_is_eq; rewrite unfold_bind; reflexivity.
      { auto. }
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
      + intros. specialize (HK _ H). pclearbot.
        right. eapply CIH; [ auto | ..].
        3,4 :eapply bisimulation_is_eq; setoid_rewrite <- unfold_bind; reflexivity.
        eauto.
        intros; eapply H1. rewrite (itree_eta x'). rewrite <- Heqi2.
        rewrite <- itree_eta.
        eapply k_spec_Returns; eauto.
      + match goal with
        | |- k_spec _ _ _ _ ?l _ => remember l
        end.
        assert (i0 = (fun a => k2 a >>= k')). {
          apply FunctionalExtensionality.functional_extensionality.
          intros; apply bisimulation_is_eq. rewrite Heqi3.
          rewrite <- unfold_bind; reflexivity.
        }
        assert (i' = t2 >>= k'). {
          apply bisimulation_is_eq. rewrite Heqi0; rewrite <- unfold_bind; reflexivity.
        }
        rewrite H, H0. eapply k_spec_bind; eauto.
  Qed.

  (* Interp bind law *)
  Lemma interp_prop_bind :
    forall R (t : _ R) (k : R -> _ R),
      (interp_prop eq (bind t k) ≈
                   bind (interp_prop eq t) (fun x => interp_prop eq (k x)))%monad.
  Proof.
    intros R t k.
    repeat red.
    split; [| split]; cycle 1.
    { do 3 red. intros; split; intros; [rewrite <- H | rewrite H] ; auto. }
    { do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption. }
    split; intros; [ rewrite <- H | rewrite H]; clear H;
      [ | eapply interp_prop_bind_flip_impl; eauto ].
    clear y.
    setoid_rewrite unfold_bind in H0.
    punfold H0; red in H0; cbn in H0.
    pose proof (itree_eta t). eapply bisimulation_is_eq in H.
    rewrite H. remember (observe t).
    remember (observe
            match i with
            | RetF r => k r
            | TauF t => Tau (ITree.bind t k)
            | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
            end); remember (observe x).
    clear t Heqi H.
    revert i x k Heqi0 Heqi1.
    induction H0; intros; subst; auto; pclearbot.
    - intros; subst; cbn.
      destruct i eqn: Ht; try inv Heqi0.
      eexists (ret r), _.
      split; [ | split]; eauto.
      + pstep; red; constructor; auto.
      + setoid_rewrite Eq.bind_ret_l. rewrite (itree_eta x), <- Heqi1. reflexivity.
      + intros. eapply Returns_ret_inv in H; subst.
        pstep; red. rewrite <- Heqi1, <- H0; constructor; auto.
    - (* coind tau *)
      (* tricky case : need to use classical reasoning to case-analyze on whether prefix of tree is finite *)
      admit.
    - (* tauL *)
      destruct i eqn: Hi; try inv Heqi0.
      + eexists (ret _), (fun _ => _).
        split. pstep. red. cbn. constructor ; auto.
        split; [ rewrite bind_ret_l; reflexivity |  ].
        intros. apply Returns_ret_inv in H; subst.
        rewrite (itree_eta (k r)). rewrite <- H1.
        pstep. constructor.
        specialize (IHinterp_PropTF (observe (ret r)) x (fun _ => t1) eq_refl eq_refl).
        destruct IHinterp_PropTF as (?&?&?&?&?). auto.
      + specialize (IHinterp_PropTF (observe t) x k).

        assert (H' : ITree.bind t k =
                      match observe t with
                      | RetF r => k r
                      | TauF t => Tau (ITree.bind t k)
                      | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
                      end). {
          eapply bisimulation_is_eq; rewrite unfold_bind; reflexivity.
        }
        rewrite H' in IHinterp_PropTF.
        specialize (IHinterp_PropTF eq_refl eq_refl).
        destruct IHinterp_PropTF as (?&?&?&?&?). eexists _, _.
        split; [ | split]; eauto.
        pstep; constructor; auto. rewrite <- itree_eta in H; auto. punfold H.
    - (* tauR *)
      specialize (IHinterp_PropTF i t2 k eq_refl eq_refl).
      destruct IHinterp_PropTF as (?&?&?&?&?). eexists _, _.
      split; [ | split]; eauto.
      rewrite (itree_eta x). rewrite <- Heqi1. rewrite tau_eutt. auto.
    - destruct i eqn: Ht; try inv Heqi0.
      + eexists (ret r), _.
        split; [ | split]; eauto.
        * pstep; red; constructor; auto.
        * setoid_rewrite Eq.bind_ret_l. rewrite (itree_eta x), <- Heqi1. reflexivity.
        * intros. eapply Returns_ret_inv in H; subst.
          pstep; red. rewrite <- Heqi1, <- H0. econstructor; eauto.
      + dependent destruction H1.
        repeat red.
        (* There needs to be an "atomic" split of the vis case *)
      admit.
  Admitted.

  Lemma interp_prop_ret_pure :
    forall {T E F} (RR : relation T) `{REF: Reflexive _ RR} (x : T)
      (h : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop),
    interp_prop h k_spec _ RR (ret x) (ret x).
  Proof.
    intros T E F RR REF x h k_spec.
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
      interp_prop h k_spec _ RR (ret x) (ret y).
  Proof.
    intros T E F RR x y h k_spec RRxy.
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
    forall {E F}
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      (h: E ~> itree F)
      (HC : handler_correct h_spec h)
      (KC : k_spec_correct h k_spec),
      forall R RR `{Reflexive _ RR} t t', t ≈ t' -> interp_prop h_spec k_spec R RR t (interp h t').
  Proof.
    intros E F h_spec k_spec h HC KC R RR H t t' H1.
    revert t t' H1.
    pcofix CIH.
    intros t t' eq.
    pstep.
    red.
    unfold interp, Basics.iter, MonadIter_itree.
    rewrite (itree_eta t) in eq.
    destruct (observe t).
    (* - econstructor. reflexivity. rewrite <- eq. rewrite unfold_iter. cbn. rewrite Eq.bind_ret_l. cbn.  reflexivity. *)
    (* - econstructor. right. *)
    (*   eapply CIH. rewrite tau_eutt in eq. rewrite eq. reflexivity. *)
    (* - econstructor. *)
    (*   apply HC. *)
    (*   intros a. cbn.   *)
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

  Lemma interp_prop_ret_inv :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR
      (r1 : R)
      (t : itree F R)
      (H : interp_prop h_spec k_spec R RR (ret r1) t),
       exists  r2, RR r1 r2 /\ t ≈ ret r2.
  Proof.
  Abort.

  Lemma interp_prop_vis_inv :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR S
      (e : E S)
      (k : S -> itree E R)
      (t : itree F R)
      (H : interp_prop h_spec k_spec R RR (vis e k) t), 
    exists  ms, exists (ks : S -> itree F R),
      h_spec S e ms /\ k_spec S R e ms k ks t.
  Proof.
    intros.
    punfold H.
    red in H. inversion H; subst.
  Abort.

End interp_prop.
