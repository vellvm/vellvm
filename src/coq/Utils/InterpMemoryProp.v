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

(* TODO: Move this? *)
Ltac inj_pair2_existT :=
  repeat
    match goal with
    | H : _ |- _ => apply inj_pair2 in H
    end.

Ltac subst_existT :=
  inj_pair2_existT; subst.

Section interp_memory_prop.

  Context {S1 S2 : Type}.
  Context {E F OOM : Type -> Type} {OOMF: OOM -< F}.
  Notation stateful R := (S2 * (S1 * R))%type.

  Notation interp_memory_h_spec := (forall T, E T -> stateT S1 (stateT S2 (PropT F)) T).
  Notation interp_memory_k_spec := (forall T R2, E T -> itree F (stateful T) -> (stateful T -> itree F (stateful R2)) -> itree F (stateful R2) -> Prop).

  Context (h_spec : interp_memory_h_spec) {R1 R2 : Type} (RR : R1 -> stateful R2 -> Prop).
  Context (k_spec : interp_memory_k_spec).

  Definition k_spec_correct : Prop
    := forall T (R2 : Type) e k2 t2 s1 s2 ta,
      h_spec _ e s1 s2 ta ->
      t2 ≈ bind ta k2 ->
      k_spec T R2 e ta k2 t2.

  Definition k_spec_correct_exec
             (h: forall T, E T -> itree F (stateful T)) : Prop
    := forall T R2 e k2 t2, t2 ≈ bind (h T e) k2 -> k_spec T R2 e (h T e) k2 t2.

  (* Well-formedness conditions for k_specs *)
  Class k_spec_WF := {
      (* k_spec_Returns: forall {A R2} ta k2 t2 e, *)
      (*   k_spec A R2 e ta k2 t2 -> forall a, Returns a ta -> forall a', Returns a' (k2 a) -> Returns a' t2; *)
      (* (* Not sure what this is supposed to be... *) *)
      (* k_spec_bind: forall {A R1 R2} ta k1 k2 (t2 : itree F _) e (k' : R1 -> itree F R2), *)
      (*   k_spec A R1 R2 e ta k1 k2 t2 -> *)
      (*   k_spec A R1 R2 e ta k1 (fun x => bind (k2 x) k') (bind t2 k'); *)
      k_spec_Proper : forall {A R2} e ta k2,
        Proper (eutt eq  ==>  iff) (@k_spec A R2 e ta k2);
      k_spec_Correct : k_spec_correct;
      (* k_spec_respects_h_spec : forall {A} t2 (ta : itree F _) (k : _ -> itree F _) e s1 s2, *)
      (*   (* The interpretation of `e` can yield `ta` *) *)
      (*   h_spec _ e s1 s2 ta -> *)
      (*   (* t2 provides a valid handling of `e` + the continuation *) *)
      (*   t2 ≈ x <- ta;; k x -> *)
      (*   k_spec A R1 R2 e ta k1 k2 t2 -> *)
      (*   (* We can handle e with x...???? *) *)
      (*   h_spec _ e s1 s2 x *)
    }.

  Context (k_spec_wellformed : k_spec_WF).

  (* A more general proper relation with k_spec and eutt, allowing the
     states to be compared differently *)
  Class k_spec_Proper_S1S2 (RS1 : relation S1) (RS2 : relation S2) := {
      k_spec_Proper_RR_Proper : forall {A R2} e ta k2,
        Proper (eutt (prod_rel RS2 (prod_rel RS1 eq)) ==> iff) (@k_spec A R2 e ta k2);
    }.

  Inductive interp_memory_PropTF
            (b1 b2 : bool) (sim : itree E R1 -> itree F (stateful R2) -> Prop)
            : itree' E R1 -> itree' F (stateful R2) -> Prop :=
  | Interp_Memory_PropT_Ret : forall (r1 : R1) (r2 : stateful R2) (REL: RR r1 r2),
      interp_memory_PropTF b1 b2 sim (RetF r1) (RetF r2)

  | Interp_Memory_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_memory_PropTF b1 b2 sim (TauF t1) (TauF t2)

  | Interp_Memory_PropT_TauL : forall t1 t2
                          (CHECK: is_true b1)
                          (HS: interp_memory_PropTF b1 b2 sim (observe t1) t2),
      interp_memory_PropTF b1 b2 sim (TauF t1) t2

  | Interp_Memory_PropT_TauR : forall t1 t2
                          (CHECK: is_true b2)
                          (HS: interp_memory_PropTF b1 b2 sim t1 (observe t2)),
      interp_memory_PropTF b1 b2 sim t1 (TauF t2)

  | Interp_Memory_PropT_Vis_OOM : forall A (e : OOM A) k t1 t2
                         (HT1: t2 ≅ vis e k),
      interp_memory_PropTF b1 b2 sim t1 (observe t2)

  | Interp_Memory_PropT_Vis : forall A (e : E A)
                         (ta : itree F (stateful A))
                         t2 s1 s2
                         (k1 : A -> itree E R1)
                         (k2 : stateful A -> itree F (stateful R2))
                         (HK : forall a b, @Returns E A a (trigger e) ->
                                           @Returns F (stateful A) b ta ->
                                           a = snd (snd b) ->
                                           sim (k1 a) (k2 b))
                         (HSPEC : h_spec _ e s1 s2 ta)

                         (* k_spec => t2 ≈ bind ta k2 *)
                         (* k_spec => True *)
                         (KS : k_spec A R2 e ta k2 t2), 
        interp_memory_PropTF b1 b2 sim (VisF e k1) (observe t2).

  Hint Constructors interp_memory_PropTF : core.

  Lemma interp_memory_PropTF_mono b1 b2 x0 x1 sim sim'
        (IN: interp_memory_PropTF b1 b2 sim x0 x1)
        (LE: sim <2= sim'):
    interp_memory_PropTF b1 b2 sim' x0 x1.
  Proof using.
    intros. induction IN; eauto.
  Qed.

  Hint Resolve interp_memory_PropTF_mono : paco.

  Definition interp_memory_PropT_ b1 b2 sim t0 t1 :=
    interp_memory_PropTF b1 b2 sim (observe t0) (observe t1).
  Hint Unfold interp_memory_PropT_ : core.

  Lemma interp_memory_PropT__mono b1 b2 : monotone2 (interp_memory_PropT_ b1 b2).
  Proof using.
    do 2 red. intros. eapply interp_memory_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_memory_PropT__mono : paco.

  Lemma interp_memory_PropT_idclo_mono: monotone2 (@id (itree E R1 -> itree F R2 -> Prop)).
  Proof using. unfold id. eauto. Qed.
  Hint Resolve interp_memory_PropT_idclo_mono : paco.

  Definition interp_memory_prop' b1 b2 :=
    paco2 (interp_memory_PropT_ b1 b2) bot2.

  Definition interp_memory_prop :=
    interp_memory_prop' true true.

  #[global] Instance interp_memory_prop_eq_itree_Proper_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> impl) interp_memory_prop.
  Proof using.
    repeat intro.
    repeat intro. eapply bisimulation_is_eq in H, H0; subst; eauto.
  Qed.

  #[global] Instance interp_memory_prop_eq_itree_Proper :
    Proper (eq_itree eq ==> eq_itree eq ==> iff) interp_memory_prop.
  Proof using.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.

  #[global] Instance interp_memory_prop_eq_itree_Proper_flip_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl) interp_memory_prop.
  Proof using.
    pose proof interp_memory_prop_eq_itree_Proper as PROP.
    unfold Proper, respectful in *.
    intros x y H x0 y0 H0.
    do 2 red. intros INTERP.
    eapply PROP; eauto.
  Qed.

  Lemma interp_memory_prop_inv_tau_r t0 t1:
    interp_memory_prop t0 (Tau t1) ->
    interp_memory_prop t0 t1.
  Proof using E F OOM OOMF R1 R2 RR S1 S2 h_spec k_spec k_spec_wellformed.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t0).
    remember (observe t0); remember (TauF t1).
    revert t0 Heqi t1 Heqi0.
    induction H; intros; inv Heqi0; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_memory_PropTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_memory_PropTF.
      punfold IHinterp_memory_PropTF.
    - rewrite <- itree_eta. pstep; auto.
    - rewrite itree_eta in HT1.
      rewrite H0 in HT1.
      pinversion HT1; subst.
      dependent induction REL.
    - pstep; eapply Interp_Memory_PropT_Vis; eauto.
      + eapply k_spec_Proper with (y:=t2); eauto.
        rewrite <- tau_eutt.
        pstep; red; cbn.
        rewrite H0.
        apply EqTau.
        left.
        apply Reflexive_eqit_eq.
  Qed.

  Lemma interp_memory_prop_inv_tau_l t0 t1:
    interp_memory_prop (Tau t0) t1 ->
    interp_memory_prop t0 t1.
  Proof using.
    intros H.
    punfold H; red in H; cbn in H.
    rewrite (itree_eta t1).
    remember (TauF t0); remember (observe t1).
    revert t0 Heqi t1 Heqi0.
    dependent induction H; intros; inv Heqi; pclearbot; eauto.
    - pstep; constructor; punfold HS; auto.
    - rewrite <- itree_eta. pstep; auto.
    - pstep; constructor; auto.
      specialize (IHinterp_memory_PropTF _ eq_refl _ eq_refl).
      rewrite <- itree_eta in IHinterp_memory_PropTF.
      punfold IHinterp_memory_PropTF.
    - apply eqitree_inv_Vis_r in HT1.
      destruct HT1.
      destruct H.
      rewrite H.
      pstep; red; cbn.
      change (VisF (subevent A e) x) with (observe (Vis (subevent A e) x)).
      eapply Interp_Memory_PropT_Vis_OOM.
      reflexivity.
  Qed.

  Lemma interp_memory_prop_inv_tau t0 t1:
    interp_memory_prop (Tau t0) (Tau t1) ->
    interp_memory_prop t0 t1.
  Proof using E F OOM OOMF R1 R2 RR S1 S2 h_spec k_spec k_spec_wellformed.
    intros H.
    apply interp_memory_prop_inv_tau_l in H.
    apply interp_memory_prop_inv_tau_r in H; auto.
  Qed.

  #[global] Instance interp_memory_prop_eutt_Proper_impl_ :
    forall x, Proper (eutt eq ==> impl) (interp_memory_prop x).
  Proof using E F OOM OOMF R1 R2 RR S1 S2 h_spec k_spec k_spec_wellformed.
    repeat intro. red in H0.
    punfold H; punfold H0; red in H; red in H0; cbn in *.
    revert_until k_spec.
    pcofix CIH; intros k_spec_wellformed x y y' EQ H.
    remember (observe x); remember (observe y).
    pstep. red.
    revert x Heqi y Heqi0 EQ.
    (* induct on interp_memory_prop *)
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
          eapply interp_memory_PropTF_mono; eauto.
          intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
        * remember (VisF e k1) as ot.
          hinduction HS before CIH; intros; try discriminate; eauto.
          -- change (VisF e0 k2) with (observe (Vis e0 k2)).
             rewrite itree_eta in HT1.
             rewrite Heqot in HT1.
             pinversion HT1.
             repeat subst_existT.
             eapply Interp_Memory_PropT_Vis_OOM.
             reflexivity.
          -- change (VisF e0 k3) with (observe (Vis e0 k3)).
             eapply Interp_Memory_PropT_Vis.
             ++ intros a b H1 H2 H3.
                left. specialize (HK _ b H1 H2 H3). pclearbot.
                eapply paco2_mon; eauto. intros; inv PR.
             ++ eauto.
             ++ eapply k_spec_wellformed with (y:=t2); eauto.
                pstep; red; cbn.
                rewrite Heqot.
                constructor.

                unfold id in *.
                intros v; pclearbot.
                left.
                apply Symmetric_eqit_eq.
                apply REL.
        * eapply IHREL; eauto. pstep_reverse.
          assert (interp_memory_prop t0 (Tau t1)) by (pstep; auto).
          apply interp_memory_prop_inv_tau_r in H. punfold H.
    - rewrite <- Heqi. constructor; auto.
      specialize (IHinterp_memory_PropTF _ eq_refl _ Heqi0 EQ). auto.
    - rewrite <- Heqi.
      remember (TauF t2) as ot. clear Heqi0 y.
      hinduction EQ before CIH; intros; try inversion Heqot; pclearbot; subst; eauto.
      punfold REL.
      eapply IHinterp_memory_PropTF; eauto.
      constructor; eauto.
      assert (Tau t0 ≈ t2). { pstep; auto. }
      apply eqit_inv_Tau_l in H1; punfold H1.
      eapply IHinterp_memory_PropTF; eauto.
      constructor; eauto.
    - rewrite itree_eta in HT1.
      hinduction EQ before CIH; intros.
      + pinversion HT1.
      + pinversion HT1.
        inv CHECK.
      + pinversion HT1; repeat subst_existT.
        change (VisF (subevent A e0) k2) with (observe (Vis (subevent A e0) k2)).
        eapply Interp_Memory_PropT_Vis_OOM.
        reflexivity.
      + pinversion HT1.
        inv CHECK0.
      + constructor; auto.
        eapply IHEQ; eauto.
    - rewrite <- Heqi.
      rewrite Heqi0 in EQ.
      assert (t2 ≈ y) as TSY.
      { rewrite (itree_eta t2).
        rewrite Heqi0.
        rewrite <- itree_eta.
        reflexivity.
      }

      assert (KS':k_spec A R2 e ta k2 y).
      { eapply k_spec_Proper; eauto.
        symmetry; auto.
      }

      eapply Interp_Memory_PropT_Vis; eauto.
      intros; eauto.
      specialize (HK _ _ H H0 H1). pclearbot.
      left. eapply paco2_mon_bot; intros; eauto.

      { eapply k_spec_wellformed with (y:=y); eauto.
        apply Symmetric_eqit_eq.
        pstep; red; cbn; auto.
      }
  Qed.

  #[global] Instance interp_memory_prop_eutt_Proper_impl :
    Proper (eutt eq ==> eutt eq ==> impl) (interp_memory_prop).
  Proof using E F OOM OOMF R1 R2 RR S1 S2 h_spec k_spec k_spec_wellformed.
    intros y y' EQ x x' EQ' H.
    rewrite <- EQ'. clear x' EQ'.
    punfold H; punfold EQ; red in H; red in EQ; cbn in *.
    revert_until k_spec_wellformed.
    pcofix CIH.
    intros x x' EQ y H.
    remember (observe x); remember (observe y).
    pstep. red. genobs_clear x' ox'.
    revert x Heqi y Heqi0 EQ.
    (* induct on interp_memory_prop *)
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
          eapply interp_memory_PropTF_mono; eauto.
          intros; left; pclearbot; eapply paco2_mon; eauto; intros; inv PR0.
        * remember (VisF e k1) as ot.
          hinduction HS before CIH; intros; try discriminate; eauto.
          -- inv Heqot.
             subst_existT.
             eapply Interp_Memory_PropT_Vis; eauto.
             intros a b H1 H2 H3.
             right.
             eapply CIH; eauto.
             specialize (REL a). pclearbot. punfold REL.
             specialize (HK _ _ H1 H2 H3). pclearbot.
             punfold HK.

             

        * eapply IHREL; eauto. pstep_reverse.
          assert (interp_memory_prop (Tau t0) t2) by (pstep; auto).
          apply interp_memory_prop_inv_tau_l in H. punfold H.
    - specialize (IHinterp_memory_PropTF _ eq_refl _ Heqi0).
      assert (t1 ≈ go ox').
      { rewrite <- tau_eutt; pstep; auto. }
      punfold H0.
    - rewrite <- Heqi0.
      constructor; auto. eapply IHinterp_memory_PropTF; eauto.
    - apply eqitree_inv_Vis_r in HT1.
      destruct HT1.
      destruct H.
      rewrite <- Heqi0.
      rewrite H.
      change (VisF (subevent A e) x0) with (observe (Vis (subevent A e) x0)).
      eapply Interp_Memory_PropT_Vis_OOM.
      reflexivity.
    - rewrite Heqi in EQ.
      hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; inv Heqi.
      + dependent destruction H1.
        eapply Interp_Memory_PropT_Vis; eauto.
        intros. specialize (HK _ _ H H0 H1); pclearbot.
        right; eapply CIH; [ | punfold HK].
        specialize (REL a).
        punfold REL.

        eapply k_spec_Proper; eauto.
        rewrite (itree_eta t2), Heqi0, <- itree_eta.
        reflexivity.
      + econstructor; eauto.
  Qed.

  #[global] Instance interp_memory_prop_eutt_Proper :
    Proper (eutt eq ==> eutt eq ==> iff) interp_memory_prop.
  Proof using E F OOM OOMF R1 R2 RR S1 S2 h_spec k_spec k_spec_wellformed.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.

  (* OOM case changes this lemma, and it may require knowing that OOM events only return void *)
  Lemma interp_memory_prop_ret_inv:
    forall r1 t,
      interp_memory_prop (ret r1) t -> (exists r2 , RR r1 r2 /\ t ≈ ret r2) \/ (exists A (e : OOM A) k, t ≈ vis e k)%type.
  Proof using.
    intros r1 t INTERP.
    punfold INTERP.
    red in INTERP.
    setoid_rewrite itree_eta with (t:=t).
    remember (observe (ret r1)); remember (observe t).
    clear Heqi0.
    dependent induction INTERP; subst; pclearbot; intros.
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
        destruct IHINTERP as [[r2 [RRr1r2 EQ]] | [A [e [k VIS]]]].
        * left.
          exists r2; split; auto.
          rewrite <- itree_eta in EQ.
          rewrite EQ.
          rewrite tau_eutt.
          reflexivity.
        * right.
          exists A.
          exists e. exists k.
          rewrite <- itree_eta in VIS.
          rewrite VIS.
          rewrite tau_eutt.
          reflexivity.
      + specialize (IHINTERP eq_refl).
        destruct IHINTERP as [[r2 [RRr1r2 EQ]] | [A' [e' [k' VIS]]]].
        * left.
          exists r2; split; auto.
          rewrite <- itree_eta in EQ.
          rewrite EQ.
          rewrite tau_eutt.
          reflexivity.
        * right.
          exists A'. exists e'. exists k'.
          rewrite <- itree_eta in VIS.
          rewrite VIS.
          rewrite tau_eutt.
          reflexivity.
    - right.
      apply eqitree_inv_Vis_r in HT1.
      destruct HT1 as [k' [VIS K]].
      exists A. exists e. exists k.
      rewrite VIS.
      pstep; red; cbn.
      constructor.
      intros v. red.
      left.
      rewrite K.
      assert (k v ≈ k v) by reflexivity.
      auto.
    - inv Heqi.
  Qed.

  Lemma interp_memory_prop_vis :
    forall {X} (e : E X) k t ta k' s1 s2,
      t ≈ x <- ta;; k' x ->
      h_spec X e s1 s2 ta ->
      (forall (a : X) (b : stateful X),
          @Returns E X a (trigger e) ->
          Returns b ta -> a = snd (snd b) -> interp_memory_prop (k a) (k' b)) ->
      interp_memory_prop (Vis e k) t.
  Proof using All.
    intros.
    red; pstep; eapply Interp_Memory_PropT_Vis; eauto.
    intros. left; eauto. eapply H1; eauto.
    eapply k_spec_Correct; eauto.
  Qed.

End interp_memory_prop.

Arguments interp_memory_prop {_ _ _ _ _ _} _ {_ _}.
Arguments interp_memory_prop' {_ _ _ _ _ _} _ {_ _}.

Hint Constructors interp_memory_PropTF : core.
Hint Resolve interp_memory_PropTF_mono : paco.
Hint Unfold interp_memory_PropT_ : core.
Hint Resolve interp_memory_PropT__mono : paco.
Hint Resolve interp_memory_PropT_idclo_mono : paco.

#[global] Instance interp_memory_prop_Proper_eq :
  forall S1 S2 (E F OOM : Type -> Type) `{OOME: OOM -< F}
    h_spec
    k_spec `{KS_WF : @k_spec_WF _ _ E F h_spec k_spec}
    R (RR : R -> R -> Prop) (HR: Reflexive RR) (HT : Transitive RR),
    Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_memory_prop S1 S2 E F OOM OOME h_spec _ _ (fun x '(_, (_, y)) => RR x y) k_spec).
Proof using.
  intros S1 S2 E F OOM OOME h_spec k_spec KS_WF R RR REFL TRANS.
  intros y y' EQ x x' EQ' H. subst.
  punfold H; punfold EQ; red in H; red in EQ; cbn in *.
  revert_until TRANS.
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
    hinduction EQ before REL; intros; inv Heqi1; inv Heqi; intros.
    + constructor; eauto.
      destruct r2. destruct p; eauto.
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
        -- econstructor; eauto. destruct r2, p; eauto.
        -- econstructor; eauto.
        -- apply eqitree_inv_Vis_r in HT1.
           destruct HT1 as [k' [VIS K]].
           rewrite VIS.
           change (VisF (subevent A e) k') with (observe (Vis (subevent A e) k')).
           eapply Interp_Memory_PropT_Vis_OOM.
           reflexivity.
      * remember (VisF e k2) as ot.
        hinduction HS before CIH; intros; try discriminate; eauto.
        -- inv Heqot; subst_existT.
           eapply Interp_Memory_PropT_Vis; eauto.
           intros a b H1 H2 H3.
           right.
           eapply CIH; eauto.
           specialize (REL a). pclearbot. punfold REL.
           specialize (HK _ _ H1 H2 H3). pclearbot.
           punfold HK.
      * eapply IHREL; eauto. pstep_reverse.
        assert (interp_memory_prop (OOMF:=OOME) h_spec (fun x '(_, (_, y)) => RR x y) k_spec (Tau t2) t0) by (pstep; auto).
        apply interp_memory_prop_inv_tau_l in H. punfold H.
  - specialize (IHinterp_memory_PropTF _ Heqi _ Heqi0).
    assert (eutt RR (go xo) t1).
    { rewrite <- (tau_eutt t1); pstep; auto. }
    punfold H0.
  - rewrite <- Heqi0.
    constructor; auto.
  - subst.
    punfold HT1.
    red in HT1.
    cbn in HT1.
    dependent induction HT1.
    rewrite <- Heqi0.
    rewrite <- x.
    change (VisF (subevent A e) k1) with (observe (Vis (subevent A e) k1)).
    eapply Interp_Memory_PropT_Vis_OOM.
    reflexivity.
  - rewrite Heqi in EQ.
    remember (VisF e k1).
    hinduction EQ before CIH; intros; try inversion Heqi1; pclearbot; inv Heqi.
    + dependent destruction H1.
      eapply Interp_Memory_PropT_Vis; eauto.
      intros. specialize (HK _ _ H H0 H1); pclearbot.
      right; eapply CIH; [ | punfold HK].
      specialize (REL a).

      punfold REL.

      eapply k_spec_Proper; eauto.
      rewrite (itree_eta t2), Heqi0, <- itree_eta.
      reflexivity.
    + econstructor; eauto.
Qed.
