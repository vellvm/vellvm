From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMEvents.

From Mem Require Import
     OOM.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From Coq Require Import Relations.

Require Import Morphisms.
Require Import Paco.paco.
Require Import Coq.Program.Equality.

Ltac inv_existT :=
  repeat match goal with
         | H: existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; inversion H; subst
         end.

Ltac inv_observes :=
  repeat
    match goal with
    | H1 : _ = observe ?x,
        H2 : _ = observe ?x |- _ =>
        setoid_rewrite <- H1 in H2; inversion H2; subst
    end.

Section contains_UB.
  Context {E F G : Type -> Type}.
  #[local] Notation Eff := (E +' F +' UBE +' G).

  Inductive contains_UB {R} : itree Eff R -> Prop :=
  | CrawlTau  : forall t1 t2, t2 ≅ Tau t1 -> contains_UB t1 -> contains_UB t2
  | CrawlVis1 : forall Y (e : (E +' F) Y) x k t2, t2 ≅ (vis e k) -> contains_UB (k x) -> contains_UB t2
  | CrawlVis2 : forall Y (e : G Y) x k t2, t2 ≅ (vis e k) -> contains_UB (k x) -> contains_UB t2
  | FindUB    : forall s k t2, t2 ≅ (vis (subevent (F:=Eff) _ (ThrowUB s)) k) -> contains_UB t2.

  #[global] Instance proper_eutt_contains_UB {R} {RR : relation R} : Proper (@eqit Eff _ _ RR true true ==> iff) contains_UB.
  Proof using Type.
    unfold Proper, respectful.
    intros x y EQ.
    split; intros UB.
    { revert y EQ.
      induction UB.
      - intros y EQ.
        apply IHUB.
        rewrite <- (tau_eutt t1).
        rewrite <- H.
        auto.
      - rename Y into T.
        intros y EQ.
        punfold EQ; red in EQ.
        { remember (observe t2) as t2o.
          remember (observe y) as yo.
          revert e k t2 y H UB IHUB Heqt2o Heqyo.
          induction EQ; intros e' k t2' y H UB IHUB Heqt2o Heqyo.
          punfold H; red in H.
          rewrite <- Heqt2o in H.
          inversion H.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          cbn in H.
          inversion H; inversion CHECK.

          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            dependent induction H.

            eapply CrawlVis1 with (k:=k2) (e:=subevent T e').
            { symmetry.
              pfold; red.
              rewrite <- Heqyo.
              constructor; eauto.
              intros v.
              red. left.
              apply Reflexive_eqit. typeclasses eauto.
            }

            apply IHUB.
            pclearbot.
            eapply eutt_cong_eq.
            symmetry; apply REL0.
            reflexivity.
            apply REL.
          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            inversion H; inversion CHECK0.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t1 := t2).

            pfold; red; rewrite <- Heqyo.
            cbn.
            constructor; left.
            apply Reflexive_eqit. typeclasses eauto.
            eapply IHEQ; eauto.
            pfold; red; rewrite <- x.
            cbn; constructor; eauto.
        }
      - rename Y into T.
        intros y EQ.
        punfold EQ; red in EQ.
        { remember (observe t2) as t2o.
          remember (observe y) as yo.
          revert e k t2 y H UB IHUB Heqt2o Heqyo.
          induction EQ; intros e' k t2' y H UB IHUB Heqt2o Heqyo.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          inversion H.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          cbn in H.
          inversion H; inversion CHECK.

          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            dependent induction H.

            eapply CrawlVis2 with (k:=k2).
            { symmetry.
              pfold; red.
              rewrite <- Heqyo.
              cbn.
              econstructor; eauto.
              intros v.
              red. left.
              apply Reflexive_eqit. typeclasses eauto.
            }

            apply IHUB.
            pclearbot.
            eapply eutt_cong_eq.
            symmetry; apply REL0.
            reflexivity.
            apply REL.
          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            inversion H; inversion CHECK0.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t1 := t2).

            pfold; red; rewrite <- Heqyo.
            cbn.
            constructor; left.
            apply Reflexive_eqit. typeclasses eauto.
            eapply IHEQ; eauto.
            pfold; red; rewrite <- x.
            cbn; constructor; eauto.
        }
      - intros y EQ.
        punfold H; red in H.
        dependent induction H.
        punfold EQ; red in EQ.
        genobs t2 ot2. genobs y oy. clear t2 Heqot2.
        revert y Heqoy.

        induction EQ; try solve [inv x]; intros.
        + subst. inv x.
          dependent destruction H1.
          eapply FindUB.
          pfold; red.
          rewrite <- Heqoy.
          cbn.
          econstructor; intros [].
        + subst.
          eapply CrawlTau with (t1:=t2).
          pfold; red; rewrite <- Heqoy; cbn.
          constructor. left.
          apply Reflexive_eqit. typeclasses eauto.

          eapply IHEQ; eauto.
    }

    { revert x EQ.
      induction UB.
      - intros x EQ.
        apply IHUB.
        rewrite <- (tau_eutt t1).
        rewrite <- H.
        auto.
      - rename Y into T.
        rename x into v.
        intros x EQ.
        punfold EQ; red in EQ.
        { remember (observe t2) as t2o.
          remember (observe x) as xo.
          revert e k t2 x H UB IHUB Heqt2o Heqxo.
          induction EQ; intros e' k t2' x H UB IHUB Heqt2o Heqxo.
          punfold H; red in H.
          rewrite <- Heqt2o in H.
          inversion H.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          cbn in H.
          inversion H; inversion CHECK.

          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            dependent induction H.

            eapply CrawlVis1 with (k:=k1) (e:=subevent T e').
            { symmetry.
              pfold; red.
              rewrite <- Heqxo.
              constructor; eauto.
              intros v'.
              red. left.
              apply Reflexive_eqit. typeclasses eauto.
            }

            apply IHUB.
            pclearbot.
            eapply eutt_cong_eq.
            reflexivity.
            symmetry; apply REL0.
            apply REL.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t1 := t1).

            pfold; red; rewrite <- Heqxo.
            cbn.
            constructor; left.
            apply Reflexive_eqit. typeclasses eauto.
            eapply IHEQ; eauto.
            pfold; red; rewrite <- x.
            cbn; constructor; eauto.
          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            inversion H; inversion CHECK0.
        }
      - rename Y into T.
        intros y EQ.
        punfold EQ; red in EQ.
        { remember (observe t2) as t2o.
          remember (observe y) as yo.
          revert e k t2 y H UB IHUB Heqt2o Heqyo.
          induction EQ; intros e' k t2' y H UB IHUB Heqt2o Heqyo.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          inversion H.

          punfold H; red in H.
          rewrite <- Heqt2o in H.
          cbn in H.
          inversion H; inversion CHECK.

          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            dependent induction H.

            eapply CrawlVis2 with (k:=k1).
            { symmetry.
              pfold; red.
              rewrite <- Heqyo.
              cbn.
              econstructor; eauto.
              intros v.
              red. left.
              apply Reflexive_eqit. typeclasses eauto.
            }

            apply IHUB.
            pclearbot.
            eapply eutt_cong_eq.
            reflexivity.
            symmetry; apply REL0.
            apply REL.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t1 := t1).

            pfold; red; rewrite <- Heqyo.
            cbn.
            constructor; left.
            apply Reflexive_eqit. typeclasses eauto.
            eapply IHEQ; eauto.
            pfold; red; rewrite <- x.
            cbn; constructor; eauto.
          - punfold H; red in H.
            rewrite <- Heqt2o in H.
            cbn in H.
            inversion H; inversion CHECK0.
        }
      - intros y EQ.
        punfold H; red in H.
        dependent induction H.
        punfold EQ; red in EQ.

        genobs t2 ot2. genobs y oy. clear t2 Heqot2.
        revert y Heqoy.

        induction EQ; try solve [inv x]; intros.
        + subst. inv x.
          dependent destruction H1.
          eapply FindUB.
          pfold; red.
          rewrite <- Heqoy.
          cbn.
          econstructor; intros [].
        + subst.
          eapply CrawlTau with (t1:=t1).
          pfold; red; rewrite <- Heqoy; cbn.
          constructor. left.
          apply Reflexive_eqit. typeclasses eauto.

          eapply IHEQ; eauto.
    }

    Unshelve.

    all: intros [].
  Qed.

  (*
  (* TODO: Move this *)
  Definition stronger (x1 x2 b : bool) : Prop :=
    match b with
    | true =>
        (* Can remove taus, so anything is stronger *)
        True
    | false =>
        (* Can't remove taus *)
        match x1, x2 with
        | false, false =>
            True
        | _, _ =>
            False
        end
    end.

  #[global] Instance eqit_eqit_Proper :
    forall {E : Type -> Type} {R : Type} {RR : R -> R -> Prop} (bx1 bx2 by1 by2 b1 b2 : bool),
      stronger bx1 bx2 b1 ->
      stronger by1 by2 b2 ->
      Proper (eqit RR bx1 bx2 ==> eqit RR by1 by2 ==> iff) (@eqit E _ _ RR b1 b2).
  Proof.
    intros E0 R RR bx1 bx2 by1 by2 b1 b2 STRONGX STRONGY.
    unfold Proper, respectful.
    intros x x' XX y y' YY.
    split; intros XY.
    { destruct bx1, bx2, b1; inversion STRONGX.
      - rewrite XX in XY.

    }

  Qed.
*)

End contains_UB.

Section contains_UB_lemmas.
  Context {E F G : Type -> Type}.
  Local Notation Eff := (E +' F +' UBE +' G).

  Lemma ret_not_contains_UB {R} {RR : relation R} :
    forall (t : itree Eff R) rv, eqit RR true true t (ret rv) -> ~ contains_UB t.
  Proof using Type.
    intros t rv EQ CUB.
    rewrite EQ in CUB.
    inversion CUB; subst;
      pinversion H; inversion CHECK.
  Qed.

End contains_UB_lemmas.

Section bind_lemmas.
  Context {E F G : Type -> Type}.
  Local Notation Eff := (E +' F +' UBE +' G).

  Lemma bind_contains_UB :
    forall {R T} (t : itree Eff R) (k : R -> itree Eff T),
      contains_UB t ->
      contains_UB (ITree.bind t k).
  Proof using Type.
    intros R T t k CUB.
    induction CUB.
    - rewrite H.
      rewrite tau_eutt.
      eauto.
    - rewrite H.
      rewrite bind_vis.
      eapply CrawlVis1; [reflexivity | cbn; eauto].
    - rewrite H.
      rewrite bind_vis.
      eapply CrawlVis2; [reflexivity | cbn; eauto].
    - rewrite H.
      rewrite bind_vis.
      eapply FindUB; reflexivity.
  Qed.

  Lemma bind_contains_UB_k :
    forall {R T} (t : itree Eff R) (k : R -> itree Eff T) (a : R),
      (* Need to make sure `t` doesn't spin. *)
      Returns a t ->
      contains_UB (k a) ->
      contains_UB (ITree.bind t k).
  Proof using Type.
    intros R T t k a RET CUB.
    induction RET.
    - rewrite H; rewrite bind_ret_l; auto.
    - rewrite H; rewrite tau_eutt; eauto.
    - destruct e as [e | [f | [ube | g]]].
      + rewrite H.
        rewrite bind_vis.
        eapply CrawlVis1 with (e := (inl1 e)) (k := (fun x0 : X => ITree.bind (k0 x0) k)).
        reflexivity.
        eauto.
      + rewrite H.
        rewrite bind_vis.
        eapply CrawlVis1 with (e := (inr1 f)) (k := (fun x0 : X => ITree.bind (k0 x0) k)).
        reflexivity.
        eauto.
      + rewrite H.
        rewrite bind_vis.
        destruct ube.
        eapply FindUB with (s:=u) (k:=(fun x0 : void => ITree.bind (k0 x0) k)).
        reflexivity.
      + rewrite H.
        rewrite bind_vis.
        eapply CrawlVis2 with (e := g) (k := (fun x0 : X => ITree.bind (k0 x0) k)).
        reflexivity.
        eauto.
  Qed.

  Lemma bind_contains_UB' :
    forall {R T} (t : itree Eff R) (k : R -> itree Eff T),
      contains_UB (ITree.bind t k) ->
      (forall x, ~ contains_UB (k x)) ->
      contains_UB t.
  Proof.
    intros R T t k UB NUB.
  Admitted.
End bind_lemmas.

Section interp_lemmas.
  Context {E1 F1 G1 : Type -> Type}.
  Local Notation Eff1 := (E1 +' F1 +' UBE +' G1).

  Context {E2 F2 G2 : Type -> Type}.
  Local Notation Eff2 := (E2 +' F2 +' UBE +' G2).

  Variable (handler : Handler Eff1 Eff2).

  Definition handler_keeps_UB :=
    forall {R} (e : UBE R),
      contains_UB (handler _ ((inr1 (inr1 (inl1 e))) : Eff1 R)).

  (* We want a lemma about `interp` preserving `contains_UB`.

    It seems like we could say something like:

      Definition handler_keeps_UB := forall {R} (e : UBE R),
        contains_UB (handler _ ((inr1 (inr1 (inl1 e))) : Eff1 R)).

    Unfortunately, this isn't good enough to ensure:

      contains_UB (interp handler t).

    `handler_keeps_UB` isn't enough because there are other events
    besides `UBE` that `handler` interprets into itrees. Let's say I
    have some event `e : E bool`, and I have the following itree:

      maybe_UB :=
        b <- trigger e;;
        if b then raiseUB "UB happens!"else (ret 0)

    Depending on how `e` is handled the resulting tree may or may not
    have UB. If we look at the relevant constructor for `contains_UB`:

      | CrawlVis1 : forall Y (e : (E +' F) Y) x k t2, t2 ≅ (vis e k)
        -> contains_UB (k x) -> contains_UB t2

    We see that `maybe_UB` contains UB because there exists `x = true`
    that will make the continuation contain UB.

    However, if we have a `handler` which interprets `e` as `ret
    false`, then:

      interp handler maybe_UB :=
        ret false;;
        if b then raiseUB "UB happens!"else (ret 0)

    Which is of course just:

      interp handler maybe_UB := ret 0

    Which clearly contains no UB events.

    Another cause of problems is if the handler might produce a
    divergent itree.
   *)

  Lemma interp_contains_UB :
    forall {R} (t : itree Eff1 R),
      contains_UB t ->
      handler_keeps_UB ->
      (forall {T} (e : Eff1 T), exists a, Returns a (handler T e)) ->
      contains_UB (interp handler t).
  Proof.
    intros R t UB KEEP RET.
    Import InterpFacts.
    induction UB.
      try solve [rewrite H;
                 rewrite InterpFacts.interp_tau;
                 rewrite tau_eutt; eauto].
  Abort.
End interp_lemmas.


Section refine_OOM_h_lemmas.
  Context {E G : Type -> Type}.
  Local Notation Eff := (E +' OOME +' UBE +' G).

  Hint Resolve interp_PropT__mono : paco.

  (* Only the <- direction is true *)
  Global Instance proper_refine_OOM_h
           {R} {RR : relation R} : Proper (@refine_OOM_h Eff _ _ RR ==> flip impl) contains_UB.
    unfold Proper, respectful.
    intros x y EQ UB; revert x EQ.
    induction UB.
    (*   - intros x EQ. *)
    (*     apply IHUB. *)

    (*     unfold refine_OOM_h in *. *)
    (*     eapply interp_prop_eq_itree_Proper in EQ. *)
    (*     3 : symmetry; apply H. 3 : reflexivity. 2 : typeclasses eauto. *)
    (*     apply interp_prop_inv_tau_l in EQ. *)
    (*     auto. typeclasses eauto. *)
    (*   - rename Y into T. *)
    (*     rename x into v. *)
    (*     intros x EQ. *)
    (*     revert e k H UB IHUB. *)
    (*     punfold EQ; red in EQ. *)
    (*     genobs t2 t2o.  *)
    (*     revert t2 Heqt2o. *)
    (*     induction EQ; intros ? Heqt2o e' k H UB IHUB. *)
    (*     + punfold H; red in H. *)
    (*       rewrite <- Heqt2o in H. *)
    (*       inversion H. *)

    (*     + punfold H; red in H. *)
    (*       rewrite <- Heqt2o in H. *)
    (*       inversion H; inversion CHECK. *)

    (*     + punfold H; red in H. *)
    (*       rewrite <- Heqt2o in H. *)
    (*       inversion H; inversion CHECK. *)

    (*     + punfold H; red in H. *)

    (*     + punfold H; red in H. *)
    (*       rewrite <- Heqt2o in H. cbn in H. *)
    (*       dependent destruction H. *)
    (*       destruct e' as [e | oome]; cbn in KS; cbn in HTA; red in HTA. *)
    (*       * rewrite KS. *)
    (*         rewrite HTA. *)

    (*         assert (ta ≈ vis e (fun x => ret x)) as TAvis. *)
    (*         { rewrite HTA. *)
    (*           reflexivity. *)
    (*         } *)

    (*       eapply ReturnsVis with (a := v) in TAvis. *)
    (*       2: { *)
    (*         econstructor. *)
    (*         cbn. *)
    (*         reflexivity. *)
    (*       } *)

    (*       rewrite bind_trigger. *)
    (*       eapply CrawlVis1 with (e := (resum IFun T e)) (k := k2). *)
    (*       reflexivity. *)
    (*       eapply IHUB. *)
    (*       unfold refine_OOM_h. *)
    (*       pclearbot. *)
    (*       rewrite <- REL. *)

    (*       specialize (HK v TAvis). *)
    (*       pclearbot. *)
    (*       unfold interp_prop. *)
    (*       apply HK. *)
    (*     + (* t2 has OOM *) *)
    (*       clear KS. *)
    (*       clear HTA. *)
    (*       inversion oome; subst. *)
    (*       contradiction. *)
    (*   - rename Y into T. *)
    (*     rename x into v. *)
    (*     intros x EQ. *)
    (*     revert e k H UB IHUB. *)
    (*     punfold EQ; red in EQ. *)
    (*     genobs t2 t2o. *)
    (*     revert t2 Heqt2o. *)
    (*     induction EQ; rename t2 into x; intros t2 Heqt2o e' k H UB IHUB. *)

    (*     punfold H; red in H. *)
    (*     rewrite <- Heqt2o in H. *)
    (*     inversion H. *)

    (*     punfold H; red in H. *)
    (*     rewrite <- Heqt2o in H. *)
    (*     inversion H; inversion CHECK. *)

    (*     punfold H; red in H. *)
    (*     rewrite <- Heqt2o in H. *)
    (*     dependent induction H. *)

    (*     cbn in KS; *)
    (*       cbn in HTA; red in HTA; try rewrite HTA in KS. *)
    (*     + rewrite KS. *)

    (*       assert (ta ≈ vis e' (fun x => ret x)) as TAvis. *)
    (*       { rewrite HTA. *)
    (*         reflexivity. *)
    (*       } *)

    (*       eapply ReturnsVis with (a := v) in TAvis. *)
    (*       2: { *)
    (*         econstructor. *)
    (*         cbn. *)
    (*         reflexivity. *)
    (*       } *)

    (*       rewrite bind_trigger. *)
    (*       eapply CrawlVis2 with (e := (resum IFun T e')) (k := k2). *)
    (*       reflexivity. *)
    (*       eapply IHUB. *)
    (*       unfold refine_OOM_h. *)
    (*       pclearbot. *)
    (*       rewrite <- REL. *)

    (*       specialize (HK v TAvis). *)
    (*       pclearbot. *)
    (*       unfold interp_prop. *)
    (*       apply HK. *)
    (*   - intros y EQ. *)
    (*     punfold H; red in H. *)
    (*     dependent induction H. *)
    (*     punfold EQ; red in EQ. *)
    (*     genobs t2 ot2. *)
    (*     clear t2 Heqot2. *)

    (*     induction EQ; try inv x. *)

    (*     dependent destruction H1. *)
    (*     cbn in KS. *)
    (*     cbn in HTA; red in HTA. *)
    (*     subst ta. *)

    (*     rewrite KS. *)
    (*     rewrite bind_trigger. *)
    (*     eapply FindUB with (s := s) (k:=k2). *)
    (*     reflexivity. *)
    (* } *)
  Admitted.

  Lemma contains_UB_refine_OOM_h :
    forall R (RR : relation R) (x y : itree Eff R),
      contains_UB y ->
      refine_OOM_h RR x y ->
      contains_UB x.
  Proof using Type.
    intros R RR x y UB REF.
    rewrite REF.
    eauto.
  Qed.
End refine_OOM_h_lemmas.
