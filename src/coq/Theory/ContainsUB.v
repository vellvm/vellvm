Require Import String.
Definition blah := 2.
From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.Lang
     Handlers.OOM.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.

From Coq Require Import Relations RelationClasses.

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
  | FindUB    : forall s k t2, t2 ≅ (vis (subevent _ (ThrowUB s)) k) -> contains_UB t2.

  #[global] Instance proper_eutt_contains_UB {R} {RR : relation R} : Proper (@eqit Eff _ _ RR true true ==> iff) contains_UB.
  Proof.
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

            eapply CrawlVis1 with (k0:=k2) (e:=subevent T e').
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
            rewrite <- REL0.
            eauto.
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

            eapply CrawlVis2 with (k0:=k2).
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
            rewrite <- REL0.
            eauto.
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
        rewrite <- x in EQ.
        dependent induction EQ.
        + eapply FindUB.
          pfold; red.
          rewrite <- x.
          cbn.
          econstructor; intros [].
        + eapply CrawlTau with (t1:=t0).
          pfold; red; rewrite <- x; cbn.
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

            eapply CrawlVis1 with (k0:=k1) (e:=subevent T e').
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
            rewrite <- REL0.
            eauto.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t2 := t1).

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

            eapply CrawlVis2 with (k0:=k1).
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
            rewrite <- REL0.
            eauto.
          - punfold H; red in H.
            cbn in H.
            dependent induction H.
            eapply CrawlTau with (t2 := t1).

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
        rewrite <- x in EQ.
        dependent induction EQ.
        + eapply FindUB.
          pfold; red.
          rewrite <- x.
          cbn.
          econstructor; intros [].
        + eapply CrawlTau with (t3:=t1).
          pfold; red; rewrite <- x; cbn.
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
  Proof.
    intros t rv EQ CUB.
    rewrite EQ in CUB.
    inversion CUB; subst;
      pinversion H; inversion CHECK.
  Qed.

End contains_UB_lemmas.

Section refine_OOM_h_lemmas.
  Context {E G : Type -> Type}.
  Local Notation Eff := (E +' OOME +' UBE +' G).

  (* Only the <- direction is true *)
  Global Instance proper_refine_OOM_h
           {R} {RR : relation R} : Proper (@refine_OOM_h E (UBE +' G) _ RR ==> flip impl) contains_UB.
  Proof.
    unfold Proper, respectful.
    intros x y REF UB.
    
    { generalize dependent RR.
      generalize dependent x.
      generalize dependent y.
      pcofix CIH.
      intros y UB x RR REF.

      pinversion REF; subst;
        inv_contains_UB;
        inv_observes;
        inv_existT;
        pclearbot.

      all: admit.
  Admitted.

  Lemma contains_UB_refine_OOM_h :
    forall R (RR : relation R) (x y : itree Eff R),
      contains_UB y ->
      refine_OOM_h RR x y ->
      contains_UB x.
  Proof.
    intros R RR x y UB REF.
    rewrite REF.
    eauto.
  Qed.
End refine_OOM_h_lemmas.

(* TODO: move this *)
Lemma eqitree_inv_Tau_l {E R} (t t' : itree E R) :
  Tau t ≅ t' -> exists t0, observe t' = TauF t0 /\ t ≅ t0.
Proof.
  intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
Qed.

Section bind_lemmas.
  Context {E F G : Type -> Type}.
  Local Notation Eff := (E +' F +' UBE +' G).

  Lemma bind_contains_UB :
    forall {R T} (t : itree Eff R) (k : R -> itree Eff T),
      contains_UB t ->
      contains_UB (ITree.bind t k).
  Proof.
    intros R T t k CUB.
  Admitted.

  Lemma bind_contains_UB' :
    forall {R T} (t : itree Eff R) (k : R -> itree Eff T),
      contains_UB (ITree.bind t k) ->
      (forall x, ~ contains_UB (k x)) ->
      contains_UB t.
  Proof.

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

  Lemma interp_contains_UB :
    forall {R} (t : itree Eff1 R),
      contains_UB t ->
      handler_keeps_UB ->
      contains_UB (interp handler t).
  Proof.
    intros R t UB KEEP.

    unfold handler_keeps_UB in KEEP.

    rewrite (itree_eta t).
    genobs t to.
    revert t to Heqto UB.
    pcofix CIH; intros t to Heqto UB.

    pinversion UB; clear UB.
    - (* Tau *)
      admit.
    - (* Vis E + F *)
      admit.
    - (* Vis G *)
      admit.
    - (* UB *)
      rewrite <- H0 in Heqto.
      subst.
      pfold.

      unfold handler_keeps_UB in KEEP.
      pose proof (KEEP _ (ThrowUB s)).
      rewrite <- InterpFacts.interp_trigger in H.

      punfold H.
      cbn in H.
  Admitted.
End interp_lemmas.
