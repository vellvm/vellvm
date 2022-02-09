Require Import String.

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

Section contains_UB.
  Context {E F G : Type -> Type}.
  Local Notation Eff := (E +' F +' UBE +' G).

  Inductive contains_UB' {R} (CUB : itree Eff R -> Prop) : itree' Eff R -> Prop :=
  | CrawlTau  : forall t, CUB t -> contains_UB' CUB (TauF t)
  | CrawlVis1 : forall Y (e : (E +' F) Y) x (k : Y -> itree Eff R), CUB (k x) -> contains_UB' CUB (VisF (subevent _ e) k)
  | CrawlVis2 : forall Y (e : G Y) x (k : Y -> itree Eff R), CUB (k x) -> contains_UB' CUB (VisF (subevent _ e) k)
  | FindUB    : forall s k, contains_UB' CUB (VisF (subevent _ (ThrowUB s)) k).

  Definition contains_UB {R} : itree Eff R -> Prop
    := paco1 (fun CUB t => contains_UB' CUB (observe t)) bot1.

  Lemma contains_UB_mon {R} : monotone1 (fun (CUB : rel1 (itree Eff R)) (t : itree Eff R) => contains_UB' CUB (observe t)).
  Proof.
    unfold monotone1.
    intros x0 r r' IN LE.
    induction (observe x0).
    - inversion IN.
    - inversion IN; subst; constructor; eauto.
    - inversion IN;
        try apply inj_pair2 in H1;
        try apply inj_pair2 in H2;
        subst;
        try econstructor; eauto.

      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      subst.

      econstructor.
  Qed.
End contains_UB.

Hint Unfold contains_UB : Core.
Hint Resolve contains_UB_mon : paco.

Ltac inv_existT :=
  repeat match goal with
         | H: existT _ _ _ = existT _ _ _ |- _ =>
             apply inj_pair2 in H; inversion H; subst
         end.

Ltac inv_contains_UB :=
  match goal with
  | UB : contains_UB ?x,
      H : _ = observe ?x |- _ =>
      punfold UB; rewrite <- H in UB;
      inversion UB; subst
  | UB : contains_UB ?x
    |- _ =>
      punfold UB;
      inversion UB; subst
  end.

Ltac pfold_contains_UB :=
  match goal with
  | H : _ = observe ?y |- paco1 _ _ ?y =>
      pfold; rewrite <- H
  end.

Ltac inv_observes :=
  repeat
    match goal with
    | H1 : _ = observe ?x,
        H2 : _ = observe ?x |- _ =>
        setoid_rewrite <- H1 in H2; inversion H2; subst
    end.

Ltac subst_into_contains_UB :=
  match goal with
  | OBS : _ = observe ?x,
      CUB : contains_UB ?x |- _ =>
      punfold CUB; subst_into_contains_UB
  | OBS : _ = observe ?x,
      CUB : contains_UB' _ (observe ?x) |- _ =>
      setoid_rewrite <- OBS in CUB
  end.

Ltac inv_contains_UB' :=
  match goal with
  | CUB : contains_UB' _ _ |- _ =>
      inversion CUB; subst
  end.


Section contains_UB_lemmas.
  Context {E F G : Type -> Type}.
  Local Notation Eff := (E +' F +' UBE +' G).

  Lemma contains_UB_tau {R} (t : itree Eff R):
    contains_UB t <-> contains_UB (Tau t).
  Proof.
    split; intros UB.
    { pfold.
      punfold UB.
      constructor.
      left.
      pfold.
      apply UB.
    }

    { pfold.
      pinversion UB; subst.
      punfold H0.
    }
  Qed.

  Lemma ret_not_contains_UB {R} {RR : relation R} :
    forall (t : itree Eff R) rv a b, eqit RR a b t (ret rv) -> ~ contains_UB t.
  Proof.
    intros t rv a b EQ CUB.
    punfold EQ.
    unfold eqit_ in EQ.
    punfold CUB.
    remember (observe t) as to.
    remember (observe (ret rv)) as ro.
    revert t Heqto Heqro.
    induction EQ; intros t TO RO; inversion TO; inversion RO; subst.
    - inversion CUB.
    - eapply IHEQ.
      + inversion CUB; subst; pclearbot.
        punfold H2.
      + reflexivity.
      + reflexivity.
  Qed.

  Instance proper_eqit_contains_UB {R} {RR : relation R} (a b : bool) : Proper (@eqit Eff _ _ RR a b ==> iff) contains_UB.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    split.
    { generalize dependent RR.
      generalize dependent y.
      generalize dependent x.
      pcofix CIH.
      intros x y RR EQ UB.

      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        pclearbot;
        try solve [
            pfold_contains_UB;
            econstructor; right; eauto
          ]; inversion CHECK; subst.

      - (* Left tau, nothing about y *)
        clear UB.
        punfold H1.

        genobs y yo.
        genobs t1 t1o.

        (* revert H0. *)
        clear H0.
        revert t1 Heqt1o Heqyo.
        pfold.

        induction REL; intros t1' Heqt1o Heqyo; pose proof True as H0; inversion Heqt1o; inversion Heqyo; subst.
        + inversion H1.
        + inversion H1; subst; pclearbot.
          constructor.
          right.
          rewrite H2 in H1.
          eapply CIH.
          2: pfold; apply H1.

          punfold REL.
          red in REL.
          pfold.
          red.
          rewrite <- H2.
          constructor.
          constructor.
          eauto.
        + inversion H1; subst; inv_existT; subst; pclearbot;
            econstructor; right; eauto.
        + inversion H1; subst; pclearbot.
          punfold H4.
        + constructor.
          right.
          eapply CIH; eauto.
          pfold.
          auto.
      - (* Left and right tau *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Right tau, external call on the left *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Right tau, debug or failure event on the left *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* UB *)
        pfold.
        rewrite <- H1.
        constructor.
        right.
        eapply CIH.
        pfold.
        red.
        apply REL.
        pfold.
        auto.
    }

    { generalize dependent RR.
      generalize dependent x.
      generalize dependent y.
      pcofix CIH.
      intros y x RR EQ UB.

      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        pclearbot;
        try solve [
            pfold_contains_UB;
            econstructor; right; eauto
          ]; inversion CHECK; subst.

      - (* Left and right tau *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, external call on the right *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, debug or failure on the right *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* UB *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, nothing about x on the right. *)
        clear UB.
        punfold H0.

        genobs x xo.
        genobs t2 t2o.

        (* revert H0. *)
        clear H1.
        revert t2 Heqt2o Heqxo.
        pfold.

        induction REL; intros t2' Heqt2o Heqxo; pose proof True as H1; inversion Heqt2o; inversion Heqxo; subst.
        + inversion H0.
        + inversion H0; subst; pclearbot.
          constructor.
          right.
          rewrite H2 in H0.
          eapply CIH.
          2: pfold; apply H0.

          punfold REL.
          red in REL.
          pfold.
          red.
          rewrite <- H2.
          constructor.
          constructor.
          eauto.
        + inversion H0; subst; inv_existT; subst; pclearbot;
            econstructor; right; eauto.
        + constructor.
          right.
          eapply CIH; eauto.
          pfold.
          auto.
        + inversion H0; subst; pclearbot.
          punfold H4.
    }
  Qed.

  Hint Resolve interp_PropT__mono : paco.

  Lemma contains_UB_eutt :
    forall R (RR : relation R) (t1 t2 : itree Eff R),
      contains_UB t1 ->
      eutt RR t2 t1 ->
      contains_UB t2.
  Proof.
    intros R RR t1 t2 UB EQ.
    rewrite EQ.
    eauto.
  Qed.

End contains_UB_lemmas.

Section refine_OOM_h_lemmas.
  Context {E G : Type -> Type}.
  Local Notation Eff := (E +' OOME +' UBE +' G).

  (* Only the <- direction is true *)
  Instance proper_refine_OOM_h
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
