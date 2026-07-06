(** * Relation up to tau *)

(** [rutt] ("relation up to tau") is a generalization of [eutt] that may relate trees
  indexed by different event type families [E]. *)

(** It corresponds roughly to the interpretation of "types as relations" from the relational
  parametricity model by Reynolds (Types, Abstraction and Parametric Polymorphism).
  Any polymorphic function [f : forall E R, itree E R -> ...] should respect this relation,
  in the sense that for any relations [rE], [rR], the implication
  [rutt rE rR t t' -> (f t ~~ f t')] should hold, where [~~] is some canonical relation on the
  codomain of [f].

  If we could actually quotient itrees "up to taus", and Coq could generate
  parametricity ("free") theorems on demand, the above might be a free theorem. *)

(** [rutt] is used to define the [trace_refine] relation in [ITree.ITrace.ITraceDefinition]. *)

From Vellvm Require Import Tactics.
From Stdlib Require Import
  Program
.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     Eq
     Basics
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section RuttF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  (* From the point of view of relational parametricity, it would be more fitting
  to replace [(REv, RAns)] with one [REv : forall A1 A2, (A1 -> A2 -> Prop) -> (E1 A1 -> E2 A2 -> Prop)].
  Contributions to that effect are welcome. *)
  Context (Rcutl : forall (A : Type), E1 A -> Prop ).
  Context (Rcutr : forall (B : Type), E2 B -> Prop ).
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
  Context (RR : R1 -> R2 -> Prop).
  Arguments Rcutl {A}.
  Arguments Rcutr {B}.
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive ruttF (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttF sim (VisF e1 k1) (VisF e2 k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttF sim (observe t1) ot2 ->
      ruttF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttF sim ot1 (observe t2) ->
      ruttF sim ot1 (TauF t2)
  | EqCutL : forall (A : Type) (e : E1 A) k t,
      Rcutl e ->
      ruttF sim (VisF e k) t
  | EqCutR : forall (B : Type) (e : E2 B) k t,
      Rcutr e ->
      ruttF sim t (VisF e k).
  Hint Constructors ruttF : itree.

  Definition rutt_ (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    ruttF sim (observe t1) (observe t2).
  Hint Unfold rutt_ : itree.

  Lemma rutt_monot : monotone2 rutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition rutt : itree E1 R1 -> itree E2 R2 -> Prop := paco2 rutt_ bot2.
  Hint Unfold rutt : itree.

End RuttF.
Hint Resolve rutt_monot : paco.
Hint Constructors ruttF : itree.

Lemma rutt_inv_Tau_l :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  rutt Rcutl Rcutr REv RAns RR (Tau t1) t2 ->
  rutt Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros * EQ.
  punfold EQ; red in EQ; cbn in EQ.
  dependent induction EQ; pclearbot; eauto.
  - pfold; punfold H; red in H |-*.
    rewrite <- x. constructor. apply H.
  - pfold; apply EQ.
  - pfold; red; rewrite <- x.
    constructor.
    specialize (IHEQ t1 t0).
    forward IHEQ. reflexivity.
    specialize (IHEQ eq_refl eq_refl).
    punfold IHEQ.
  - pfold; red; rewrite <- x.
    now constructor.
Qed.

Lemma rutt_inv_Tau_r :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  rutt Rcutl Rcutr REv RAns RR t1 (Tau t2) ->
  rutt Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros * EQ.
  punfold EQ; red in EQ; cbn in EQ.
  dependent induction EQ; pclearbot; eauto.
  - pfold; punfold H; red in H |-*.
    rewrite <- x. constructor. apply H.
  - pfold; red; rewrite <- x.
    constructor.
    specialize (IHEQ t0 t2).
    forward IHEQ. reflexivity.
    specialize (IHEQ eq_refl eq_refl).
    punfold IHEQ.
  - pfold; apply EQ.
  - pfold; red; rewrite <- x.
    now constructor.
Qed.

Lemma rutt_inv_Tau :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  rutt Rcutl Rcutr REv RAns RR (Tau t1) (Tau t2) ->
  rutt Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros.
  now apply rutt_inv_Tau_l, rutt_inv_Tau_r.
Qed.  

Lemma rutt_eutt_l {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INL: eutt eq t1 t2)
      (INR: @rutt E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t2 t3):
  rutt Rcutl Rcutr REv RAns RR t1 t3.
Proof.
  revert_until RR. pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t1 ot1.
  hinduction INR before CIH; intros; subst; clear t2 t3; eauto with itree.
  - remember (RetF r1) as ot.
    hinduction INL before CIH; intros; inv Heqot; eauto with paco itree.
  - (* t2 = τ m1 , t3 = τ m2 *)
    pclearbot.
    assert (DEC: (exists m1, ot1 = TauF m1) \/ (forall m1, ot1 <> TauF m1)).
    { destruct ot1; eauto; right; red; intros ? abs; inv abs. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply eqit_inv_Tau. pfold; apply INL.
    + (* t1 <> τ ..*)
      inv INL; try (exfalso; eapply EQ; eauto; fail).
      econstructor.
      punfold H; red in H.
      hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * clear EQ CHECK.
        subst.
        induction H; pclearbot; eauto with itree.
        constructor; left; eapply paco2_mon; eauto; intuition.
        constructor; auto.
        intros; left; eapply paco2_mon; eauto; intuition.
      * clear EQ CHECK.
        unfold id in REL; pclearbot.
        remember (VisF e k2) as ot.
        hinduction H before CIH; intros; try discriminate; eauto with itree.
        ** inv_Vis.
           constructor; auto.
           pclearbot. 
           intros.
           right; eapply CIH.
           apply REL.
           apply H0; eauto.
        ** inv_Vis.
           eapply EqCutL; auto.
      * clear CHECK0.
        apply IHREL; auto.
        pose proof rutt_inv_Tau_l (RR := RR) Rcutr Rcutl REv RAns t2 m2.
        forward H0.
        now pfold.
        punfold H0.
  - pclearbot.
    dependent induction INL; eauto with itree.
    red in REL; pclearbot.
    constructor; auto.
    intros; right.
    eapply CIH. apply REL.
    now apply H0.
  - apply IHINR.
    assert (eutt eq (go ot1) (Tau t1)) by (pfold; apply INL).
    rewrite tau_eutt in H.
    punfold H.
  - dependent induction INL; eauto with itree.
Qed.

Lemma rutt_eutt_r {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INR: eutt eq t2 t3)
      (INL: @rutt E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t1 t2):
  rutt Rcutl Rcutr REv RAns RR t1 t3.
Proof.
  revert_until RR. pcofix CIH. intros.
  pstep. punfold INL. punfold INR. red in INL, INR |- *. genobs_clear t3 ot3.
  hinduction INL before CIH; intros; subst; clear t1 t2; eauto with itree.
  - remember (RetF r2) as ot.
    hinduction INR before CIH; intros; inv Heqot; eauto with paco itree.
  - (* t1 = τ m1 , t2 = τ m2 *)
    pclearbot.
    assert (DEC: (exists m3, ot3 = TauF m3) \/ (forall m3, ot3 <> TauF m3)).
    { destruct ot3; eauto; right; red; intros ? abs; inv abs. }
    destruct DEC as [EQ | EQ].
    + destruct EQ as [m3 ?]; subst.
      econstructor. right. pclearbot. eapply CIH; eauto with paco.
      eapply eqit_inv_Tau. pfold; apply INR.
    + (* t3 <> τ ..*)
      inv INR; try (exfalso; eapply EQ; eauto; fail).
      econstructor.
      punfold H; red in H.
      hinduction REL before CIH; intros; try (exfalso; eapply EQ; eauto; fail).
      * clear EQ CHECK.
        subst.
        induction H; pclearbot; eauto with itree.
        constructor; left; eapply paco2_mon; eauto; intuition.
        constructor; auto.
        intros; left; eapply paco2_mon; eauto; intuition.
      * clear EQ CHECK.
        unfold id in REL; pclearbot.
        remember (VisF e k1) as ot.
        hinduction H before CIH; intros; try discriminate; eauto with itree.
        ** inv_Vis.
           constructor; auto.
           pclearbot. 
           intros.
           right; eapply CIH.
           apply REL.
           apply H0; eauto.
        ** inv_Vis.
           eapply EqCutR; auto.
      * clear CHECK0.
        apply IHREL; auto.
        pose proof rutt_inv_Tau_r (RR := RR) Rcutr Rcutl REv RAns m1 t1.
        forward H0.
        now pfold.
        punfold H0.
  - pclearbot.
    dependent induction INR; eauto with itree.
    red in REL; pclearbot.
    constructor; auto.
    intros; right.
    eapply CIH. apply REL.
    now apply H0.
  - apply IHINL.
    assert (eutt eq (Tau t0) (go ot3)) by (pfold; apply INR).
    rewrite tau_eutt in H.
    punfold H.
  - dependent induction INR; eauto with itree.
Qed.

From Stdlib Require Import Setoid Morphisms.

Lemma rutt_eutt {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eutt eq ==> eutt eq ==> iff) (@rutt E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; split; intros EQ.
  eapply rutt_eutt_l, rutt_eutt_r; eauto; symmetry; eauto.
  eapply rutt_eutt_l, rutt_eutt_r; eauto; symmetry; eauto.
Qed.

  
