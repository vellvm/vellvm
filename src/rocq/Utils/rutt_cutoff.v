(** * Equivalence up to tau with relation on events and cutoffs *)

(** [rutt] generalizes [eutt] by taking as parameter
    a relation on the signatures of the related computations.
    [ruttc] further refines it by allowing to treat some
    events as valid cutoffs in the refinement: typically,
    relating Undefined Behavior in the source to any
    computation in the target.

    Things get quite verbose, but it's overall straightforwards.
 *)

From Coinduction Require Import all.

From Vellvm Require Import
  Tactics
  Utils.ITreeUtil
  Utils.ListUtil.

From Stdlib Require Import
  Program Setoid Morphisms List.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
  Basics.Utils
  Axioms
  ITree
  Eq
  Basics
  HeterogeneousRelations
  Rutt
  RuttFacts
  Recursion
  RecursionFacts
  TranslateFacts
  InterpFacts 
.


Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Definition pred1 (E : Type -> Type) := forall A, E A -> Prop.
Definition eqp1 {E}: relation (pred1 E) := fun R1 R2 => forall A (e : E A), R1 _ e <-> R2 _ e .
Variant sum_pred1 {E1 E2 : Type -> Type} (P1 : pred1 E1) (P2 : pred1 E2) : pred1 (E1 +' E2) :=
  | sum_pred1_inl {A} (e : E1 A) : P1 _ e -> sum_pred1 P1 P2 _ (inl1 e)
  | sum_pred1_inr {A} (e : E2 A) : P2 _ e -> sum_pred1 P1 P2 _ (inr1 e). 
Definition TT1 {E}: pred1 E := fun _ _ => True.
Definition FF1 {E}: pred1 E := fun _ _ => False.
Definition FF4 {E F} : prerel E F := fun _ _ _ _ => False.
Definition TT4 {E F} : prerel E F := fun _ _ _ _ => True.
Definition TT6 {E F} : postrel E F := fun _ _  _ _ _ _ => True.
Definition FF6 {E F} : postrel E F := fun _ _  _ _ _ _ => False.

#[global] Instance eq_REv_sum_prerel {E1 E2 D1 D2}:
  Proper (eq_REv ==> eq_REv ==> eq_REv) (@sum_prerel E1 E2 D1 D2).
Proof.
  cbv; intuition.
  dependent induction H1; constructor; [apply H | apply H0]; auto.
  dependent induction H1; constructor; [apply H | apply H0]; auto.
Qed.
       
Variant inl_prerel {E1 E2 D1 D2 : Type -> Type}
  (PR : prerel (E1 +' E2) (D1 +' D2)) : prerel E1 D1 :=
  | Inl_prerel A B (e1 : E1 A) (e2 : D1 B) :
    PR _ _ (inl1 e1) (inl1 e2) -> inl_prerel PR _ _ e1 e2.

Variant inr_prerel {E1 E2 D1 D2 : Type -> Type}
  (PR : prerel (E1 +' E2) (D1 +' D2)) : prerel E2 D2 :=
  | Inr_prerel A B (e1 : E2 A) (e2 : D2 B) :
    PR _ _ (inr1 e1) (inr1 e2) -> inr_prerel PR _ _ e1 e2.

Lemma eq_REv_sum_rel_inl {E F G H} (RA : prerel E F) (RB : prerel G H) :
  eq_REv (inl_prerel (sum_prerel RA RB)) RA.
Proof.
  cbv; intuition.
  dependent induction H0; dependent induction H0; auto.
  now do 2 constructor.
Qed.
 
Lemma eq_REv_sum_rel_inr {E F G H} (RA : prerel E F) (RB : prerel G H) :
  eq_REv (inr_prerel (sum_prerel RA RB)) RB.
Proof.
  cbv; intuition.
  dependent induction H0; dependent induction H0; auto.
  now do 2 constructor.
Qed.

Variant inl_postrel {E1 E2 D1 D2 : Type -> Type}
  (PR : postrel (E1 +' E2) (D1 +' D2)) : postrel E1 D1 :=
  | Inl_postrel A B (e1 : E1 A) a (e2 : D1 B) b :
    PR _ _ (inl1 e1) a (inl1 e2) b -> inl_postrel PR _ _ e1 a e2 b.
       
Variant inr_postrel {E1 E2 D1 D2 : Type -> Type}
  (PR : postrel (E1 +' E2) (D1 +' D2)) : postrel E2 D2 :=
  | Inr_postrel A B (e1 : E2 A) a (e2 : D2 B) b :
    PR _ _ (inr1 e1) a (inr1 e2) b -> inr_postrel PR _ _ e1 a e2 b.

Lemma eq_RAns_sum_rel_inr {E F G H} (RA : postrel E F) (RB : postrel G H) :
  eq_RAns (inr_postrel (sum_postrel RA RB)) RB.
Proof.
  intros A B; split; intros [e1 a] [e2 b] HR; cbn in *.
  - dependent induction HR.
    match goal with
    | HS : sum_postrel _ _ _ _ _ _ _ _ |- _ => dependent induction HS
    end; auto.
  - now do 2 constructor.
Qed.

Section RuttcF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  (* Cutoff on the left *)
  Context (Rcutl : pred1 E1).
  (* Cutoff on the right *)
  Context (Rcutr : pred1 E2).
  Context (REv : prerel E1 E2).
  Context (RAns : postrel E1 E2).
  Context (RR : R1 -> R2 -> Prop).
  Arguments Rcutl {A}.
  Arguments Rcutr {A}.
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive ruttcF (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttcF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttcF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttcF sim (VisF e1 k1) (VisF e2 k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttcF sim (observe t1) ot2 ->
      ruttcF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttcF sim ot1 (observe t2) ->
      ruttcF sim ot1 (TauF t2)
  (* New constructors *)
  | EqCutL : forall (A : Type) (e : E1 A) k t,
      Rcutl e ->
      ruttcF sim (VisF e k) t
  | EqCutR : forall (B : Type) (e : E2 B) k t,
      Rcutr e ->
      ruttcF sim t (VisF e k).
  Hint Constructors ruttcF : itree.

  Definition ruttc_ (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    ruttcF sim (observe t1) (observe t2).
  Hint Unfold ruttc_ : itree.

  Lemma ruttc_mono : Proper (leq ==> leq) ruttc_.
  Proof.
    intros sim sim' LE t1 t2 H. red in H |- *.
    induction H; eauto with itree.
    - constructor. now apply LE.
    - constructor; auto. intros; now apply LE, H0.
  Qed.

  Definition ruttc_mon : mon (itree E1 R1 -> itree E2 R2 -> Prop) :=
    {| body := ruttc_ ; Hbody := ruttc_mono |}.

  Definition ruttc : itree E1 R1 -> itree E2 R2 -> Prop := gfp ruttc_mon.

End RuttcF.
#[global] Hint Constructors ruttcF : itree.
#[global] Hint Unfold ruttc_ : itree.

(** ** [ruttc]-specific tactics, following [rutt]'s ([rcbn], [rstep]). *)

(* Expose the [ruttcF] functor in a goal [ruttc_mon x t1 t2]. *)
Ltac rccbn := cbn [ruttc_mon body]; try unfold ruttc_.
Ltac rccbn_in H := cbn [ruttc_mon body] in H; try unfold ruttc_ in H.
Tactic Notation "rccbn" "in" ident(h) := rccbn_in h.

(* Unfold [ruttc] by one step, in the goal or in a hypothesis. *)
Tactic Notation "rcstep" := unfold ruttc; step; rccbn.
Tactic Notation "rcstep" "in" ident(h) := unfold ruttc in h; step in h; rccbn in h.

(* Refold the [ruttcF] functor of a goal back into [ruttc_mon x t1 t2]. *)
Lemma ruttc_to_mon_obs {E1 E2 R1 R2} Rcutl Rcutr REv RAns (RR : R1 -> R2 -> Prop) x t1 t2 :
  @ruttcF E1 E2 R1 R2 Rcutl Rcutr REv RAns RR x (observe t1) (observe t2)
  = @ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR x t1 t2.
Proof. reflexivity. Qed.

Lemma ruttc_to_mon_go {E1 E2 R1 R2} Rcutl Rcutr REv RAns (RR : R1 -> R2 -> Prop) x o1 o2 :
  @ruttcF E1 E2 R1 R2 Rcutl Rcutr REv RAns RR x o1 o2
  = @ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR x (go o1) (go o2).
Proof. reflexivity. Qed.

#[global] Hint Rewrite @ruttc_to_mon_obs : to_mon_obs.
#[global] Hint Rewrite @ruttc_to_mon_go  : to_mon_go.

(** ** Up-to principles *)

(* Validity of the up-to [euttge] principle, on every element of the chain. *)
#[global] Instance euttge_proper_ruttcChain {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR}
  (c : Chain (@ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR)) :
  Proper (euttge eq ==> euttge eq ==> flip impl) (elem c).
Proof.
  unfold Proper, respectful, flip, impl.
  tower induction.
  intros IH x x' EQx y y' EQy; step in EQx; step in EQy.
  rccbn; intros EQ.
  genobs x' ox'; genobs y' oy'.
  revert x x' y y' Heqox' Heqoy' EQx EQy.
  induction EQ; intros.

  (* EqRet *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. genret r1 or1. revert x Heqox.
    hinduction EQx before ox; try discriminate.
    + intros; subst; inv Heqor1. clear x Heqox.
      genobs y oy. genret r2 or2. revert y Heqoy.
      hinduction EQy before oy; try discriminate.
      * subst; intros [=<-] ? ?. constructor. auto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqTau *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. gentau m1 om1. revert x Heqox.
    hinduction EQx before ox; try discriminate.
    + intros [=<-] ? ?.
      genobs y oy. gentau m2 om2. revert y Heqoy.
      hinduction EQy before oy; try discriminate.
      * intros [=<-] ? ?. constructor. eapply IH; eauto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqVis *)
  - clear x' y' Heqox' Heqoy'.
    genobs x ox. genvis e1 k1 ot1. revert x Heqox.
    hinduction EQx before ox; try discriminate.
    + intros. apply eq_inv_VisF_weak in Heqot1 as (-> & ? & ?); cbn in *; subst.
      clear x Heqox.
      genobs y oy. genvis e2 k2 ot2. revert y Heqoy.
      hinduction EQy before oy; try discriminate.
      * intros. apply eq_inv_VisF_weak in Heqot2 as (-> & ? & ?); cbn in *; subst.
        constructor; auto. intros. eapply IH. apply (REL a). apply (REL0 b). apply H0; auto.
      * intros. apply EqTauR; auto. eapply IHEQy; eauto.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqTauL *)
  - edestruct euttge_tau_r_inv; [step; eauto |].
    simpobs.
    apply EqTauL; auto.
    eapply IHEQ; eauto.
    assert (euttge eq (Tau x0) (Tau t1)) by (now step).
    unstep; eapply euttge_tau_inv; eauto.

  (* EqTauR *)
  - edestruct euttge_tau_r_inv; [step; eauto |].
    simpobs.
    apply EqTauR; auto.
    eapply IHEQ; eauto.
    assert (euttge eq (Tau x0) (Tau t2)) by (now step).
    unstep; eapply euttge_tau_inv; eauto.

  (* EqCutL *)
  - clear Heqoy'.
    genobs x ox. genvis e k ot. revert x Heqox.
    hinduction EQx before ox; try discriminate.
    + intros. apply eq_inv_VisF_weak in Heqot as (-> & ? & ?); cbn in *; subst.
      now apply EqCutL.
    + intros; subst. apply EqTauL; auto. eapply IHEQx; eauto.

  (* EqCutR *)
  - clear Heqox'.
    genobs y oy. genvis e k ot. revert y Heqoy.
    hinduction EQy before oy; try discriminate.
    + intros. apply eq_inv_VisF_weak in Heqot as (-> & ? & ?); cbn in *; subst.
      now apply EqCutR.
    + intros; subst. apply EqTauR; auto. eapply IHEQy; eauto.
Qed.

(* Same, stated on [b (elem c)]: the guarded level reached by [coinduction]. *)
#[global] Instance euttge_proper_ruttcChain_mon {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR}
  (c : Chain (@ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR)) :
  Proper (euttge eq ==> euttge eq ==> flip impl) (ruttc_mon Rcutl Rcutr REv RAns RR (elem c)).
Proof.
  exact (euttge_proper_ruttcChain (chain_b c)).
Qed.

#[global] Instance euttge_proper_ruttc {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR} :
  Proper (euttge eq ==> euttge eq ==> flip impl) (@ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR).
Proof.
  exact (euttge_proper_ruttcChain (chain_gfp _)).
Qed.

(* The usual up-to bind, on every element of the chain: the prefixes are
   related by [ruttc] itself, the continuations by the chain element. *)
Lemma ruttc_bind_chain {E1 E2 R1 R2} Rcutl Rcutr REv RAns (RR : R1 -> R2 -> Prop)
  (c : Chain (@ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR)) :
  forall U1 U2 (UU : U1 -> U2 -> Prop) (t1 : itree E1 U1) (t2 : itree E2 U2) k1 k2,
    ruttc Rcutl Rcutr REv RAns UU t1 t2 ->
    (forall u1 u2, UU u1 u2 -> elem c (k1 u1) (k2 u2)) ->
    elem c (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  tower induction.
  intros IH U1 U2 UU t1 t2 k1 k2 EQ EQK.
  rcstep in EQ. rccbn.
  genobs t1 ot1. genobs t2 ot2.
  hinduction EQ before IH; intros.
  - rewrite 2 observe_bind; simpobs. apply EQK; auto.
  - rewrite 2 observe_bind; simpobs.
    constructor. eapply IH; eauto.
    intros; step; now apply EQK.
  - rewrite 2 observe_bind; simpobs.
    constructor; auto. intros.
    eapply IH; [now apply H0 |].
    intros; step; now apply EQK.
  - rewrite observe_bind; simpobs.
    apply EqTauL. eapply IHEQ; eauto.
  - setoid_rewrite observe_bind at 2; simpobs.
    apply EqTauR. eapply IHEQ; eauto.
  - rewrite observe_bind; simpobs. now apply EqCutL.
  - setoid_rewrite observe_bind at 2; simpobs. now apply EqCutR.
Qed.

(* [ruttc_bind_chain] at the guarded level [b (elem c)], where [coinduction]
   leaves the goal: the continuations are then also related at that level. *)
Lemma ruttc_bind_bchain {E1 E2 R1 R2} Rcutl Rcutr REv RAns (RR : R1 -> R2 -> Prop)
  (c : Chain (@ruttc_mon E1 E2 R1 R2 Rcutl Rcutr REv RAns RR)) :
  forall U1 U2 (UU : U1 -> U2 -> Prop) (t1 : itree E1 U1) (t2 : itree E2 U2) k1 k2,
    ruttc Rcutl Rcutr REv RAns UU t1 t2 ->
    (forall u1 u2, UU u1 u2 ->
              ruttc_mon Rcutl Rcutr REv RAns RR (elem c) (k1 u1) (k2 u2)) ->
    ruttc_mon Rcutl Rcutr REv RAns RR (elem c) (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  exact (ruttc_bind_chain _ _ _ _ _ (chain_b c)).
Qed.

(* Refold [gfp ruttc_mon] into [ruttc], e.g. in the continuations of a
   constructor applied at the [gfp] level, so that [ruttc]'s instances apply. *)
Ltac fold_ruttc :=
  repeat match goal with
  | |- context[gfp (@ruttc_mon ?E1 ?E2 ?R1 ?R2 ?a ?b ?c ?d ?e)] =>
      fold (@ruttc E1 E2 R1 R2 a b c d e)
  end.

(* Progressive [Proper] instances for [rutt] and congruence with eutt. *)

#[global] Instance ruttc_Proper_R {E1 E2 R1 R2}:
  Proper (
      eqp1
      ==> eqp1
      ==> eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@ruttc E1 E2 R1 R2).
Proof.
  intros ?? EQcutl ?? EQcutr REv1 REv2 HREv  RAns1 RAns2 HRAns RR1 RR2 HRR t1 _ <- t2 _ <-.
  split; intros Hruttc.

  - revert t1 t2 Hruttc; coinduction c CIH; intros t1 t2 Hruttc.
    rcstep in Hruttc; rccbn.
    hinduction Hruttc before CIH; intros.
    + constructor; now apply HRR.
    + constructor; now apply CIH.
    + constructor; [now apply HREv |].
      intros a b HA; apply CIH, H0.
      now apply (eq_RAns_iff HRAns).
    + now apply EqTauL.
    + now apply EqTauR.
    + apply EqCutL; now apply EQcutl.
    + apply EqCutR; now apply EQcutr.

  - revert t1 t2 Hruttc; coinduction c CIH; intros t1 t2 Hruttc.
    rcstep in Hruttc; rccbn.
    hinduction Hruttc before CIH; intros.
    + constructor; now apply HRR.
    + constructor; now apply CIH.
    + constructor; [now apply HREv |].
      intros a b HA; apply CIH, H0.
      now apply (eq_RAns_iff HRAns).
    + now apply EqTauL.
    + now apply EqTauR.
    + apply EqCutL; now apply EQcutl.
    + apply EqCutR; now apply EQcutr.
Qed.

(* Implication counterpart of [ruttc_Proper_R]: the cuts, [REv] and the
   return relation may be weakened, [RAns] strengthened. *)
Lemma ruttc_weaken {E1 E2 R1 R2}
  (Rcutl Rcutl' : pred1 E1) (Rcutr Rcutr' : pred1 E2)
  (REv REv' : prerel E1 E2) (RAns RAns' : postrel E1 E2)
  (RR RR' : R1 -> R2 -> Prop)
  (HCutl : forall A (e : E1 A), Rcutl A e -> Rcutl' A e)
  (HCutr : forall B (e : E2 B), Rcutr B e -> Rcutr' B e)
  (HREv : forall A B (e1 : E1 A) (e2 : E2 B), REv A B e1 e2 -> REv' A B e1 e2)
  (HRAns : forall A B (e1 : E1 A) a (e2 : E2 B) b, RAns' A B e1 a e2 b -> RAns A B e1 a e2 b)
  (HRR : forall r1 r2, RR r1 r2 -> RR' r1 r2) :
  forall t1 t2,
    ruttc Rcutl Rcutr REv RAns RR t1 t2 ->
    ruttc Rcutl' Rcutr' REv' RAns' RR' t1 t2.
Proof.
  coinduction c CIH; intros t1 t2 Hruttc.
  rcstep in Hruttc; rccbn.
  hinduction Hruttc before CIH; intros.
  - constructor; auto.
  - constructor; now apply CIH.
  - constructor; auto.
    intros; apply CIH, H0, HRAns; auto.
  - now apply EqTauL.
  - now apply EqTauR.
  - apply EqCutL; auto.
  - apply EqCutR; auto.
Qed.

(* Cut-rule derived from the up-to *)
Lemma ruttc_bind {E1 E2 R1 R2 T1 T2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR: R1 -> R2 -> Prop) (RT: T1 -> T2 -> Prop) t1 t2 k1 k2:
  ruttc Rcutl Rcutr REv RAns RR t1 t2 ->
  (forall r1 r2,
      RR r1 r2 ->
      ruttc Rcutl Rcutr REv RAns RT (k1 r1) (k2 r2)) ->
  ruttc Rcutl Rcutr REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. unfold ruttc.
  eapply (ruttc_bind_chain _ _ _ _ _ (chain_gfp _)); eauto.
Qed.

(* Proof rules *)
(* ret *)
Lemma ruttc_ret {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (v1 : R1) (v2 : R2):
  RR v1 v2 ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (Ret v1) (Ret v2).
Proof.
  intros; rcstep; constructor; auto.
Qed.

(* trigger *)
Lemma ruttc_trigger {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (e1 : E1 R1) (e2 : E2 R2):
  REv R1 R2 e1 e2 ->
  (forall a b, RAns R1 R2 e1 a e2 b -> RR a b) ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (ITree.trigger e1) (ITree.trigger e2).
Proof.
  intros; rcstep; constructor; auto.
  intros; now apply ruttc_ret, H0.
Qed.

(* trigger_cast *)
Lemma ruttc_trigger_cast {E1 E2 : Type -> Type} {Rcutr Rcutl} {REv : prerel E1 E2} {RAns A1 A2 RR} (e1 : E1 void) (e2 : E2 void):
  REv void void e1 e2 ->
  @ruttc E1 E2 A1 A2 Rcutr Rcutl REv RAns RR
    (trigger_cast' e1) (trigger_cast' e2).
Proof.
  intros; rcstep; cbn.
  constructor; auto; intros [].
Qed.

(* map_monad *)
Lemma ruttc_map_monad_gen {E1 E2 R1 R2 A1 A2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR: R1 -> R2 -> Prop)
  (f1 : A1 -> itree E1 R1) (f2 : A2 -> itree E2 R2) (l1 : list A1) (l2 : list A2)
  (HI : Forall2 (fun a1 a2 => ruttc Rcutl Rcutr REv RAns RR (f1 a1) (f2 a2)) l1 l2) :
  ruttc Rcutl Rcutr REv RAns (Forall2 RR)
    (map_monad f1 l1)
    (map_monad f2 l2).
Proof.
  induction HI; cbn.
  - now apply ruttc_ret.
  - eapply ruttc_bind; [apply H; now left |].
    intros r1 r2 HR.
    eapply ruttc_bind; [apply IHHI; intros; apply HIN; now right|].
    intros bs1 bs2 HBS.
    apply ruttc_ret.
    now constructor.
Qed.

Lemma ruttc_map_monad {E1 E2 R1 R2 A}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR: R1 -> R2 -> Prop)
  (f1 : A -> itree E1 R1) (f2 : A -> itree E2 R2) l
  (HI : forall a, In a l -> ruttc Rcutl Rcutr REv RAns RR (f1 a) (f2 a)) :
  ruttc Rcutl Rcutr REv RAns (Forall2 RR)
    (map_monad f1 l)
    (map_monad f2 l).
Proof.
  apply ruttc_map_monad_gen.
  apply Forall2_diag, Forall_forall; auto.
Qed.

(* iter *)
Lemma ruttc_iter {E1 E2 I1 I2 R1 R2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RR: R1 -> R2 -> Prop)
  (II: I1 -> I2 -> Prop)
  (f1 : I1 -> itree E1 (I1 + R1))
  (f2 : I2 -> itree E2 (I2 + R2))
  (Hind: forall i1 i2, II i1 i2 ->
                  ruttc Rcutl Rcutr REv RAns
                    (sum_rel II RR) (f1 i1) (f2 i2))
  i1 i2 :
  II i1 i2 ->
  ruttc Rcutl Rcutr REv RAns RR
    (ITree.iter f1 i1)
    (ITree.iter f2 i2).
Proof.
  revert i1 i2.
  coinduction c cih.
  intros * HI.
  rewrite 2 unfold_iter.
  eapply ruttc_bind_bchain.
  now apply Hind.
  clear i1 i2 HI; intros [|] [|] REL; inv REL.
  - constructor; now apply cih.
  - constructor; auto.
Qed.

(* mrec *)
Lemma ruttc_interp_mrec {D1 D2 E1 E2 R1 R2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RCall : prerel D1 D2)
  (RCall' : postrel D1 D2)
  (RAns: postrel E1 E2)
  (RR: R1 -> R2 -> Prop)
  (bodies1 : D1 ~> itree (D1 +' E1))
  (bodies2 : D2 ~> itree (D2 +' E2))

  (HInd : forall A B (d1 : D1 A) (d2 : D2 B), 
      RCall A B d1 d2 -> 
      ruttc (sum_pred1 FF1 Rcutl) (sum_pred1 FF1 Rcutr) (sum_prerel RCall REv) (sum_postrel RCall' RAns)
        (fun (a : A) (b : B) => RCall' A B d1 a d2 b)
        (bodies1 A d1) (bodies2 B d2))
  t1 t2 :
  ruttc (sum_pred1 FF1 Rcutl) (sum_pred1 FF1 Rcutr) (sum_prerel RCall REv) (sum_postrel RCall' RAns) RR t1 t2 ->
  ruttc Rcutl Rcutr REv RAns RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
Proof.
  revert t1 t2.
  coinduction c CIH.
  intros * EQ.
  rewrite 2 unfold_interp_mrec.
  rcstep in EQ.
  induction EQ; cbn -[lattice.body].
  - now constructor.
  - constructor; now apply CIH.
  - dependent induction H.
    + constructor.
      apply CIH.
      eapply ruttc_bind.
      now apply HInd.
      now intros; apply H0; constructor.
    + constructor; intros; auto.
      step; constructor.
      apply CIH, H0; constructor; auto.
  - rewrite tau_euttge.
    rewrite unfold_interp_mrec; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_interp_mrec; apply IHEQ.
  - dependent induction H.
    + destruct H.
    + constructor; auto.
  - dependent induction H.
    + destruct H.
    + constructor; auto.
Qed.

(* mrec *)
Lemma ruttc_mrec {D1 D2 E1 E2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (RCall : prerel D1 D2)
  (RCall' : postrel D1 D2)
  (bodies1 : D1 ~> itree (D1 +' E1))
  (bodies2 : D2 ~> itree (D2 +' E2))

  (HInd : forall A B (d1 : D1 A) (d2 : D2 B), 
      RCall A B d1 d2 -> 
      ruttc (sum_pred1 FF1 Rcutl) (sum_pred1 FF1 Rcutr) (sum_prerel RCall REv) (sum_postrel RCall' RAns)
        (fun (a : A) (b : B) => RCall' A B d1 a d2 b)
        (bodies1 A d1) (bodies2 B d2))
  {A B} (d1 : D1 A) (d2 : D2 B) :
  RCall A B d1 d2 ->
  ruttc Rcutl Rcutr REv RAns (fun (a : A) (b : B) => RCall' A B d1 a d2 b) (mrec bodies1 d1) (mrec bodies2 d2).
Proof.
  intros. eapply ruttc_interp_mrec; eauto.
Qed.

(* translate: characterizing the resulting relations generically
   in terms of h1/h2 and the original relations is a pain. I will
   do it if somebody need it, but in the mean time I'll restrict
   to the case I'm interested in.
 *)
Lemma ruttc_translate_inr {E1 E2 F1 F2 R1 R2}
  (Rcutl : pred1 E1)
  (Rcutr : pred1 E2)
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (REv' : prerel F1 F2)
  (RAns': postrel F1 F2)
  (RR: R1 -> R2 -> Prop)
  (t1 : itree E1 R1) (t2 : itree E2 R2) :
  ruttc Rcutl Rcutr REv RAns RR t1 t2 ->
  ruttc (sum_pred1 TT1 Rcutl) (sum_pred1 TT1 Rcutr)
    (sum_prerel REv' REv)
    (sum_postrel RAns' RAns)
    RR (translate (inr1 (E1 := F1)) t1) (translate (inr1 (E1 := F2)) t2).
Proof.
  revert t1 t2.
  coinduction c cih.
  intros * EQ.
  rcstep in EQ.
  rewrite 2 unfold_translate.
  induction EQ; cbn -[lattice.body].
  - now constructor.
  - constructor; now apply cih.
  - constructor; auto.
    constructor; auto.
    intros; eapply cih.
    dependent induction H1; apply H0; auto.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - do 2 constructor; eauto.
  - do 2 constructor; eauto.
Qed.

(* I give up, there's a nicer proof somewhere by relaxing
   [ruttc_Proper_R] to implication so that we can weaken
   REv/RAns over Fi to False, but reproving from scratch
   is easier.
 *)
Lemma ruttc_translate_inr' {E1 E2 F1 F2 R1 R2}
  (Rcutl : pred1 E1) 
  (Rcutr : pred1 E2) 
  (REv : prerel E1 E2)
  (RAns: postrel E1 E2)
  (Rcutl' : pred1 (F1 +' E1)) 
  (Rcutr' : pred1 (F2 +' E2)) 
  (REv' : prerel (F1 +' E1) (F2 +' E2))
  (RAns': postrel (F1 +' E1) (F2 +' E2))
  (RR: R1 -> R2 -> Prop)
  (HRcutl: eqp1 Rcutl' (sum_pred1 FF1 Rcutl))
  (HRcutr: eqp1 Rcutr' (sum_pred1 FF1 Rcutr))
  (HREv : eq_REv (inr_prerel REv') REv)
  (HRAns : eq_RAns (inr_postrel RAns') RAns)
  (t1 : itree E1 R1) (t2 : itree E2 R2) :
  ruttc Rcutl Rcutr REv RAns RR t1 t2 ->
  ruttc Rcutl' Rcutr' REv' RAns'
    RR (translate (inr1 (E1 := F1)) t1) (translate (inr1 (E1 := F2)) t2).
Proof.
  revert t1 t2.
  coinduction c cih.
  intros * EQ.
  rcstep in EQ.
  rewrite 2 unfold_translate.
  induction EQ; cbn -[lattice.body].
  - now constructor.
  - constructor; now apply cih.
  - constructor; auto.
    edestruct HREv as [_ HR].
    specialize (HR e1 e2 H).
    now dependent induction HR.
    intros; eapply cih.
    apply H0.
    edestruct HRAns as [HR _].
    specialize (HR (e1,a) (e2,b)).
    cbn in *; apply HR.
    now constructor.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - constructor.
    now apply HRcutl; constructor.
  - constructor.
    now apply HRcutr; constructor.
Qed.

Lemma ruttc_inv_Tau_l :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR (Tau t1) t2 ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros * EQ.
  rcstep in EQ; cbn in EQ.
  dependent induction EQ.
  - rewrite (itree_eta t2), <- x, tau_euttge. exact H.
  - rcstep. exact EQ.
  - rewrite (itree_eta t2), <- x, tau_euttge. eauto.
  - rcstep. rewrite <- x. now constructor.
Qed.

Lemma ruttc_inv_Tau_r :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR t1 (Tau t2) ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros * EQ.
  rcstep in EQ; cbn in EQ.
  dependent induction EQ.
  - rewrite (itree_eta t1), <- x, tau_euttge. exact H.
  - rewrite (itree_eta t1), <- x, tau_euttge. eauto.
  - rcstep. exact EQ.
  - rcstep. rewrite <- x. now constructor.
Qed.

Lemma ruttc_inv_Tau :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR (Tau t1) (Tau t2) ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros.
  now apply ruttc_inv_Tau_l, ruttc_inv_Tau_r.
Qed.  

Lemma ruttc_flip {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR} (t1: itree E1 R1) (t2: itree E2 R2):
  ruttc Rcutl Rcutr REv RAns RR t1 t2 <->
  ruttc Rcutr Rcutl (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; coinduction c CIH; intros t1 t2 Hruttc;
    rcstep in Hruttc; rccbn.
  - induction Hruttc; try now constructor.
    + apply EqTau. now apply CIH.
    + apply EqVis. auto. intros b a HAns. cbn in HAns.
      specialize (H0 a b HAns). now apply CIH.
  - induction Hruttc; try now constructor.
    + apply EqTau. now apply CIH.
    + apply EqVis. auto. intros b a HAns. cbn in HAns.
      specialize (H0 a b HAns). now apply CIH.
Qed.

(* Adapted from [rutt_cong_eutt], with the two cut-off cases. *)
Lemma ruttc_cong_eutt_l {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR}:
  forall (t1: itree E1 R1) t1' (t2: itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  ruttc Rcutl Rcutr REv RAns RR t1' t2.
Proof.
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  coinduction c CIH; intros t1 t1' Heutt t2 Hrutt.
  rcstep in Hrutt; rccbn.
  rewrite (itree_eta t1') in Heutt.
  remember (observe t1) as ot1 eqn:Hot1.
  remember (observe t2) as ot2 eqn:Hot2.
  move Hrutt before CIH; revert_until Hrutt.
  induction Hrutt as [r1 r2|m1 m2| |m1 ot2'| |A e k t' HC|B e k t' HC];
    intros tt1 tt1' Heutt' tt2 Hot1' Hot2'.
  - (* EqRet *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear Hot1' Hot2' tt1 tt2.
    remember (RetF r1) as oRetL eqn:HoRetL.
    induction Heutt'; try discriminate.
    + inv HoRetL. now constructor.
    + apply EqTauL. now apply IHHeutt'.
  - (* EqTau *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear tt1 Hot1'.
    clear tt2 Hot2'.
    rcstep in H.
    remember (TauF m1) as oTauL eqn:HoTauL.
    revert m1 m2 H HoTauL.
    induction Heutt' as [r1 r2 _|m1' m1''|U' e1 k1 k1' _|t1' ot1' _ IHHeutt'|t1'' m1''];
      intros m1 m2 H HoTauL; try discriminate.
    + (* EqTau of Heutt' *)
      inv HoTauL. apply EqTau. apply CIH with m1.
      * apply REL.
      * unfold ruttc. step. exact H.
    + (* EqTauL of Heutt': need to case on the head of m1 *)
      inv HoTauL.
      destruct (observe m1) as [r1|m1_body|U1 e1 k1] eqn:Hobs_m1.
      * (* m1 = Ret r1 *)
        remember (RetF r1) as oRetL eqn:HoRetL.
        clear Hobs_m1 m1 IHIHHeutt'.
        revert H.
        induction IHHeutt'; try discriminate; intros.
        ** inv HoRetL.
           apply EqTauR.
           remember (RetF r1) as oRetL2 eqn:HoRetL2.
           induction H; try discriminate.
           *** inv HoRetL2. constructor. now subst.
           *** apply EqTauR. now apply IHruttcF.
           *** now apply EqCutR.
        ** apply EqTauL. apply IHIHHeutt'; auto.
      * (* m1 = Tau m1_body *)
        apply (IHIHHeutt' m1_body m2); auto.
        unstep. apply ruttc_inv_Tau_l. now rcstep.
      * (* m1 = Vis e1 k1 *)
        remember (VisF e1 k1) as oVisL eqn:HoVisL.
        clear Hobs_m1 m1 IHIHHeutt'.
        revert H.
        induction IHHeutt'; try discriminate; intros.
        ** symmetry in HoVisL; dependent destruction HoVisL.
           apply EqTauR.
           remember (VisF e k0) as oVisL2 eqn:HoVisL2.
           induction H; try discriminate.
           *** dependent destruction HoVisL2.
               apply EqVis; auto. intros a b HAns.
               apply CIH with (k0 a).
               **** apply REL.
               **** apply H0; auto.
           *** apply EqTauR. apply IHruttcF; auto.
           *** dependent destruction HoVisL2. now apply EqCutL.
           *** now apply EqCutR.
        ** apply EqTauL. apply IHIHHeutt'; auto.
    + (* EqTauR of Heutt' *)
      apply EqTau. apply CIH with m1.
      * rewrite <- tau_eutt with (t:=m1). step. subst t1''. exact Heutt'.
      * unfold ruttc. step. exact H.
  - (* EqVis *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear tt1 Hot1' tt2 Hot2'.
    remember (VisF e1 k1) as oVisL eqn:HoVisL.
    induction Heutt'; try discriminate; intros.
    + dependent destruction HoVisL.
      apply EqVis; auto. intros a b HAns.
      apply CIH with (k1 a).
      * apply REL.
      * apply H0; auto.
    + apply EqTauL. apply IHHeutt'; auto.
  - (* EqTauL *)
    eapply IHHrutt with (t1 := m1) (t1' := tt1') (t2 := tt2); auto.
    rewrite <- tau_eutt with (t:=m1). rewrite <- Heutt'.
    rewrite (itree_eta tt1). rewrite <- Hot1'. reflexivity.
  - (* EqTauR *)
    apply EqTauR. eapply IHHrutt; eauto.
  - (* EqCutL *)
    step in Heutt'. cbn in Heutt'.
    rewrite <- Hot1' in Heutt'. clear tt1 Hot1' tt2 Hot2'.
    remember (VisF e k) as oVisL eqn:HoVisL.
    induction Heutt'; try discriminate; intros.
    + dependent destruction HoVisL. now apply EqCutL.
    + apply EqTauL. apply IHHeutt'; auto.
  - (* EqCutR *)
    now apply EqCutR.
Qed.

Lemma ruttc_eutt_l {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INL: eutt eq t1 t2)
      (INR: @ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t2 t3):
  ruttc Rcutl Rcutr REv RAns RR t1 t3.
Proof.
  eapply ruttc_cong_eutt_l; eauto.
  now symmetry.
Qed.

Lemma ruttc_eutt_r {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INR: eutt eq t2 t3)
      (INL: @ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t1 t2):
  ruttc Rcutl Rcutr REv RAns RR t1 t3.
Proof.
  apply ruttc_flip.
  eapply ruttc_cong_eutt_l; eauto.
  now apply ruttc_flip.
Qed.

#[global]Instance ruttc_eutt {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eutt eq ==> eutt eq ==> iff) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; split; intros EQ.
  - eapply ruttc_eutt_l; [symmetry; exact EQ1 |].
    eapply ruttc_eutt_r; [exact EQ2 | exact EQ].
  - eapply ruttc_eutt_l; [exact EQ1 |].
    eapply ruttc_eutt_r; [symmetry; exact EQ2 | exact EQ].
Qed.

#[global]Instance ruttc_eq_itree {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eq_itree Logic.eq ==> eq_itree Logic.eq ==> flip impl) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; rewrite EQ1,EQ2; intuition eauto with *.
Qed.

Lemma ruttc_trigger_cutl
  {E1 E2 R1 S1 R2 Rcutl Rcutr REv RAns RR}
  (e1 : E1 R1) (k1 : R1 -> itree E1 S1) (t2 : itree E2 R2) :
  Rcutl R1 e1 ->
  ruttc Rcutl Rcutr REv RAns RR (trigger e1 >>= k1) t2.
Proof.
  intros.
  unfold trigger; cbn.
  rewrite bind_vis.
  rcstep; now constructor.
Qed.

Lemma ruttc_trigger_cutr
  {E1 E2 R1 R2 S2 Rcutl Rcutr REv RAns RR}
  (t1 : itree E1 R1) (e2 : E2 R2) (k2 : R2 -> itree E2 S2) :
  Rcutr R2 e2 ->
  ruttc Rcutl Rcutr REv RAns RR t1 (trigger e2 >>= k2).
Proof.
  intros.
  unfold trigger; cbn.
  rewrite bind_vis.
  rcstep; now constructor.
Qed.

Lemma ruttc_interp_itree {E1 E2 R1 R2 Rcutl Rcutr REv RAns RR}
  (h1 : E1 ~> itree E1) (h2 : E2 ~> itree E2)
  (Hl: forall A1 (e1 : E1 A1), Rcutl _ e1 -> h1 _ e1 ≅ trigger e1)
  (Hr: forall A2 (e2 : E2 A2), Rcutr _ e2 -> h2 _ e2 ≅ trigger e2)
  (Hh: forall A1 A2 (e1 : E1 A1) (e2 : E2 A2),
      REv _ _ e1 e2 ->
      ruttc Rcutl Rcutr REv RAns (fun a1 a2 => RAns _ _ e1 a1 e2 a2) (h1 _ e1) (h2 _ e2))
  t1 t2
  (HR: @ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t1 t2):
  ruttc Rcutl Rcutr REv RAns RR (interp h1 t1) (interp h2 t2).
Proof.
  revert t1 t2 HR.
  coinduction c cih; intros.
  rewrite 2 unfold_interp.
  rcstep in HR.
  induction HR; cbn -[lattice.body].
  - now constructor.
  - constructor; now apply cih.
  - eapply ruttc_bind_bchain.
    apply Hh; auto.
    intros; constructor.
    apply cih.
    apply H0,H1.
  - rewrite tau_euttge, unfold_interp; auto.
  - rewrite tau_euttge, unfold_interp; auto.
  - rewrite Hl; auto.
    apply (gfp_bchain c).
    apply ruttc_trigger_cutl; auto.
  - rewrite Hr; auto.
    apply (gfp_bchain c).
    apply ruttc_trigger_cutr; auto.
Qed.

Lemma ruttc_trigger'
  {E1 E2 R1 R2 Rcutr Rcutl REv RAns S1 S2 SS} (e1 : E1 R1) (e2 : E2 R2)
  (k1 : R1 -> itree E1 S1) (k2 : R2 -> itree E2 S2):
  REv R1 R2 e1 e2 ->
  (forall a b, RAns R1 R2 e1 a e2 b -> ruttc Rcutr Rcutl REv RAns SS (k1 a) (k2 b)) ->
  @ruttc E1 E2 S1 S2 Rcutr Rcutl REv RAns SS
    (ITree.bind (ITree.trigger e1) k1) (ITree.bind (ITree.trigger e2) k2).
Proof.
  intros * HE HA.
  unfold ITree.trigger.
  rewrite 2 bind_vis.
  rcstep. constructor; auto.
  intros; fold_ruttc.
  rewrite 2 bind_ret_l; apply HA; auto.
Qed.

