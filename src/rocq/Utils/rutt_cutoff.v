(** * Equivalence up to tau with relation on events and cutoffs *)

(** [rutt] generalizes [eutt] by taking as parameter
    a relation on the signatures of the related computations.
    [ruttc] further refines it by allowing to treat some
    events as valid cutoffs in the refinement: typically,
    relating Undefined Behavior in the source to any
    computation in the target.

    Things get quite verbose, but it's overall straightforwards.
 *)

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
.

From Paco Require Import paco.

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

  Lemma ruttc_monot : monotone2 ruttc_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition ruttc : itree E1 R1 -> itree E2 R2 -> Prop := paco2 ruttc_ bot2.
  Hint Unfold ruttc : itree.

End RuttcF.
Hint Resolve ruttc_monot : paco.
Hint Constructors ruttcF : itree.

(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 R1 R2
  (Rcutl : forall A, E1 A -> Prop)
  (Rcutr : forall B, E2 B -> Prop)
  (REv : prerel E1 E2)
  (RAns : postrel E1 E2)
  (RR : R1 -> R2 -> Prop) :
  wcompatible2
    (ruttc_ Rcutl Rcutr REv RAns RR)
    (euttge_trans_clo RR).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR. punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst; try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail)).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H1. pclearbot.
    apply gpaco2_clo.
    econstructor; eauto with itree.
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (VisF e k) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    dependent destruction H2.
    now constructor.
  - remember (VisF e k) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    dependent destruction H2.
    now constructor.
Qed.

#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* Overly general principle allowing for adjoining
   non-eq but compatible post-conditions on the sides.
   Incompatible with rewrite so we specialize right after.
 *)
Lemma gruttc_cong_eqit_gen
  {R1 R2 : Type} {E1 E2 : Type -> Type}
  {Rcutl : forall A, E1 A -> Prop}
  {Rcutr : forall B, E2 B -> Prop}
  {REv : prerel E1 E2}
  {RAns : postrel E1 E2}
  {RR1 RR2} {RR : R1 -> R2 -> Prop} b r rg
  (LERR1: forall x x' y, (RR1 x x': Prop) -> (RR x' y: Prop) -> RR x y)
  (LERR2: forall x y y', (RR2 y y': Prop) -> RR x y' -> RR x y) :
  Proper (eqit RR1 b false ==> eqit RR2 b false ==> flip impl)
    (gpaco2 (ruttc_ Rcutl Rcutr REv RAns RR) (euttge_trans_clo RR) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

(* Rewriting [eq_itree eq] *)
#[global] Instance gruttc_cong_eq_itree
  {R1 R2 : Type} {E1 E2 : Type -> Type}
  {Rcutl : forall A, E1 A -> Prop}
  {Rcutr : forall B, E2 B -> Prop}
  {REv : prerel E1 E2}
  {RAns : postrel E1 E2}
  {RR : R1 -> R2 -> Prop} r rg :
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
    (gpaco2 (ruttc_ Rcutl Rcutr REv RAns RR) (euttge_trans_clo RR) r rg).
Proof.
  repeat intro; eapply gruttc_cong_eqit_gen; eauto; intuition; subst; auto.
Qed.

(* Rewriting [euttge eq] *)
#[global] Instance gruttc_cong_euttge
  {R1 R2 : Type} {E1 E2 : Type -> Type}
  {Rcutl : forall A, E1 A -> Prop}
  {Rcutr : forall B, E2 B -> Prop}
  {REv : prerel E1 E2}
  {RAns : postrel E1 E2}
  {RR : R1 -> R2 -> Prop} r rg :
  Proper (euttge eq ==> euttge eq ==> flip impl)
    (gpaco2 (ruttc_ Rcutl Rcutr REv RAns RR) (euttge_trans_clo RR) r rg).
Proof.
  repeat intro; eapply gruttc_cong_eqit_gen; eauto; intuition; subst; auto.
Qed.

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

  - revert t1 t2 Hruttc; ginit; gcofix CIH; intros t1 t2 Hruttc.
    rewrite (itree_eta t1), (itree_eta t2). 
    punfold Hruttc; red in Hruttc.
    hinduction Hruttc before CIH; intros; pclearbot.
    + gstep; constructor; now apply HRR.
    + gstep; constructor; eauto with paco.
    + gstep; constructor.
      now apply HREv.
      intros; gfinal; left; apply CIH.
      apply H0.
      assert (H2: RAns1 A B e1 a e2 b); eauto.
      { erewrite <- eq_RAns_iff. apply H1. assumption. }
    + rewrite tau_euttge, itree_eta; apply IHHruttc.
    + rewrite tau_euttge, (itree_eta t0); apply IHHruttc.
    + gstep; constructor; apply EQcutl; auto.
    + gstep; constructor; apply EQcutr; auto.

  - revert t1 t2 Hruttc; ginit; gcofix CIH; intros t1 t2 Hruttc.
    rewrite (itree_eta t1), (itree_eta t2). 
    punfold Hruttc; red in Hruttc.
    hinduction Hruttc before CIH; intros; pclearbot.
    + gstep; constructor; now apply HRR.
    + gstep; constructor; eauto with paco.
    + gstep; constructor.
      now apply HREv.
      intros; gfinal; left; apply CIH.
      apply H0.
      assert (H2: RAns2 A B e1 a e2 b); eauto.
      { erewrite eq_RAns_iff. apply H1. assumption. }
    + rewrite tau_euttge, itree_eta; apply IHHruttc.
    + rewrite tau_euttge, (itree_eta t0); apply IHHruttc.
    + gstep; constructor; apply EQcutl; auto.
    + gstep; constructor; apply EQcutr; auto.
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
  ginit; gcofix CIH; intros t1 t2 Hruttc.
  rewrite (itree_eta t1), (itree_eta t2).
  punfold Hruttc; red in Hruttc.
  hinduction Hruttc before CIH; intros; pclearbot.
  - gstep; constructor; auto.
  - gstep; constructor; eauto with paco.
  - gstep; constructor; auto.
    intros; gfinal; left; apply CIH, H0, HRAns; auto.
  - rewrite tau_euttge, itree_eta; apply IHHruttc.
  - rewrite tau_euttge, (itree_eta t0); apply IHHruttc.
  - gstep; constructor; auto.
  - gstep; constructor; auto.
Qed.

(* The usual up-to bind *)
Section RuttcBind.
  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  Context (Rcutl : pred1 E1).
  Context (Rcutr : pred1 E2).
  Context (REv : prerel E1 E2).
  Context (RAns : postrel E1 E2).
  Context (RR : R1 -> R2 -> Prop).

  Inductive ruttc_bind_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
  | rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: ruttc Rcutl Rcutr REv RAns RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
    : ruttc_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
  .
  Hint Constructors ruttc_bind_clo: core.

  Lemma ruttc_clo_bind :
    ruttc_bind_clo <3= gupaco2 (ruttc_ Rcutl Rcutr REv RAns RR) (euttge_trans_clo RR).
  Proof.
    intros rr. gcofix CIH. intros. destruct PR.
    gclo; econstructor; auto_ctrans_eq.
    1,2: rewrite unfold_bind; reflexivity.
    punfold EQV. unfold rutt_ in *.
    hinduction EQV before CIH; intros; pclearbot; cbn;
      repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
    - gclo. econstructor; auto_ctrans_eq.
      1,2: reflexivity.
      eauto with paco.
    - gstep. econstructor. eauto 7 with paco.
    - gstep. econstructor; eauto 7 with paco.
      intros. specialize (H0 a b H1). pclearbot. eauto 7 with paco.
    - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
    - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
    - gstep.
      now constructor.
    - gstep.
      now constructor.
   Qed.

End RuttcBind.

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
  intros. ginit.
  (* For some reason [guclo] fails, apparently trying to infer the type in a
     context with less information? *)
  eapply gpaco2_uclo; [|eapply ruttc_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H0. eauto.
Qed.

(* Proof rules *)
(* ret *)
Lemma ruttc_ret {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (v1 : R1) (v2 : R2):
  RR v1 v2 ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (Ret v1) (Ret v2).
Proof.
  pfold; constructor; auto.
Qed. 

(* trigger *)
Lemma ruttc_trigger {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (e1 : E1 R1) (e2 : E2 R2):
  REv R1 R2 e1 e2 ->
  (forall a b, RAns R1 R2 e1 a e2 b -> RR a b) ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (ITree.trigger e1) (ITree.trigger e2).
Proof.
  pfold; constructor; auto.
  intros.
  left; pfold; constructor; auto.
Qed. 

(* trigger_cast *)
Lemma ruttc_trigger_cast {E1 E2 : Type -> Type} {Rcutr Rcutl} {REv : prerel E1 E2} {RAns A1 A2 RR} (e1 : E1 void) (e2 : E2 void):
  REv void void e1 e2 ->
  @ruttc E1 E2 A1 A2 Rcutr Rcutl REv RAns RR
    (trigger_cast' e1) (trigger_cast' e2).
Proof.
  intros.
  pfold.
  unfold trigger_cast.
  red; cbn.
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
  ginit.
  revert i1 i2.
  gcofix cih.
  intros * HI.
  setoid_rewrite unfold_iter.
  eapply gpaco2_uclo; [|eapply ruttc_clo_bind|]; eauto with paco.
  econstructor.
  now apply Hind.
  clear i1 i2 HI; intros [|] [|] REL; inv REL.
  gstep; constructor; eauto with paco.
  gstep; constructor; eauto.
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
  ginit. gcofix CIH.
  intros * EQ.
  rewrite 2 unfold_interp_mrec.
  punfold EQ; red in EQ.
  induction EQ; cbn; pclearbot.
  - now gstep; constructor.
  - gstep; constructor; eauto with paco.
  - dependent induction H.
    + gstep; constructor.
      gfinal; left; apply CIH.
      eapply ruttc_bind.
      now apply HInd.
      now intros; apply H0; constructor.
    + gstep; constructor; intros; auto.
      gstep; constructor; intros; auto.
      gfinal; left; apply CIH, H0; constructor; auto.
  - rewrite tau_euttge.
    rewrite unfold_interp_mrec; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_interp_mrec; apply IHEQ.
  - dependent induction H.
    + destruct H.
    + gstep; constructor; auto.
  - dependent induction H.
    + destruct H.
    + gstep; constructor; auto.
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
  ginit; gcofix cih.
  intros * EQ.
  punfold EQ; red in EQ.
  rewrite 2 unfold_translate. 
  induction EQ; cbn; pclearbot.
  - now gstep; constructor.
  - gstep; constructor; eauto with paco.
  - gstep. constructor; auto.
    constructor; auto.
    intros; gfinal; left; eapply cih.
    dependent induction H1; apply H0; auto.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - gstep; do 2 constructor; eauto.   
  - gstep; do 2 constructor; eauto.   
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
  ginit; gcofix cih.
  intros * EQ.
  punfold EQ; red in EQ.
  rewrite 2 unfold_translate. 
  induction EQ; cbn; pclearbot.
  - now gstep; constructor.
  - gstep; constructor; eauto with paco.
  - gstep. constructor; auto.
    edestruct HREv as [_ HR].
    specialize (HR e1 e2 H).
    now dependent induction HR.
    intros; gfinal; left; eapply cih.
    apply H0.
    edestruct HRAns as [HR _].
    specialize (HR (e1,a) (e2,b)).
    cbn in *; apply HR.
    now constructor.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - rewrite tau_euttge.
    rewrite unfold_translate; apply IHEQ.
  - gstep; constructor.
    now apply HRcutl; constructor.
  - gstep; constructor.
    now apply HRcutr; constructor.
Qed. 

Lemma ruttc_inv_Tau_l :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR (Tau t1) t2 ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
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

Lemma ruttc_inv_Tau_r :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR t1 (Tau t2) ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
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

Lemma ruttc_inv_Tau :
forall {E1 E2 : Type -> Type} {R1 R2 : Type} Rcutr Rcutl REv RAns {RR : R1 -> R2 -> Prop}
  (t1 : itree E1 R1) (t2 : itree E2 R2),
  ruttc Rcutl Rcutr REv RAns RR (Tau t1) (Tau t2) ->
  ruttc Rcutl Rcutr REv RAns RR t1 t2.
Proof.
  intros.
  now apply ruttc_inv_Tau_l, ruttc_inv_Tau_r.
Qed.  

Lemma ruttc_eutt_l {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INL: eutt eq t1 t2)
      (INR: @ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t2 t3):
  ruttc Rcutl Rcutr REv RAns RR t1 t3.
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
        constructor; left; eapply paco2_mon; eauto; intuition easy.
        constructor; auto.
        intros; left; eapply paco2_mon; eauto; intuition easy.
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
        pose proof ruttc_inv_Tau_l (RR := RR) Rcutr Rcutl REv RAns t2 m2.
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

Lemma ruttc_eutt_r {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} t1 t2 t3
      (INR: eutt eq t2 t3)
      (INL: @ruttc E1 E2 R1 R2 Rcutl Rcutr REv RAns RR t1 t2):
  ruttc Rcutl Rcutr REv RAns RR t1 t3.
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
        constructor; left; eapply paco2_mon; eauto; intuition easy.
        constructor; auto.
        intros; left; eapply paco2_mon; eauto; intuition easy.
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
        pose proof ruttc_inv_Tau_r (RR := RR) Rcutr Rcutl REv RAns m1 t1.
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

#[global]Instance ruttc_eutt {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eutt eq ==> eutt eq ==> iff) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; split; intros EQ.
  eapply ruttc_eutt_l, ruttc_eutt_r; eauto; symmetry; eauto.
  eapply ruttc_eutt_l, ruttc_eutt_r; eauto; symmetry; eauto.
Qed.

#[global]Instance ruttc_eq_itree {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eq_itree Logic.eq ==> eq_itree Logic.eq ==> flip impl) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; rewrite EQ1,EQ2; intuition eauto with *.
Qed.

