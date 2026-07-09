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
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Section RuttcF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  (* Cutoff on the left *)
  Context (Rcutl : forall (A : Type), E1 A -> Prop ).
  (* Cutoff on the right *)
  Context (Rcutr : forall (B : Type), E2 B -> Prop ).
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
  Context (RR : R1 -> R2 -> Prop).
  Arguments Rcutl {A}.
  Arguments Rcutr {B}.
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive ruttcF (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttcF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttcF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
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
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
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
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
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

Section RuttcBind.
  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.
  Context (Rcutl : forall (A : Type), E1 A -> Prop ).
  Context (Rcutr : forall (B : Type), E2 B -> Prop ).
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
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

Lemma ruttc_bind {E1 E2 R1 R2 T1 T2}
  (Rcutl : forall (A : Type), E1 A -> Prop )
  (Rcutr : forall (B : Type), E2 B -> Prop )
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
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

Lemma ruttc_ret {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (v1 : R1) (v2 : R2):
  RR v1 v2 ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (Ret v1) (Ret v2).
Proof.
  pfold; constructor; auto.
Qed. 

Lemma ruttc_trigger {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} (e1 : E1 R1) (e2 : E2 R2):
  REv R1 R2 e1 e2 ->
  (forall a b, RAns R1 R2 e1 a e2 b -> RR a b) ->
  @ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR (ITree.trigger e1) (ITree.trigger e2).
Proof.
  pfold; constructor; auto.
  intros.
  left; pfold; constructor; auto.
Qed. 

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

Lemma ruttc_map_monad {E1 E2 R1 R2 A}
  (Rcutl : forall (A : Type), E1 A -> Prop )
  (Rcutr : forall (B : Type), E2 B -> Prop )
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
  (RR: R1 -> R2 -> Prop)
  (f1 : A -> itree E1 R1) (f2 : A -> itree E2 R2) l:
  (forall a, In a l -> ruttc Rcutl Rcutr REv RAns RR (f1 a) (f2 a)) ->
  ruttc Rcutl Rcutr REv RAns (Forall2 RR)
    (map_monad f1 l)
    (map_monad f2 l).
Proof.
  induction l as [| a l IH]; intros HIN; cbn.
  - now apply ruttc_ret.
  - eapply ruttc_bind; [apply HIN; now left |].
    intros r1 r2 HR.
    eapply ruttc_bind; [apply IH; intros; apply HIN; now right|].
    intros bs1 bs2 HBS.
    apply ruttc_ret.
    now constructor.
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

Lemma ruttc_eutt {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eutt eq ==> eutt eq ==> iff) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; split; intros EQ.
  eapply ruttc_eutt_l, ruttc_eutt_r; eauto; symmetry; eauto.
  eapply ruttc_eutt_l, ruttc_eutt_r; eauto; symmetry; eauto.
Qed.

