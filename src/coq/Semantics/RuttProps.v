From Coq Require Import Program Setoid Morphisms RelationClasses.
From Paco Require Import paco.
From ITree Require Import
  ITree
  ITreeFacts
  Core.Subevent
  Basics.HeterogeneousRelations
  Eq.Rutt
  Props.Leaf.

#[global] Hint Constructors ruttF: core.
#[global] Hint Unfold rutt_: core.
#[global] Hint Unfold rutt: core.
#[global] Hint Unfold id: core.

(* Building blocks to prove rutt *)

Section MakeRutt.
Variables (E1 E2: Type -> Type).
Variables (R1 R2: Type).
Variable (REv: forall T1 T2, E1 T1 -> E2 T2 -> Prop).
Variable (RAns: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).
Variable (RR: R1 -> R2 -> Prop).

Lemma rutt_Ret (r1: R1) (r2: R2):
  RR r1 r2 ->
  rutt REv RAns RR (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. pstep; constructor; auto. Qed.

Lemma rutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
    (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 -> rutt REv RAns RR (k1 t1) (k2 t2)) ->
  rutt REv RAns RR (Vis e1 k1) (Vis e2 k2).
Proof.
  intros He Hk. pstep; constructor; auto.
  intros; left. apply Hk; auto.
Qed.

Lemma rutt_trigger (e1: E1 R1) (e2: E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 -> RR t1 t2) ->
  rutt REv RAns RR (trigger e1) (trigger e2).
Proof.
  intros. apply rutt_Vis; auto.
  intros. apply rutt_Ret; auto.
Qed.
End MakeRutt.

(* Inversion lemmas for eutt, decaying into euttge. *)

Lemma eutt_inv_Ret_l {E R} (r1: R) (t2: itree E R):
  (Ret r1) ≈ t2 -> t2 ≳ (Ret r1).
Proof.
  intros Heutt. punfold Heutt; red in Heutt; cbn in Heutt.
  rewrite itree_eta. remember (RetF r1) as ot1.
  induction Heutt; intros; try discriminate.
  - inv Heqot1. reflexivity.
  - inv Heqot1. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
Qed.

Lemma eutt_inv_Ret_r {E R} (t1: itree E R) (r2: R):
  t1 ≈ (Ret r2) -> t1 ≳ (Ret r2).
Proof.
  intros Heutt. punfold Heutt; red in Heutt; cbn in Heutt.
  rewrite itree_eta. remember (RetF r2) as ot2.
  induction Heutt; intros; try discriminate.
  - inv Heqot2. reflexivity.
  - inv Heqot2. rewrite tau_euttge. rewrite itree_eta. now apply IHHeutt.
Qed.

(* Specialized up-to principles for ≅ and ≳ since typeclasses eauto can't prove
   required properties on the relation (even if trivial for eq) *)

#[global] Instance grutt_cong_eqit_eq {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (Rutt.rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  apply grutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance grutt_cong_euttge_eq {R1 R2 : Type} {E1 E2 : Type -> Type} {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (Rutt.rutt_ REv RAns RS) (euttge_trans_clo RS) r rg).
Proof.
  apply grutt_cong_euttge; now intros * ->.
Qed.

(* Tactic to fold eqitF automatically by expanding observe if needed *)
Tactic Notation "fold_eqitF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | eqitF ?_RR ?_B1 ?_B2 id (upaco2 (eqit_ ?_RR ?_B1 ?_B2 id) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_eqitF in H; [| eauto | eauto]
  end.

(* Manipulations on REv and RAns, specifically equality/flip properties. These
   don't fit nicely in eq_rel or flip because of the heterogenenous quantified
   types *)

Definition eq_REv {E1 E2: Type -> Type} (REv1 REv2: forall A B, E1 A -> E2 B -> Prop) :=
  forall A B, eq_rel (REv1 A B) (REv2 A B).

#[global] Instance eq_REv_Equivalence {E1 E2}: Equivalence (@eq_REv E1 E2).
Proof.
  constructor.
  - red. red. reflexivity.
  - red. intros * H. red in H. red. now symmetry.
  - hnf. intros * H1 H2. red in H1, H2. red. etransitivity; eauto.
Qed.

Definition flip_REv {E1 E2: Type -> Type} (REv1: forall A B, E1 A -> E2 B -> Prop) :=
  fun B A e2 e1 => REv1 A B e1 e2.

Lemma flip_flip_REv {E1 E2} REv1:
  @eq_REv E1 E2 (flip_REv (flip_REv REv1)) REv1.
Proof. reflexivity. Qed.

(* For RAns we want to defer to eq_rel, but for that we need to regroup events
   and their return values into pairs *)
Definition RAns_pair E1 E2 (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) {A B}:
    relationH (E1 A * A) (E2 B * B) :=
  fun '(e1, a) '(e2, b) => RAns A B e1 a e2 b.

Lemma RAns_pair_iff {E1 E2 A B} RAns1:
  forall e1 (a:A) e2 (b:B), RAns_pair E1 E2 RAns1 (e1,a) (e2,b) <-> RAns1 A B e1 a e2 b.
Proof. reflexivity. Qed.

Definition eq_RAns {E1 E2} (RAns1 RAns2: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  forall A B, eq_rel (@RAns_pair E1 E2 RAns1 A B) (@RAns_pair E1 E2 RAns2 A B).

Lemma eq_RAns_iff {E1 E2} {RAns1 RAns2} (H: @eq_RAns E1 E2 RAns1 RAns2):
  forall A B e1 a e2 b, RAns2 A B e1 a e2 b <-> RAns1 A B e1 a e2 b.
Proof. intros *. rewrite <- ! RAns_pair_iff. split; apply H. Qed.

#[global] Instance eq_RAns_Equivalence {E1 E2}: Equivalence (@eq_RAns E1 E2).
Proof.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

Definition flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  fun B A e2 (b:B) e1 (a:A) => flip (@RAns_pair E1 E2 RAns A B) (e2, b) (e1, a).

Lemma flip_RAns_iff {E1 E2 A B} RAns:
  forall e1 (a:A) e2 (b:B), @flip_RAns E1 E2 RAns B A e2 b e1 a <-> RAns _ _ e1 a e2 b.
Proof. reflexivity. Qed.

Lemma flip_flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop):
  eq_RAns (flip_RAns (flip_RAns RAns)) RAns.
Proof. reflexivity. Qed.

(* Additional lemmas and properties on rutt:
   - Inversion principles
   - Congruence for eutt
   - Flip result
   - Bind lemmas (TODO: now bind inversion lemma) *)

Section RuttProps.

Context {E1 E2 : Type -> Type}.
Context {R1 R2 : Type}.
Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
Context (RR : R1 -> R2 -> Prop).

(* Additional inversion principles *)

Lemma ruttF_inv_VisF_r {sim} t1 U2 (e2: E2 U2) (k2: U2 -> _):
  ruttF REv RAns RR sim t1 (VisF e2 k2) ->
  (exists U1 (e1: E1 U1) k1, t1 = VisF e1 k1 /\
    forall v1 v2, RAns _ _ e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
  \/
  (exists t1', t1 = TauF t1' /\
    ruttF REv RAns RR sim (observe t1') (VisF e2 k2)).
Proof.
  refine (fun H =>
    match H in ruttF _ _ _ _ _ t2 return
      match t2 return Prop with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ _ _ _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  - left; eauto.
  - destruct i0; eauto.
Qed.

Lemma ruttF_inv_VisF {sim}
    U1 U2 (e1 : E1 U1) (e2 : E2 U2) (k1 : U1 -> _) (k2 : U2 -> _)
  : ruttF REv RAns RR sim (VisF e1 k1) (VisF e2 k2) ->
    forall v1 v2, RAns U1 U2 e1 v1 e2 v2 -> sim (k1 v1) (k2 v2).
Proof.
  intros H. dependent destruction H. assumption.
Qed.

Ltac unfold_rutt :=
  (try match goal with [|- rutt_ _ _ _ _ _ _ _ ] => red end);
  (repeat match goal with [H: rutt_ _ _ _ _ _ _ _ |- _ ] => red in H end).

Lemma fold_ruttF:
  forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
  ruttF REv RAns RR (upaco2 (rutt_ REv RAns RR) bot2) ot1 ot2 ->
  ot1 = observe t1 ->
  ot2 = observe t2 ->
  rutt REv RAns RR t1 t2.
Proof.
  intros * eq -> ->; pfold; auto.
Qed.

Lemma ruttF_inv_Tau_l {r: itree E1 R1 -> itree E2 R2 -> Prop}:
  forall m1 t2,
  (*                  Maybe generalizable to r? vvvv *)
  ruttF REv RAns RR (upaco2 (rutt_ REv RAns RR) bot2) (TauF m1) (observe t2) ->
  ruttF REv RAns RR (upaco2 (rutt_ REv RAns RR) r) (observe m1) (observe t2).
Proof.
  intros * Hrutt. apply (fold_ruttF (Tau m1) t2) in Hrutt; auto.
  apply rutt_inv_Tau_l in Hrutt. punfold Hrutt; red in Hrutt.
  eapply rutt_monot; eauto using upaco2_mon_bot.

(* Alternative proof that might (?) generalize to any r instead of bot2
  intros * Hrutt; remember (TauF m1) as t1; revert Heqt1.
  induction Hrutt; intros; try discriminate.
  (* EqTau with hypothesis [rutt m1 m2].
     This is the hardest case, since we can't just initiate an ruttF with
     EqTauR; we need to use a symmetric constructor (EqRet/EqTau/EqVis). We
     don't have one, so we unfold the previous level and add our EqTauR on top
     of it. Then we conclude by monotonicity. However when r <> bot2 there
     might not be a lower level! *)
  - inversion Heqt1; clear Heqt1; subst.
    pclearbot. punfold H; red in H.
    apply EqTauR. eapply rutt_monot; eauto using upaco2_mon_bot.
  (* EqTauL *)
  - inversion Heqt1; clear Heqt1; subst.
    rewrite (itree_eta' ot2). eapply rutt_monot; eauto using upaco2_mon_bot.
  (* EqTauR *)
  - subst; rename t0 into m2. apply EqTauR. apply IHHrutt; auto. *)
Qed.

#[global] Instance ruttF_Proper_R:
  Proper (eq                   (* REv *)
      ==> eq                   (* RAns *)
      ==> @eq_rel R1 R2        (* RR *)
      ==> eq_rel               (* sim *)
      ==> eq_rel) (@ruttF E1 E2 R1 R2).
Proof.
  repeat red.
  intros; subst. split; hnf; intros.
  - induction H; try auto.
    constructor. apply H1. assumption.
    constructor. apply H2. assumption.
    constructor. assumption. intros. apply H2, H0, H3.
  - induction H; try auto.
    constructor. apply H1. assumption.
    constructor. apply H2. assumption.
    constructor. assumption. intros. apply H2, H0, H3.
Qed.

Lemma rutt_inv_Ret r1 r2:
  rutt REv RAns RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma rutt_inv_Ret_l r1 t2:
  rutt REv RAns RR (Ret r1) t2 -> exists r2, t2 ≳ Ret r2 /\ RR r1 r2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot1; subst. exists r2. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot1) as [r2 [H1 H2]]. exists r2; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Ret_r t1 r2:
  rutt REv RAns RR t1 (Ret r2) -> exists r1, t1 ≳ Ret r1 /\ RR r1 r2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot2) as [r1 [H1 H2]]. exists r1; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  rutt REv RAns RR (Vis e1 k1) t2 ->
  exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> rutt REv RAns RR (k1 v1) (k2 v2)).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename B into U2.
    exists U2, e2, k2; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - destruct (IHHrutt eq_refl) as (U2 & e2 & k2 & Ht0 & HAns).
    rewrite <- itree_eta in Ht0.
    exists U2, e2, k2; split; auto. now rewrite tau_eutt.
Qed.

Lemma rutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  rutt REv RAns RR t1 (Vis e2 k2) ->
  exists U1 (e1: E1 U1) k1,
    t1 ≈ Vis e1 k1 /\
    REv U1 U2 e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> rutt REv RAns RR (k1 v1) (k2 v2)).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
    subst; rename A into U1.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - destruct (IHHrutt eq_refl) as (U1 & e1 & k1 & Ht0 & HAns).
    rewrite <- itree_eta in Ht0.
    exists U1, e1, k1; split; auto. now rewrite tau_eutt.
Qed.

Lemma rutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  rutt REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
  forall u1 u2, RAns U1 U2 e1 u1 e2 u2 -> rutt REv RAns RR (k1 u1) (k2 u2).
Proof.
  intros H u1 u2 Hans. punfold H.
  apply ruttF_inv_VisF with (v1 := u1) (v2 := u2) in H. pclearbot; auto.
  assumption.
Qed.

End RuttProps.

Tactic Notation "fold_ruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | ruttF ?_REV ?_RANS ?_RR (upaco2 (rutt_ ?_REV ?_RANS ?_RR) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_ruttF in H; [| eauto | eauto]
  end.

Lemma rutt_flip {E1 E2 R1 R2 REv RAns RR} (t1: itree E1 R1) (t2: itree E2 R2):
  rutt REv RAns RR t1 t2 <-> rutt (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt;
  punfold Hrutt; red in Hrutt; pstep; red.
  - induction Hrutt; auto.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
  - induction Hrutt; auto.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
Qed.

#[global] Instance ruttF_Proper_R2 {E1 E2 R1 R2}:
  Proper (eq_REv                                       (* REv *)
      ==> eq_RAns                                      (* RAns *)
      ==> @eq_rel R1 R2                                (* RR *)
      ==> (eq_itree eq ==> eq_itree eq ==> iff)        (* sim *)
      ==> going (eq_itree eq)                          (* t1 *)
      ==> going (eq_itree eq)                          (* t2 *)
      ==> iff) (@ruttF E1 E2 R1 R2).
Proof.
  intros REv REv' HREv RAns RAns' HRAns RR RR' HRR.
  intros sim sim' Hsim t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.

  - revert t1' t2' Ht1 Ht2; induction Hrutt; intros;
    destruct Ht1 as [Ht1], Ht2 as [Ht2]; symmetry in Ht1, Ht2.
    * apply eqitree_inv_Ret_r in Ht1; cbn in Ht1; subst.
      apply eqitree_inv_Ret_r in Ht2; cbn in Ht2; subst.
      constructor. now apply HRR.
    * apply eqitree_inv_Tau_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      apply eqitree_inv_Tau_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. symmetry in H1, H2. eapply Hsim; eauto.
    * apply eqitree_inv_Vis_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      apply eqitree_inv_Vis_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. now apply HREv.
      intros. specialize (H2 a). specialize (H3 b). symmetry in H2, H3.
      apply (Hsim _ _ H2 _ _ H3). apply H0. erewrite <- eq_RAns_iff.
      apply H1. assumption.
    * apply eqitree_inv_Tau_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      constructor. apply IHHrutt.
      constructor. symmetry. rewrite <- ! itree_eta. assumption.
      constructor. symmetry. assumption.
    * apply eqitree_inv_Tau_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. apply IHHrutt.
      constructor. symmetry. assumption.
      constructor. symmetry. rewrite <- ! itree_eta. assumption.

  (* Same thing; t1->t1', t1'->t1'' (name conflict), remove symmetry *)
  - revert t1 Ht1 t2 Ht2; induction Hrutt; intros;
    destruct Ht1 as [Ht1], Ht2 as [Ht2].
    * apply eqitree_inv_Ret_r in Ht1; cbn in Ht1; subst.
      apply eqitree_inv_Ret_r in Ht2; cbn in Ht2; subst.
      constructor. now apply HRR.
    * apply eqitree_inv_Tau_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      apply eqitree_inv_Tau_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. eapply Hsim; eauto.
    * apply eqitree_inv_Vis_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      apply eqitree_inv_Vis_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. now apply HREv.
      intros. specialize (H2 a). specialize (H3 b).
      apply (Hsim _ _ H2 _ _ H3). apply H0. erewrite eq_RAns_iff.
      apply H1. assumption.
    * apply eqitree_inv_Tau_r in Ht1; cbn in Ht1; destruct Ht1 as [? []]; subst.
      constructor. apply IHHrutt.
      constructor. rewrite <- ! itree_eta. assumption.
      constructor. assumption.
    * apply eqitree_inv_Tau_r in Ht2; cbn in Ht2; destruct Ht2 as [? []]; subst.
      constructor. apply IHHrutt.
      constructor. assumption.
      constructor. rewrite <- ! itree_eta. assumption.
Qed.

#[global] Instance rutt_Proper_R {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv1 REv2 HREv  RAns1 RAns2 HRAns RR1 RR2 HRR t1 _ <- t2 _ <-.
  split; intros Hrutt.

  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. pclearbot. pinversion H.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns1 A B e1 a e2 b). { erewrite <- eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. pclearbot. pinversion H0.

  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. pclearbot. pinversion H.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns2 A B e1 a e2 b). { erewrite eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. pclearbot. pinversion H0.
Qed.

#[global] Instance rutt_Proper_R2 {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  clear. intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.

  - rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
    ginit. gclo. econstructor; eauto with paco.
    * symmetry in Ht1. apply eq_sub_euttge in Ht1. apply Ht1.
    * symmetry in Ht2. apply eq_sub_euttge in Ht2. apply Ht2.
    * intros; now subst.
    * intros; now subst.

  - rewrite HREv, HRAns, HRR; clear HREv REv1 HRAns RAns1 HRR RR1.
    ginit. gclo. econstructor; eauto with paco.
    * apply eq_sub_euttge in Ht1. apply Ht1.
    * apply eq_sub_euttge in Ht2. apply Ht2.
    * intros; now subst.
    * intros; now subst.
Qed.

Lemma rutt_cong_eutt {E1 E2 R1 R2}:
  forall REv RAns RR (t1: itree E1 R1) t1' (t2: itree E2 R2),
  rutt REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  rutt REv RAns RR t1' t2.
Proof.
  (* First by coinduction; then do an induction on Hrutt to expose the ruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore ruttF until landing on an rutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  ginit; gcofix CIH; intros t1 t1' Heutt t2 Hrutt.
  punfold Hrutt; red in Hrutt.
  rewrite (itree_eta t1) in Heutt.
  rewrite (itree_eta t2).

  move Hrutt before CIH; revert_until Hrutt.
  induction Hrutt as [r1 r2|m1 m2| |m1 ot2|]; clear t1 t2; intros t1' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  * apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  * punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. fold_ruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (itree_eta m1) in Hrutt.
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge. gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply rutt_inv_Tau_l in Hrutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros; try discriminate.
        - symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (itree_eta m2).
          punfold Hrutt; red in Hrutt; cbn in Hrutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Hrutt; intros; try discriminate.
          * dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          * idtac. rewrite tau_euttge, (itree_eta t2). now apply IHHrutt.
        - idtac. rewrite tau_euttge, itree_eta; now apply IHHeutt. }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for rutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  * rewrite itree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + now apply EqTauL, IHHeutt.

  (* EqTauL: We get a very strong IHHrutt at the ruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  * apply IHHrutt. rewrite <- itree_eta. now rewrite <- tau_eutt.

  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  * rewrite tau_euttge. rewrite (itree_eta t0). now apply IHHrutt.
Qed.

#[global] Instance rutt_Proper_R3 {E1 E2 R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  - eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
  - symmetry in Ht1, Ht2.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *. eapply rutt_cong_eutt; eauto.
Qed.

Section RuttBind.

Context {E1 E2 : Type -> Type}.
Context {R1 R2 : Type}.
Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
Context (RR : R1 -> R2 -> Prop).

Inductive rutt_bind_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
  itree E1 R1 -> itree E2 R2 -> Prop :=
| rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: rutt REv RAns RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : rutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors rutt_bind_clo: core.

Lemma rutt_clo_bind :
  rutt_bind_clo <3= gupaco2 (rutt_ REv RAns RR) (euttge_trans_clo RR).
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
Qed.

End RuttBind.

(* Properties on bind for rutt *)
Lemma rutt_bind
      {E1 E2 : Type -> Type}
      {R1 R2 : Type}
      (REv : forall (A B : Type), E1 A -> E2 B -> Prop)
      (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop)
      (RR : R1 -> R2 -> Prop)
      {T1 T2} (RT: T1 -> T2 -> Prop):
  forall (t1: itree E1 R1) (k1: R1 -> itree E1 T1)
    (t2: itree E2 R2) (k2: R2 -> itree E2 T2),
    rutt REv RAns RR t1 t2 ->
    (forall r1 r2, RR r1 r2 -> rutt REv RAns RT (k1 r1) (k2 r2)) ->
    rutt REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit.
  (* For some reason [guclo] fails, visibly trying to infer the type in a context with less information? *)
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H0. eauto.
Qed.

(* Relation with eutt when there is only one type of events *)
Section RuttEutt.

Context {E: Type -> Type} {R1 R2: Type}.
Context {RR: R1 -> R2 -> Prop}.
Context (REv : forall (A B : Type), E A -> E B -> Prop).
Context (RAns : forall (A B : Type), E A -> A -> E B -> B -> Prop).

(* Admittedly scuffed *)
Context (REv_reflexive: forall U, Reflexive (REv U U)).
Context (RAns_in_reflexive: forall U e u1 u2, RAns U U e u1 e u2 -> u1 = u2).
Arguments RAns_in_reflexive {U e u1 u2}.

Lemma eqit_rutt_subrelation: forall t1 t2,
  eutt RR t1 t2 -> rutt REv RAns RR t1 t2.
Proof.
  pcofix CIH; intros * H. pstep. punfold H. red in H. red.
  hinduction H before CIH; intros; eauto.
  - apply EqTau. red. pclearbot. right. apply CIH. do 2 red. assumption.
  - apply EqVis. apply REv_reflexive.
    intros * Hans. red. right. apply CIH.
    pose proof (RAns_in_reflexive Hans) as <-. specialize (REL a). red in REL.
    pclearbot. apply REL.
Qed.

End RuttEutt.
