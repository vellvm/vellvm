From Coq Require Import
  Program
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Core.Subevent
  Basics.HeterogeneousRelations
  Eq.Rutt
  Props.Leaf.

From Vellvm Require Import
  Utils.OOMRutt.

(* Extra construction lemmas *)

Lemma orutt_trigger {E1 E2 OOM : Type -> Type} {OOME : OOM -< E2} {R1 R2} {REv : prerel E1 E2} {RAns : postrel E1 E2} {RR : R1 -> R2 -> Prop} (e1: E1 R1) (e2: E2 R2):
  (REv _ _ e1 e2: Prop) ->
  (forall t1 t2, (RAns _ _ e1 t1 e2 t2: Prop) -> (RR t1 t2: Prop)) ->
  (forall o : OOM R2, e2 <> subevent _ o) ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (trigger e1) (trigger e2).
Proof using.
  intros. apply orutt_Vis; auto.
  intros. apply orutt_Ret; auto.
Qed.

(* Morphisms related to [REv] and [RAns]. Both behave nicely up to quantified
   relation equality. There are also symmetry results when flipped.
*)

(* We can't use eq_rel directly due to dependent quantification *)
Definition eq_REv {E1 E2: Type -> Type} (REv1 REv2: forall A B, E1 A -> E2 B -> Prop) :=
  forall A B, eq_rel (REv1 A B) (REv2 A B).

#[global] Instance eq_REv_Equivalence {E1 E2}: Equivalence (@eq_REv E1 E2).
Proof using.
  constructor.
  - red. red. reflexivity.
  - red. intros * H. red in H. red. now symmetry.
  - hnf. intros * H1 H2. red in H1, H2. red. etransitivity; eauto.
Qed.

Definition flip_REv {E1 E2: Type -> Type} (REv1: forall A B, E1 A -> E2 B -> Prop) :=
  fun B A e2 e1 => REv1 A B e1 e2.

Lemma flip_flip_REv {E1 E2} REv1:
  @eq_REv E1 E2 (flip_REv (flip_REv REv1)) REv1.
Proof using. reflexivity. Qed.

(* For RAns we want to defer to eq_rel, but for that we need to regroup events
   and their return values into pairs.
*)
Definition RAns_pair E1 E2 (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) {A B}:
    relationH (E1 A * A) (E2 B * B) :=
  fun '(e1, a) '(e2, b) => RAns A B e1 a e2 b.

Lemma RAns_pair_iff {E1 E2 A B} RAns1:
  forall e1 (a:A) e2 (b:B), RAns_pair E1 E2 RAns1 (e1,a) (e2,b) <-> RAns1 A B e1 a e2 b.
Proof using. reflexivity. Qed.

Definition eq_RAns {E1 E2} (RAns1 RAns2: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  forall A B, eq_rel (@RAns_pair E1 E2 RAns1 A B) (@RAns_pair E1 E2 RAns2 A B).

Lemma eq_RAns_iff {E1 E2} {RAns1 RAns2} (H: @eq_RAns E1 E2 RAns1 RAns2):
  forall A B e1 a e2 b, RAns2 A B e1 a e2 b <-> RAns1 A B e1 a e2 b.
Proof using. intros *. rewrite <- ! RAns_pair_iff. split; apply H. Qed.

#[global] Instance eq_RAns_Equivalence {E1 E2}: Equivalence (@eq_RAns E1 E2).
Proof using.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

Definition flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  fun B A e2 (b:B) e1 (a:A) => flip (@RAns_pair E1 E2 RAns A B) (e2, b) (e1, a).

Lemma flip_RAns_iff {E1 E2 A B} RAns:
  forall e1 (a:A) e2 (b:B), @flip_RAns E1 E2 RAns B A e2 b e1 a <-> RAns _ _ e1 a e2 b.
Proof using. reflexivity. Qed.

Lemma flip_flip_RAns {E1 E2} (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop):
  eq_RAns (flip_RAns (flip_RAns RAns)) RAns.
Proof using. reflexivity. Qed.

(* (* This probably isn't true because OOM isn't symmetrical *) *)
(* Lemma orutt_flip {E1 E2 OOM : Type -> Type} {OOME1 : OOM -< E1} {OOME2 : OOM -< E2} {R1 R2} {REv : prerel E1 E2} {RAns : postrel E1 E2} {RR : R1 -> R2 -> Prop} (t1: itree E1 R1) (t2: itree E2 R2): *)
(*   @orutt E1 E2 OOM OOME2 R1 R2 REv RAns RR t1 t2 <-> @orutt E2 E1 OOM OOME1 R2 R1 (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1. *)
(* Proof using. *)
(*   split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt; *)
(*   punfold Hrutt; red in Hrutt; pstep; red. *)
(*   - induction Hrutt; try now constructor. *)
(*     * apply EqTau. right. apply CIH. now pclearbot. *)
(*     * apply EqVis. auto. intros b a HAns. cbn in HAns. right. *)
(*       specialize (H0 a b HAns). apply CIH. now pclearbot. *)
(*   - induction Hrutt; try now constructor. *)
(*     * apply EqTau. right. apply CIH. now pclearbot. *)
(*     * apply EqVis. auto. intros b a HAns. cbn in HAns. right. *)
(*       specialize (H0 a b HAns). apply CIH. now pclearbot. *)
(* Qed. *)

(* Progressive [Proper] instances for [rutt] and congruence with eutt. *)

#[global] Instance orutt_Proper_R {E1 E2 OOM OOME R1 R2} :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@orutt E1 E2 OOM OOME R1 R2).
Proof using.
  intros REv1 REv2 HREv  RAns1 RAns2 HRAns RR1 RR2 HRR t1 _ <- t2 _ <-.
  split; intros Hrutt.

  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros a b HAns.
      assert (H2: RAns1 A B e1 a e2 b).
      { erewrite <- eq_RAns_iff. apply HAns. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
      auto.
    * apply EqVisOOM.
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros a b HAns.
      assert (H2: RAns2 A B e1 a e2 b).
      { erewrite eq_RAns_iff. apply HAns. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
      auto.
    * apply EqVisOOM.
Qed.

#[global] Instance orutt_Proper_R2 {E1 E2 OOM OOME R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@orutt E1 E2 OOM OOME R1 R2).
Proof using.
  clear. intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  split; intros Horutt.

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

Lemma orutt_cong_eutt {E1 E2 OOM OOME R1 R2}:
  forall REv RAns RR (t1: itree E1 R1) t1' (t2: itree E2 R2),
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1' t2.
Proof using.
  (* First by coinduction; then do an induction on Horutt to expose the oruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore oruttF until landing on an orutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Horutt Heutt; revert t1 t1' Heutt t2 Horutt.
  ginit; gcofix CIH; intros t1 t1' Heutt t2 Horutt.
  punfold Horutt; red in Horutt.
  rewrite (itree_eta t1) in Heutt.
  rewrite (itree_eta t2).

  move Horutt before CIH; revert_until Horutt.
  induction Horutt as [r1 r2|m1 m2| |m1 ot2| |]; clear t1 t2; intros t1' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  * apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  * punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. fold_oruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Horutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (itree_eta m1) in Horutt.
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge. gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply orutt_inv_Tau_l in Horutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros; try discriminate.
        - symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (itree_eta m2).
          punfold Horutt; red in Horutt; cbn in Horutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Horutt; intros; try discriminate.
          * dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          * (* OOM... Any tree should work *)
            gfinal; right. pstep.
            apply EqVisOOM.
          * idtac. rewrite tau_euttge, (itree_eta t2). now apply IHHorutt.
        - idtac. rewrite tau_euttge, itree_eta; now apply IHHeutt. }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for orutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  * rewrite itree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + now apply EqTauL, IHHeutt.

  * rewrite itree_eta. gfinal; right; pstep.
    apply EqVisOOM.

  (* EqTauL: We get a very strong IHHorutt at the oruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  * apply IHHorutt. rewrite <- itree_eta. now rewrite <- tau_eutt.

  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  * rewrite tau_euttge. rewrite (itree_eta t0). now apply IHHorutt.
Qed.

Lemma orutt_cong_eutt2 {E1 E2 OOM OOME R1 R2}:
  forall REv RAns RR (t1: itree E1 R1) (t2: itree E2 R2) t2',
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2 ->
  t2 ≈ t2' ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2'.
Proof using.
  (* First by coinduction; then do an induction on Horutt to expose the oruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore oruttF until landing on an orutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Horutt Heutt; revert t1 t2 t2' Heutt Horutt.
  ginit; gcofix CIH; intros t1 t2 t2' Heutt Horutt.
  punfold Horutt; red in Horutt.
  rewrite (itree_eta t2) in Heutt.
  rewrite (itree_eta t1).
  rewrite (itree_eta t2') in *.

  move Horutt before CIH; revert_until Horutt.
  induction Horutt as [r1 r2|m1 m2| |m1 ot2| |]; clear t1 t2; intros t2' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  * apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  * punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. fold_oruttF H.
    remember (TauF m2) as ot2; revert m1 m2 H Heqot2.
    induction Heutt as [|m2_bis m2'| |m2_bis ot2' _|t2_bis m2'];
    intros * Horutt Heqot2; try discriminate.
    + inv Heqot2. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1 m2).
    + inv Heqot2. rewrite (itree_eta m2) in Horutt.
      desobs m2 Hm2; clear m2 Hm2.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge. gfinal; right. eapply paco2_mon_bot; eauto.
        punfold Horutt.
      }
      { apply orutt_inv_Tau_r in Horutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m2; revert Heqm2.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros; try discriminate.
        - symmetry in Heqm2; dependent destruction Heqm2.
          rewrite tau_euttge, (itree_eta m1).
          punfold Horutt; red in Horutt; cbn in Horutt.
          remember (VisF e1 k1) as m2; revert Heqm2.
          induction Horutt; intros; try discriminate.
          * dependent destruction Heqm2.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k0 v1) (k1 v2)); auto.
            apply Hk1k1'.
          * inv Heqm2. subst_existT.
            gfinal; right. pstep.
            apply EqVisOOM.
          * idtac. rewrite tau_euttge, (itree_eta t1). now apply IHHorutt.
        - idtac. cbn. subst. rewrite (tau_euttge t2), (itree_eta t2); now apply IHHeutt. }
    + inv Heqot2. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1 m2).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for orutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  * rewrite itree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e2 k2) as m2; revert Heqm2.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm2.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a) (k2 b)); auto. apply REL.
    + now apply EqTauR, IHHeutt.

  * rewrite itree_eta. gfinal; right; pstep.
    punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF (subevent m1 ot2) k2) as m2; revert Heqm2.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm2.
      apply EqVisOOM.
    + subst.
      apply EqTauR.
      apply IHHeutt.
      auto.


  * rewrite tau_euttge. rewrite (itree_eta t0). now apply IHHorutt.
  * apply IHHorutt. rewrite <- itree_eta. now rewrite <- tau_eutt.
Qed.


#[global] Instance orutt_Proper_R3 {E1 E2 OOM OOME R1 R2}:
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@orutt E1 E2 OOM OOME R1 R2).
Proof using.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Horutt.
  - eapply orutt_cong_eutt; eauto.
    eapply orutt_cong_eutt2; eauto.
  - symmetry in Ht1, Ht2.
    eapply orutt_cong_eutt; eauto.
    eapply orutt_cong_eutt2; eauto.
Qed.

(* Bind closure and bind lemmas. *)

Section OruttBind.
Context {E1 E2 OOM : Type -> Type}.
Context `{OOME : OOM -< E2}.
Context {R1 R2 : Type}.
Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
Context (RR : R1 -> R2 -> Prop).

Inductive orutt_bind_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
  itree E1 R1 -> itree E2 R2 -> Prop :=
| rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: @orutt E1 E2 OOM OOME U1 U2 REv RAns RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : orutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors orutt_bind_clo: core.

Lemma orutt_clo_bind :
  orutt_bind_clo <3= gupaco2 (@orutt_ E1 E2 OOM OOME R1 R2 REv RAns RR) (euttge_trans_clo RR).
Proof using.
  intros rr. gcofix CIH. intros. destruct PR.
  gclo; econstructor; auto_ctrans_eq.
  1,2: rewrite unfold_bind; reflexivity.
  punfold EQV. unfold orutt_ in *.
  hinduction EQV before CIH; intros; pclearbot; cbn;
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
  - gclo. econstructor; auto_ctrans_eq.
    1,2: reflexivity.
    eauto with paco.
  - gstep. econstructor. eauto 7 with paco.
  - gstep. econstructor; eauto 7 with paco.
    intros. specialize (H0 a b H2). pclearbot. eauto 7 with paco.
  - gstep. econstructor; eauto 7 with paco.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
Qed.

End OruttBind.

Lemma orutt_bind {E1 E2 OOM OOME R1 R2 T1 T2}
      (REv: forall A B, E1 A -> E2 B -> Prop)
      (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
      (RR: R1 -> R2 -> Prop) (RT: T1 -> T2 -> Prop) t1 t2 k1 k2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2 ->
    (forall r1 r2,
      RR r1 r2 ->
      @orutt E1 E2 OOM OOME T1 T2 REv RAns RT (k1 r1) (k2 r2)) ->
    @orutt E1 E2 OOM OOME T1 T2 REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof using.
  intros. ginit.
  (* For some reason [guclo] fails, apparently trying to infer the type in a
     context with less information? *)
  eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H0. eauto.
Qed.


Section OruttMrec.
  Context (D1 D2 E1 E2 OOM : Type -> Type) `{OOME : OOM -< E2} (bodies1 : D1 ~> itree (D1 +' E1)) (bodies2 : D2 ~> itree (D2 +' E2)).
  Context (RPre : prerel E1 E2) (RPreInv : prerel D1 D2) (RPost : postrel E1 E2) (RPostInv : postrel D1 D2).

  Context (Hbodies : forall A B (d1 : D1 A) (d2 : D2 B),
              RPreInv A B d1 d2 ->
              @orutt (D1 +' E1) (D2 +' E2) OOM _ _ _ (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
            (fun (a : A) (b : B) => RPostInv A B d1 a d2 b) (bodies1 A d1) (bodies2 B d2) ).


  Lemma interp_mrec_orutt (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : forall  (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
      @orutt _ _ OOM _ _ _ (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost) RR t1 t2 ->
      @orutt _ _ OOM _ _ _ RPre RPost RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
  Proof using D1 D2 E1 E2 Hbodies OOM OOME RPost RPostInv RPre RPreInv bodies1 bodies2.
    ginit. gcofix CIH.
    intros t1 t2 Ht12. punfold Ht12. red in Ht12.
    remember (observe t1) as ot1. remember (observe t2) as ot2.
    hinduction Ht12 before r; intros.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      gstep. red. cbn. constructor. auto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn. gstep. constructor.
      pclearbot. gfinal. eauto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn.
      inv H.
      + subst_existT. gstep. constructor.
        gfinal. left. eapply CIH.
        eapply orutt_bind; eauto.
        intros. cbn in H. clear - H H0. specialize (H0 r1 r2 (sum_postrel_inl _ _ _ _ _ _ _ _ H)).
        pclearbot. auto.
      + subst_existT. subst. gstep. constructor.
        auto. intros. repeat rewrite tau_euttge. gfinal. left. eapply CIH.
        clear - H0 H. specialize (H0 a b (sum_postrel_inr _ _ _ _ _ _ _ _ H)).
        pclearbot. auto.
        intros o CONTRA.
        eapply H1.
        inv CONTRA.
        reflexivity.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn.
      gfinal. right.
      pstep. red.
      constructor.
    - apply simpobs in Heqot1. rewrite Heqot1. rewrite unfold_interp_mrec at 1. cbn.
      rewrite tau_euttge. auto.
    - apply simpobs in Heqot2. rewrite Heqot2. setoid_rewrite unfold_interp_mrec at 2.
      cbn. rewrite tau_euttge. auto.
  Qed.

  Lemma mrec_orutt (A B : Type) (d1 : D1 A) (d2 : D2 B) :
    RPreInv A B d1 d2 ->
    @orutt _ _ OOM _ _ _ RPre RPost (fun (a : A) (b : B) => RPostInv A B d1 a d2 b)
         (mrec bodies1 d1) (mrec bodies2 d2).
  Proof using D1 D2 E1 E2 Hbodies OOM OOME RPost RPostInv RPre RPreInv bodies1 bodies2.
    intros. apply interp_mrec_orutt. auto.
  Qed.

End OruttMrec.


Lemma rutt_orutt {E1 E2 OOM OOME R1 R2 REv RAns RR} (t1 : itree E1 R1) (t2 : itree E2 R2) :
  rutt REv RAns RR t1 t2 ->
  (forall A (e2 : E2 A), {forall o : OOM A, e2 <> subevent _ o} + {exists o : OOM A, e2 = subevent _ o}) ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2.
Proof using.
  intros Hrutt.
  revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt DEC_OOM.
  pstep. punfold Hrutt. red in Hrutt; red.
  hinduction Hrutt before CIH; subst; try solve [constructor; auto]; intros DEC_OOM.
  - specialize (CIH m1 m2).
    constructor. pclearbot.
    punfold H.
    red in H.
    right.
    apply CIH.
    pstep. red.
    auto.
    auto.
  - pose proof DEC_OOM as DEC_OOM'.
    specialize (DEC_OOM' _ e2).
    destruct DEC_OOM' as [NO_OOM | YES_OOM].
    { constructor; auto.
      { intros a b H1.
        specialize (H0 a b H1).
        pclearbot.
        right.
        apply CIH.
        auto.
        auto.
      }
    }
    { destruct YES_OOM as [o YES_OOM].
      inv YES_OOM.
      apply EqVisOOM.
    }
Qed.

Hint Resolve orutt_monot : paco.
Hint Constructors oruttF : itree.
Hint Unfold orutt_ : itree.
Hint Unfold orutt : itree.

Lemma orutt_weaken :
  forall {E1 E2 OOM} `{OOME : OOM -< E2} {R1 R2}
    (PRE1 PRE2 : prerel E1 E2)
    (POST1 POST2 : postrel E1 E2)
    (ResR1 ResR2 : R1 -> R2 -> Prop)
    t1 t2,
    orutt PRE1 POST1 ResR1 t1 t2 (OOM:=OOM) ->
    (forall {A B} e1 e2, (PRE1 A B e1 e2 -> PRE2 _ _ e1 e2)) ->
    (forall {A B} e1 r1 e2 r2, (POST2 A B e1 r1 e2 r2 -> POST1 _ _ e1 r1 e2 r2)) ->
    (forall r1 r2, (ResR1 r1 r2 -> ResR2 r1 r2)) ->
    orutt PRE2 POST2 ResR2 t1 t2 (OOM:=OOM).
Proof using.
  intros E1 E2 OOM OOME R1 R2 PRE1 PRE2 POST1 POST2 ResR1 ResR2.
  pcofix CIH. pstep. intros t1 t2 RUTT. punfold RUTT.
  red in RUTT |- *. induction RUTT; pclearbot; eauto 7 with paco itree.

  intros H2 H3 H4.
  apply OOMRutt.EqVis; auto.
  intros a b H5.
  apply H3 in H5.
  apply H0 in H5.
  pclearbot.
  eauto with paco itree.
Qed.

From Vellvm Require Import
  LLVMEvents
  Utils.Error.

(* TODO: generalize *)
Lemma orutt_raise :
  forall {E1 E2 OOM : Type -> Type} OOME {R1 R2 : Type} `{FAIL1 : FailureE -< E1} `{FAIL2 : FailureE -< E2}
    {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop}
    msg1 msg2,
    (forall msg (o : OOM _), @subevent FailureE E2 FAIL2 void (Throw msg) <> @subevent OOM E2 OOME void o) ->
    PRE void void (subevent void (Throw tt)) (subevent void (Throw tt)) ->
    orutt PRE POST R1R2 (LLVMEvents.raise msg1) (LLVMEvents.raise msg2) (OOM:=OOM) (OOME:=OOME).
Proof using.
  intros E1 E2 OOM OOME R1 R2 FAIL1 FAIL2 PRE POST R1R2 msg1 msg2 OOM_NOT_FAIL PRETHROW.
  unfold LLVMEvents.raise.
  repeat rewrite bind_trigger.
  apply orutt_Vis; auto.
  intros [] [] _.
Qed.

Lemma orutt_raiseOOM :
  forall {E1 E2 : Type -> Type} `{OOME2 : OOME -< E2} {R1 R2 : Type}
    {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop} t msg,
    orutt PRE POST R1R2 t (raiseOOM msg) (OOM:=OOME) (OOME:=OOME2).
Proof using.
  intros E1 E2 OOME2 R1 R2 PRE POST R1R2 t msg.
  unfold raiseOOM.
  rewrite bind_trigger.
  pfold. red.
  cbn.
  apply EqVisOOM.
Qed.

Lemma orutt_raise_oom :
  forall {E1 E2 : Type -> Type} `{OOME2 : OOME -< E2} {R1 R2 : Type}
    {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop} t msg,
    orutt PRE POST R1R2 t (raise_oom msg) (OOM:=OOME) (OOME:=OOME2).
Proof using.
  intros E1 E2 OOME R1 R2 PRE POST R1R2 t msg.
  cbn.
  apply orutt_raiseOOM.
Qed.

Lemma orutt_raiseUB :
  forall {E1 E2 OOM : Type -> Type} OOME {R1 R2 : Type} `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
    {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop}
    msg1 msg2,
    (forall msg (o : OOM _), @subevent UBE E2 UB2 void (ThrowUB msg) <> @subevent OOM E2 OOME void o) ->
    PRE void void (subevent void (ThrowUB tt)) (subevent void (ThrowUB tt)) ->
    orutt PRE POST R1R2 (raiseUB msg1) (raiseUB msg2) (OOM:=OOM) (OOME:=OOME).
Proof using.
  intros E1 E2 OOM OOME R1 R2 UB1 UB2 PRE POST R1R2 msg1 msg2 H H0.
  unfold raiseUB.
  repeat rewrite bind_trigger.
  apply orutt_Vis; auto.
  intros [] [] _.
Qed.

Ltac solve_orutt_raise :=
  apply orutt_raise; cbn; auto;
  intros msg o CONTRA;
  inv CONTRA.

Ltac solve_orutt_raiseUB :=
  apply orutt_raiseUB; cbn; auto;
  intros msg o CONTRA;
  inv CONTRA.

(* TODO: Move this to rutt library *)
Lemma orutt_iter' {OOME E1 E2 I1 I2 R1 R2} `{OOM: OOME -< E2}
  (RI : I1 -> I2 -> Prop)
  (RR : R1 -> R2 -> Prop)
  (pre : prerel E1 E2) (post : postrel E1 E2)
  (body1 : I1 -> itree E1 (I1 + R1))
  (body2 : I2 -> itree E2 (I2 + R2))
  (rutt_body
    : forall j1 j2, RI j1 j2 -> orutt pre post (sum_rel RI RR) (body1 j1) (body2 j2) (OOM:=OOME))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    orutt pre post RR (ITree.iter body1 i1) (ITree.iter body2 i2) (OOM:=OOME).
Proof.
  ginit. gcofix CIH. intros.
  specialize (rutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros ? ? [].
  - gstep.
    red; cbn.
    constructor.
    gbase.
    auto.
  - gstep.
    red.
    constructor.
    auto.
Qed.

(* TODO: Move this to orutt library *)
Lemma orutt_iter_gen :
  forall {OOME E1 E2 : Type -> Type} `{OOM: OOME -< E2} {A B1 B2 : Type} {R : relation A} {S : relationH B1 B2} (pre : prerel E1 E2) (post : postrel E1 E2),
  forall (x : A -> itree E1 (A + B1)) (y : A -> itree E2 (A + B2)),
    (forall x0 y0 : A, R x0 y0 -> orutt pre post (sum_rel R S) (x x0) (y y0) (OOM:=OOME)) ->
    forall x0 y0 : A, R x0 y0 -> orutt pre post S (CategoryOps.iter x x0) (CategoryOps.iter y y0) (OOM:=OOME).
Proof.
  intros OOME E1 E2 OOM A B1 B2 R S pre post body1 body2 EQ_BODY x y Hxy.
  eapply orutt_iter'; eauto.
Qed.
