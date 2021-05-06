From Coq Require Import
     Lia
     List
     NArith
     ZArith.

From Vellvm Require Import Syntax.

From tutorial Require Import Fin.

Require Import Vec Unique Combinators.

Open Scope nat_scope.
Open Scope vec_scope.

Arguments n_int : default implicits.
Arguments blocks : default implicits.


Definition unique_bid {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt,
  forall b1 b2,
  unique_vector (vi ++ vt)%vec ->
  List.In b1 (blocks ir vi vo vt) ->
  List.In b2 (blocks ir vi vo vt) ->
  blk_id b1 = blk_id b2 ->
  b1 = b2.

Theorem nth_firstn : forall A (l : list A) i n a,
  i < n -> List.nth i (firstn n l) a = List.nth i l a.
Proof.
  induction l ; intros.
  - rewrite firstn_nil. reflexivity.
  - induction n.
    + lia.
    + rewrite firstn_cons. simpl. induction i.
      * reflexivity.
      * rewrite IHl. reflexivity. lia.
Qed.

Definition out_blk_id id (b : block typ) : Prop :=
  match blk_term b with
  | TERM_Br_1 bid => id = bid
  | TERM_Br _ bid1 bid2 => id = bid1 \/ id = bid2
  | _ => False
  end.

Definition cvir_ids_WF {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt b,
  (
    List.In b (blocks ir vi vo vt) ->
    In (blk_id b) (vi ++ vt)%vec
  ) /\ (
    List.In b (blocks ir vi vo vt) ->
    forall bid,
    out_blk_id bid b ->
    In bid (vo ++ vt)%vec
  ).

Theorem block_cvir_id_WF : forall c, cvir_ids_WF (block_cvir c).
Proof.
  unfold cvir_ids_WF.
  intros ? [] [] [].
  split ; intros.
  - simpl in H.
    destruct H ; [| contradiction ].
    apply vector_in_app_iff.
    left.
    unfold In.
    subst.
    simpl.
    destruct x ; simpl in * ; [lia |].
    unfold Vec.hd. simpl. intuition.
  - unfold out_blk_id in H0.
    simpl in *.
    destruct H ; [| contradiction ].
    apply vector_in_app_iff.
    left.
    unfold In.
    subst.
    simpl in *.
    subst.
    destruct x0 ; simpl in * ; [lia |].
    unfold Vec.hd. simpl. intuition.
Qed.

Theorem unique_vector_reorder :
  forall A n1 n2 n3 n4 (v1 : Vec.t A n1) (v2 : Vec.t A n2) (v3 : Vec.t A n3) (v4 : Vec.t A n4),
  unique_vector ((v1 ++ v2) ++ v3 ++ v4) -> unique_vector ((v1 ++ v3) ++ v2 ++ v4).
Proof.
  intros.
  apply unique_list_vector. simpl.
  apply unique_list_vector in H. simpl in H.
  rewrite <- app_assoc in H.
  apply unique_list_sym2 in H.
  apply unique_list_sym2.
  rewrite <- app_assoc in H.
  rewrite <- app_assoc.
  assumption.
Qed.

Theorem merge_cvir_id_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_ids_WF ir1 -> cvir_ids_WF ir2 ->
  cvir_ids_WF (merge_cvir ir1 ir2).
Proof.
  unfold cvir_ids_WF.
  intros ? ? ? ? ? ? ? ? ? ? ? ?.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  Opaque Vec.splitat.
  simpl in *.
  rewrite 3 splitat_append.
  edestruct H, H0.
  rewrite vector_in_app_iff in H1, H3.
  split ; intros ; rewrite 3 vector_in_app_iff ; apply in_app_iff in H5.
  - destruct H5 ; apply H1 in H5 + apply H3 in H5 ; destruct H5 ; intuition.
  - destruct H5 ; eapply H2 in H5 + eapply H4 in H5.
    2, 4: eassumption.
    all: rewrite vector_in_app_iff in H5.
    all: intuition.
Qed.

Theorem merge_cvir_blocks :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2) vi1 vi2 vo1 vo2 vt1 vt2,
  blocks (merge_cvir ir1 ir2) (vi1++vi2) (vo1++vo2) (vt1++vt2) = (blocks ir1 vi1 vo1 vt1 ++ blocks ir2 vi2 vo2 vt2)%list.
Proof.
  intros.
  simpl.
  rewrite 3 splitat_append.
  reflexivity.
Qed.

Theorem merge_cvir_unique :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_ids_WF ir1 ->
  cvir_ids_WF ir2 ->
  unique_bid ir1 ->
  unique_bid ir2 ->
  unique_bid (merge_cvir ir1 ir2).
Proof.
  unfold unique_bid.
  intros.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  rewrite merge_cvir_blocks in H4, H5.
  rewrite in_app_iff in H4, H5.
  specialize (H1 vi1 vo1 vt1 b1 b2).
  specialize (H2 vi2 vo2 vt2 b1 b2).
  apply unique_vector_reorder in H3.
  destruct H4, H5.
  - apply unique_vector_app1 in H3.
    apply H1.
    all: assumption.
  - apply H in H4.
    apply H0 in H5.
    eapply In_nth in H4, H5.
    destruct H4 as [? ?], H5 as [? ?].
    erewrite <- vector_app_nth1 in H4.
    erewrite <- vector_app_nth2 in H5.
    rewrite <- H4 in H6.
    rewrite <- H5 in H6.
    specialize (H3 _ _ H6).
    destruct x, x0.
    simpl in H3.
    inversion H3.
    lia.
  - apply H0 in H4.
    apply H in H5.
    eapply In_nth in H4, H5.
    destruct H4 as [? ?], H5 as [? ?].
    erewrite <- vector_app_nth2 in H4.
    erewrite <- vector_app_nth1 in H5.
    rewrite <- H4 in H6.
    rewrite <- H5 in H6.
    specialize (H3 _ _ H6).
    destruct x, x0.
    simpl in H3.
    inversion H3.
    lia.
  - apply unique_vector_app2 in H3.
    eapply H2.
    all: assumption.
Qed.

Theorem seq_cvir_id_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 (S no1)) (ir2 : cvir (S ni2) no2),
  cvir_ids_WF ir1 -> cvir_ids_WF ir2 ->
  cvir_ids_WF (seq_cvir ir1 ir2).
Proof.
  unfold cvir_ids_WF.
  intros.
  split_vec vi ni1.
  split_vec vo no1.
  simpl in *.
  destruct (Vec.uncons vt) as [it vt'] eqn:?.
  apply cons_uncons in Heqp. subst.
  split_vec vt' (n_int ir1).
  rewrite 2 splitat_append.
  edestruct H, H0.
  split.
  - intro.
    apply in_app_iff in H5.
    rewrite 2 vector_in_app_iff.
    unfold In. simpl.
    destruct H5 ; apply H1 in H5 + apply H3 in H5 ; apply in_app_iff in H5 ; simpl in * ; intuition.
  - intros.
    rewrite 2 vector_in_app_iff.
    unfold In. simpl.
    apply in_app_iff in H5.
    destruct H5 ; eapply H2 in H5 + eapply H4 in H5; try eassumption ;
    apply vector_in_app_iff in H5 ; unfold In in H5 ; simpl in H5 ; intuition.
Qed.

  (*intros.
  unfold cvir_ids_WF.
  intros.
  Opaque merge_cvir.
  simpl.
  split.
  - assert (H1 := merge_cvir_id_WF _ _ _ _ ir1 ir2 H H0).
    unfold cvir_ids_WF in H1.
    destruct (Vec.uncons vt) as [it vt'] eqn:?.
    apply cons_uncons in Heqp. subst.
    assert (List.In b
  (blocks
     (merge_cvir
        (mk_cvir
           (fun (vi0 : Vec.t raw_id ni1) (vo0 : Vec.t raw_id no1) (vt0 : Vec.t raw_id (n_int ir1)) =>
            blocks ir1 vi0 (it :: vo0) vt0))
        (mk_cvir
           (fun (vi0 : Vec.t raw_id ni2) (vo0 : Vec.t raw_id no2) (vt0 : Vec.t raw_id (n_int ir2)) =>
            blocks ir2 (it :: vi0) vo0 vt0))) vi vo vt') -> In (blk_id b) (vi ++ vt')).
    apply merge_cvir_id_WF.
    admit. admit.
    intro.
    apply Coqlib.list_in_insert.
    specialize (H2 H3).
    assumption.*)

Theorem seq_cvir_unique :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 (S no1)) (ir2 : cvir (S ni2) no2),
  cvir_ids_WF ir1 ->
  cvir_ids_WF ir2 ->
  unique_bid ir1 ->
  unique_bid ir2 ->
  unique_bid (seq_cvir ir1 ir2).
Proof.
  intros.
  unfold seq_cvir.
  Opaque merge_cvir.
  simpl.
  unfold unique_bid in *.
  intros.
  split_vec vi ni1.
  split_vec vo no1.
  simpl in *.
  destruct (Vec.uncons vt) as [it vt'] eqn:?.
  apply cons_uncons in Heqp. subst.
  split_vec vt' (n_int ir1).
  eapply merge_cvir_unique. 6: eassumption. 6: eassumption. all: eauto.
Admitted.
