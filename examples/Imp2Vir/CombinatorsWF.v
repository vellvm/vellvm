From Coq Require Import
     Lia
     List
     NArith
     ZArith.

From Vellvm Require Import Syntax.

From tutorial Require Import Fin.

Require Import Vec Combinators.

Open Scope nat_scope.
Open Scope vec_scope.

Arguments n_int : default implicits.
Arguments blocks : default implicits.

Definition unique_vector {A} {n} (v : Vec.t A n) : Prop :=
  forall i1 i2, nth v i1 = nth v i2 -> i1 = i2.

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

Theorem unique_vector_app1 :
  forall A n1 n2 (v1 : Vec.t A n1) (v2 : Vec.t A n2), unique_vector (v1 ++ v2) -> unique_vector v1.
Proof.
  unfold unique_vector.
  intros.
  destruct v1, v2, i1, i2.
  apply unique_fin. simpl.
  eassert (H1 := H (fi' x1) (fi' x2)).
  Unshelve.
  2, 3: simpl; lia.
  erewrite 2 nth_destruct in H0. simpl in H0.
  eassert (fi' x1 = fi' x2).
  apply H1.
  erewrite 2 nth_destruct. simpl. rewrite 2 app_nth1 ; try lia. exact H0.
  inversion H2. reflexivity.
  Unshelve.
  all: induction x; [simpl in *; lia | auto].
Qed.

Theorem unique_vector_app2 :
  forall A n1 n2 (v1 : Vec.t A n1) (v2 : Vec.t A n2), unique_vector (v1 ++ v2) -> unique_vector v2.
Proof.
  unfold unique_vector.
  intros.
  destruct v1, v2, i1, i2.
  apply unique_fin. simpl.
  eassert (H1 := H (fi' (n1 + x1)) (fi' (n1 + x2))).
  Unshelve.
  2, 3: simpl; lia.
  erewrite 2 nth_destruct in H0. simpl in H0.
  eassert (fi' (n1 + x1) = fi' (n1 + x2)).
  apply H1.
  erewrite 2 nth_destruct. simpl. rewrite 2 app_nth2 ; try lia.
  replace (n1 + x1 - length x) with x1 by lia.
  replace (n1 + x2 - length x) with x2 by lia.
  exact H0.
  inversion H2. lia.
  Unshelve.
  all: induction x0; [simpl in *; lia | auto].
Qed.

Theorem unique_vector_reorder :
  forall A n1 n2 n3 n4 (v1 : Vec.t A n1) (v2 : Vec.t A n2) (v3 : Vec.t A n3) (v4 : Vec.t A n4), unique_vector ((v1 ++ v2) ++ v3 ++ v4) -> unique_vector ((v1 ++ v3) ++ v2 ++ v4).
Proof.
  unfold unique_vector.
  intros.
  destruct v1, v2, v3, v4, i1 as [i1 ?], i2 as [i2 ?].
  erewrite 2 nth_destruct in H0. simpl in H0.
  apply unique_fin. simpl.
  set (cast_idx := fun i1 =>
    if andb (n1 <=? i1) (i1 <? (n1 + n2)) then i1 + n3
    else if andb ((n1 + n2) <=? i1) (i1 <=? (n1 + n2 + n3)) then i1 - n2
    else i1
  ).
  set (i1' := cast_idx i1).
  set (i2' := cast_idx i2).
  subst cast_idx. simpl in i1', i2'.
  set (bound_idx := fun i1 =>
    i1 < n1 \/
    (i1 >= n1 /\ i1 < n1 + n2) \/
    (i1 >= n1 + n2 /\ i1 < n1 + n2 + n3) \/
    i1 >= n1 + n2 + n3).
  assert (H1 : bound_idx i1) by (unfold bound_idx in *; lia).
  assert (H2 : bound_idx i2) by (unfold bound_idx in *; lia).
  subst bound_idx. simpl in *.
  eassert (H' := H (fi' i1') (fi' i2')). destruct H'. subst i1' i2'.
  rewrite <- 3 Nat.leb_gt in H1, H2.
  unfold ge in *. rewrite <- 3 Nat.leb_le in H1, H2.
  intuition.
  simpl in *. unfold andb. simpl. rewrite * H3. rewrite * H1. simpl.
Admitted.

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
(*
    simpl in H3.
    replace x0 with (x0 + length (proj1_sig (vi1 ++ vt1)) - length (proj1_sig (vi1 ++ vt1))) in H8 by lia.
    erewrite <- app_nth2 in H8 ; [| lia].

    eapply List.In_nth in H4, H5.
    destruct H4, H5.
    destruct H4, H5.
    erewrite <- app_nth1 in H7 ; [| assumption].
    erewrite <- merge_cvir_blocks in H7.
    replace x0 with (x0 + length (blocks ir1 vi1 vo1 vt1) - length (blocks ir1 vi1 vo1 vt1)) in H8 by lia.
    erewrite <- app_nth2 in H8 ; [| lia].
    rewrite <- merge_cvir_blocks in H8.
    rewrite <- H8 in H6.
    rewrite <- H7 in H6.
    simpl in H6.

  unfold unique_vector.
  intros ? ? ? ? ? ? H8 H9 ? ? ? ? ? ? ? ? ? ? ?.
  assert (H10 := merge_cvir_id_WF _ _ _ _ ir1 ir2 H8 H9 vi vo vt b1).
  assert (H10' := merge_cvir_id_WF _ _ _ _ ir1 ir2 H8 H9 vi vo vt b2).
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  specialize (H8 vi1 vo1 vt1). assert (H8' := H8 b2). specialize (H8 b1).
  specialize (H9 vi2 vo2 vt2). assert (H9' := H9 b2). specialize (H9 b1).
  destruct H8 as [H8 _], H8' as [H8' _], H9 as [H9 _], H9' as [H9' _], H10 as [H10 _], H10' as [H10' _].
  simpl in *.
  rewrite vector_in_app_iff in H8, H8', H9, H9'.
  rewrite 3 splitat_append in H2, H3, H10, H10'.
  rewrite in_app_iff in H2, H3, H10, H10'.
  destruct H2, H3.
  - eapply H.
    2,3,4: eassumption.
    intros [] [] ?.
    apply Fin.unique_fin.
    erewrite 2 nth_destruct in H5.
    simpl in H5.
    assert (x < length (proj1_sig vi1) \/ x >= length (proj1_sig vi1)) by lia.
    assert (x0 < length (proj1_sig vi1) \/ x0 >= length (proj1_sig vi1)) by lia.
    destruct vi1 as [li1 ?], vi2 as [li2 ?], vo1 as [lo1 ?], vo2 as [lo2 ?], vt1 as [lt1 ?], vt2 as [lt2 ?].
    simpl in *.
    destruct H6, H7.
    all: rewrite app_nth1 in H5 + rewrite app_nth2 in H5 ; [| assumption].
    all: rewrite app_nth1 in H5 + rewrite app_nth2 in H5 ; [| assumption].
    all: epose (x' := fi' x) + epose (x' := fi' (ni2 + x));
      epose (x0' := fi' x0) + epose (x0' := fi' (ni2 + x0));
      specialize (H1 x' x0');
      erewrite 2 nth_destruct in H1;
      simpl in H1;
      rewrite app_nth1 in H1 + rewrite app_nth2 in H1; [| rewrite app_length ; lia ];
      rewrite (app_nth1 (_ ++ _)) in H1 + rewrite (app_nth2 (_ ++ _)) in H1; [| rewrite app_length ; lia ].
    all: try rewrite * app_length in H1.
    all: rewrite app_nth1 in H1 + rewrite app_nth2 in H1 ; [| lia].
    all: rewrite app_nth1 in H1 + rewrite app_nth2 in H1 ; [| lia].
    all: try replace (x - length li1) with (ni2 + x - (length li1 + length li2)) in H5 by lia.
    all: try replace (x0 - length li1) with (ni2 + x0 - (length li1 + length li2)) in H5 by lia.
    all: apply H1 in H5.
    all: injection H5 as ?.
    all: lia.
  - intuition.
    eapply In_nth in H10, H11.
    destruct H10, H11.
    rewrite <- H8 in H4.
    rewrite <- H10 in H4.
    apply H1 in H4.
    destruct x, x0.
    eapply List.In_nth in H2, H3.
    destruct H2 as [ ? [ ? ? ]], H3 as [ ? [ ? ? ]].
    inversion H4.
    subst.
    apply In_nth in H6, H7.
    destruct H6, H7.
Admitted.
*)

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
