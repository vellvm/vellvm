From Coq Require Import
     Lia
     List
     NArith
     ZArith.

From Vellvm Require Import Syntax.

From tutorial Require Import Fin.

Require Import Vec Unique CvirCombinators.

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
  i < n -> List.nth i (List.firstn n l) a = List.nth i l a.
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
  List.In b (blocks ir vi vo vt) ->
  (
    In (blk_id b) (vi ++ vt)%vec
  ) /\ (
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

Theorem block_cvir_unique : forall c, unique_bid (block_cvir c).
Proof.
  unfold unique_bid, block_cvir.
  simpl.
  intros.
  intuition.
  subst.
  reflexivity.
Qed.

Theorem branch_cvir_id_WF : forall c e, cvir_ids_WF (branch_cvir c e).
Proof.
  unfold cvir_ids_WF.
  intros ? ? [] [] [].
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
    destruct x0 ; simpl in * ; [lia |].
    unfold Vec.hd in *. simpl in *. intuition.
Qed.

Theorem branch_cvir_unique : forall c e, unique_bid (branch_cvir c e).
Proof.
  unfold unique_bid, block_cvir.
  simpl.
  intros.
  intuition.
  subst.
  reflexivity.
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
  intros ? ? ? ? ? ? ? ? ? ? ? ? ?.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  Opaque Vec.splitat.
  simpl in *.
  rewrite 3 splitat_append in H1.
  apply in_app_iff in H1.
  split ; intros ; rewrite 3 vector_in_app_iff.
  - destruct H1 ; apply H in H1 + apply H0 in H1 ;
    rewrite vector_in_app_iff in H1 ; intuition.
  - destruct H1 ; apply H in H1 + apply H0 in H1 ; apply H1 in H2 ;
    rewrite vector_in_app_iff in H2 ; intuition.
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
    destruct H4 as [? _], H5 as [? _].
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
    destruct H4 as [? _], H5 as [? _].
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

Theorem sym_i_cvir_id_WF :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_ids_WF ir -> cvir_ids_WF (sym_i_cvir ir).
Proof.
  unfold cvir_ids_WF. intros.
  unfold sym_i_cvir in H0.
  split_vec vi ni1.
  split_vec vi2 ni3.
  rename vi21 into vi2, vi22 into vi3.
  simpl in H0.
  rewrite sym_vec_app in H0.
  apply H in H0.
  unfold In in H0.
  simpl in H0.
  rewrite 3 in_app_iff in H0.
  rewrite 3 vector_in_app_iff.
  intuition.
Qed.

Theorem sym_i_cvir_unique :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  unique_bid ir ->
  unique_bid (sym_i_cvir ir).
Proof.
  unfold unique_bid.
  intros.
  split_vec vi ni1.
  split_vec vi2 ni3.
  rename vi21 into vi2, vi22 into vi3.
  eapply H. 4: apply H3. 3: apply H2. 2: apply H1.
  rewrite sym_vec_app.
  apply unique_list_vector. apply unique_list_vector in H0. simpl in *.
  rewrite <- app_assoc. rewrite <- app_assoc. apply unique_list_sym2.
  rewrite <- app_assoc. rewrite app_assoc. apply unique_list_sym2.
  rewrite <- app_assoc. rewrite <- 2 app_assoc in H0. exact H0.
Qed.

Theorem cast_i_cvir_id_WF :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_ids_WF ir -> cvir_ids_WF (cast_i_cvir ir H).
Proof.
  unfold cvir_ids_WF. intros.
  simpl in H1.
  destruct vi.
  simpl in H1.
  apply H0 in H1.
  apply H1.
Qed.

Theorem cast_o_cvir_id_WF :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  cvir_ids_WF ir -> cvir_ids_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_ids_WF. intros.
  simpl in H1.
  destruct vi.
  simpl in H1.
  apply H0 in H1.
  apply H1.
Qed.

Theorem cast_i_cvir_unique :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  unique_bid ir -> unique_bid (cast_i_cvir ir H).
Proof.
  unfold unique_bid. intros.
  destruct vi.
  simpl in *.
  eapply H0 ; try eassumption.
  apply unique_list_vector.
  apply unique_list_vector in H1.
  simpl in *.
  exact H1.
Qed.

Theorem cast_o_cvir_unique :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  unique_bid ir -> unique_bid (cast_o_cvir ir H).
Proof.
  unfold unique_bid. intros.
  simpl in *.
  eapply H0 ; try eassumption.
Qed.

Theorem focus_input_cvir_id_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_ids_WF ir -> cvir_ids_WF (focus_input_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_i_cvir_id_WF.
  apply sym_i_cvir_id_WF.
  apply cast_i_cvir_id_WF.
  apply sym_i_cvir_id_WF.
  apply cast_i_cvir_id_WF.
  exact H.
Qed.

Theorem focus_input_cvir_unique :
  forall ni no (ir : cvir ni no) (i : fin ni),
  unique_bid ir -> unique_bid (focus_input_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_i_cvir_unique.
  apply sym_i_cvir_unique.
  apply cast_i_cvir_unique.
  apply sym_i_cvir_unique.
  apply cast_i_cvir_unique.
  exact H.
Qed.

Theorem loop_cvir_open_id_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_ids_WF ir -> cvir_ids_WF (loop_cvir_open ir).
Proof.
  unfold loop_cvir_open.
  unfold cvir_ids_WF.
  intros.
  simpl in *.
  specialize (H vi (hd vi :: vo) vt b).
  intuition.
  specialize (H2 _ H1).
  apply in_app_iff in H2. simpl in H2. apply in_app_iff.
  intuition.
  subst.
Admitted.

Theorem loop_cvir_id_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_ids_WF ir -> cvir_ids_WF (loop_cvir ir).
Proof.
  unfold loop_cvir.
  unfold cvir_ids_WF.
  intros.
  simpl in *.
  destruct (uncons vt) eqn:? in H0.
  apply cons_uncons in Heqp. subst vt.
  specialize (H (r::vi) (r::vo) t b).
  apply H in H0.
  split.
  - destruct H0 as [H0 _].
    apply in_app_iff.
    apply in_app_iff in H0.
    simpl in *.
    tauto.
  - destruct H0 as [_ H0].
    intros. specialize (H0 bid H1).
    apply in_app_iff.
    apply in_app_iff in H0.
    simpl in *.
    tauto.
Qed.

Theorem loop_cvir_unique :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  unique_bid ir -> unique_bid (loop_cvir ir).
Proof.
  unfold loop_cvir, unique_bid.
  intros.
  simpl in *.
  destruct (uncons vt) eqn:? in H1, H2.
  apply cons_uncons in Heqp. subst vt.
  eapply H ; try eassumption.
  apply unique_list_vector. apply unique_list_vector in H0. simpl in *.
  replace (r :: proj1_sig t)%list with ((r :: nil) ++ proj1_sig t)%list in H0 by reflexivity.
  apply unique_list_sym in H0.
  rewrite <- app_assoc in H0.
  apply unique_list_sym2 in H0.
  apply H0.
Qed.

Theorem seq_cvir_id_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 (S no1)) (ir2 : cvir (S ni2) no2),
  cvir_ids_WF ir1 -> cvir_ids_WF ir2 ->
  cvir_ids_WF (seq_cvir ir1 ir2).
Proof.
  unfold seq_cvir.
  intros.
  apply loop_cvir_id_WF.
  apply cast_o_cvir_id_WF.
  apply cast_i_cvir_id_WF.
  apply focus_input_cvir_id_WF.
  apply merge_cvir_id_WF ; assumption.
Qed.

Theorem seq_cvir_unique :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 (S no1)) (ir2 : cvir (S ni2) no2),
  cvir_ids_WF ir1 -> cvir_ids_WF ir2 ->
  unique_bid ir1 -> unique_bid ir2 ->
  unique_bid (seq_cvir ir1 ir2).
Proof.
  unfold seq_cvir.
  intros.
  apply loop_cvir_unique.
  apply cast_o_cvir_unique.
  apply cast_i_cvir_unique.
  apply focus_input_cvir_unique.
  apply merge_cvir_unique ; assumption.
Qed.