From Coq Require Import
     Lia
     List
     NArith
     ZArith.

From Vellvm Require Import
     Syntax
     Syntax.ScopeTheory
     Utils.Tactics.

From Imp2Vir Require Import Fin.

From Imp2Vir Require Import Utils Vec Unique CvirCombinators Relabel.

Open Scope nat_scope.
Open Scope vec_scope.

Arguments n_int : default implicits.
Arguments blocks : default implicits.

(** There is 5 properties of WF:
 - unique block ID
 - cvir input IDs WF
 - cvir outputs IDs WF
 - cvir used inputs
 - relabeling (actually, it is in Semantic.v) *)

(** Well-Formness properties *)

(* If the union of inputs and internals has no duplicate, then there will be
no duplicates block_id in the ir. *)
Definition unique_bid {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt,
  forall b1 b2,
  unique_vector (vi ++ vt)%vec ->
  List.In b1 (blocks ir vi vo vt) ->
  List.In b2 (blocks ir vi vo vt) ->
  blk_id b1 = blk_id b2 ->
  b1 = b2.

(* id is an output of the block b if the terminator of b branches to id *)
Definition out_blk_id id (b : block typ) : Prop :=
  match blk_term b with
  | TERM_Br_1 bid => id = bid
  | TERM_Br _ bid1 bid2 => id = bid1 \/ id = bid2
  | _ => False
  end.

(* If a block belongs to a CVIR,
   its id must be in the inputs or the internals (input WF) *)
Definition cvir_input_ids_WF {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt b,
  List.In b (blocks ir vi vo vt) ->
  (In (blk_id b) (vi ++ vt)%vec). (* input WF *)

(* If a block belongs to a CVIR,
   all branchs must be to a block which id in one of the provided vector
   (output WF)
NOTE: for output WF, shouldn't it be in output+internals only ? *)
Definition cvir_output_ids_WF {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt b,
  List.In b (blocks ir vi vo vt) ->
  (forall bid, out_blk_id bid b -> In bid (vi ++ vo ++ vt)%vec).

Definition cvir_ids_WF {ni no} ir : Prop :=
  forall (vi : Vec.t raw_id ni) (vo : Vec.t raw_id no) vt b,
  List.In b (blocks ir vi vo vt) ->
  (In (blk_id b) (vi ++ vt)%vec) (* input WF *)
  /\
  (forall bid, out_blk_id bid b -> In bid (vi ++ vo ++ vt)%vec). (* output WF *)

Lemma cvir_combine_in_out_ids_WF : forall (ni no : nat) (ir : cvir ni no),
  cvir_input_ids_WF ir /\ cvir_output_ids_WF ir ->
  cvir_ids_WF ir.
Proof.
  unfold cvir_ids_WF. intros. intuition.
  - unfold cvir_input_ids_WF in H1; apply H1 in H0 ; assumption.
  - unfold cvir_output_ids_WF in H2; apply H2 with (bid:= bid) in H0 ; assumption.
Qed.



(* Each block id used in input or internals must be used as an input in the
returned CFG *)
Definition cvir_inputs_used {ni no} (ir : cvir ni no) : Prop :=
  forall vi vo vt bid,
  In bid (vi ++ vt) ->
  List.In bid (inputs (blocks ir vi vo vt)).

(* If the blocks function is called twice with different vectors of block ids,
the returned list of blocks will be identical modulo relabelling of the block
ids *)
Definition cvir_relabel_WF {ni no} (ir : cvir ni no) :=
  forall vi vi' vo vo' vt vt',
  unique_vector (vi ++ vo ++ vt) ->
  unique_vector (vi' ++ vo' ++ vt') ->
  blocks ir vi' vo' vt' =
  ocfg_relabel (vec_build_map (vi++vo++vt) (vi'++vo'++vt')) (blocks ir vi vo vt).

(* A CVIR is WF if it respects all the above WF properties *)
Definition cvir_WF {ni no} (ir : cvir ni no) :=
  unique_bid ir /\
  cvir_input_ids_WF ir /\
  cvir_output_ids_WF ir /\
  cvir_inputs_used ir /\
  cvir_relabel_WF ir.

(** ---- Proof of WF combinators ---- *)

(** Intermediate lemmas *)
(* block_cvir WF *)
Lemma block_cvir_input_id_WF : forall c, cvir_input_ids_WF (block_cvir c).
  unfold cvir_input_ids_WF.
  intros.
  simpl in H.
  destruct H ; [| contradiction ].
  apply vector_in_app_iff.
  left.
  unfold In.
  subst.
  simpl.
  destruct vi.
  destruct x ; simpl in * ; [lia |].
  unfold Vec.hd. simpl. intuition.
Qed.

Lemma block_cvir_output_id_WF : forall c, cvir_output_ids_WF (block_cvir c).
Proof.
  unfold cvir_output_ids_WF.
  intros.
  unfold out_blk_id in H0.
  simpl in *.
  destruct H ; [| contradiction ].
  apply vector_in_app_iff. right.
  apply vector_in_app_iff. left.
  unfold In.
  subst.
  simpl in *.
  subst.
  destruct vo.
  destruct x ; simpl in * ; [lia |].
  unfold Vec.hd. simpl. intuition.
Qed.

Lemma block_cvir_inputs_used : forall c, cvir_inputs_used (block_cvir c).
Proof.
  unfold cvir_inputs_used.
  intros.
  destruct_vec0 vt.
  now destruct_vec1 vi.
Qed.

Lemma block_cvir_unique : forall c, unique_bid (block_cvir c).
Proof.
  unfold unique_bid, block_cvir.
  simpl.
  intros.
  intuition.
  subst.
  reflexivity.
Qed.

Lemma block_cvir_relabel_WF : forall c, cvir_relabel_WF (block_cvir c).
Proof.
  unfold cvir_relabel_WF.
  intros.
  destruct_vec1 vi. destruct_vec1 vi'.
  destruct_vec1 vo. destruct_vec1 vo'.
  destruct_vec0 vt. destruct_vec0 vt'.
  cbn. unfold bk_relabel. f_equal. cbn.
  unfold blk_id_relabel. cbn.
  rewrite !Util.eq_dec_eq.
  f_equal.
  rewrite Util.eq_dec_neq; try trivial.
  intro. unfold unique_vector in H. apply unique_list_vector in H.
  specialize (H 1 0)%nat. simpl in H.
  assert (Some r1 = Some r) by (f_equal; assumption).
  apply H in H8; lia.
Qed.

(* branch_cvir WF *)

Lemma branch_cvir_input_id_WF : forall c e, cvir_input_ids_WF (branch_cvir c e).
Proof.
  unfold cvir_input_ids_WF.
  intros.
  simpl in H.
  destruct H ; [| contradiction ].
  apply vector_in_app_iff.
  left.
  unfold In.
  subst.
  simpl.
  destruct vi;
  destruct x ; simpl in * ; [lia |].
  unfold Vec.hd. simpl. intuition.
Qed.


Lemma branch_cvir_output_id_WF : forall c e, cvir_output_ids_WF (branch_cvir c e).
Proof.
  unfold cvir_output_ids_WF.
  intros.
  unfold out_blk_id in H0.
  simpl in *.
  destruct H ; [| contradiction ].
  apply vector_in_app_iff. right.
  apply vector_in_app_iff. left.
  unfold In.
  subst.
  simpl in *.
  subst.
  destruct vo;
  destruct x ; simpl in * ; [lia |].
  destruct x ; simpl in * ; [lia |].
  unfold Vec.hd in *. simpl in *. intuition.
Qed.

Lemma branch_cvir_unique : forall c e, unique_bid (branch_cvir c e).
Proof.
  unfold unique_bid, block_cvir.
  simpl.
  intros.
  intuition.
  subst.
  reflexivity.
Qed.

Lemma branch_cvir_inputs_used : forall c e, cvir_inputs_used (branch_cvir c e).
  unfold cvir_inputs_used.
  intros.
  destruct_vec0 vt.
  now destruct_vec1 vi.
Qed.

Lemma branch_cvir_relabel_WF : forall c e, cvir_relabel_WF (branch_cvir c e).
Proof.
  unfold cvir_relabel_WF.
  intros.
  destruct_vec1 vi. destruct_vec1 vi'.
  destruct_vec2 vo. destruct_vec2 vo'.
  destruct_vec0 vt. destruct_vec0 vt'.
  cbn. unfold bk_relabel. f_equal. cbn.
  unfold blk_id_relabel. cbn.
  rewrite !Util.eq_dec_eq.
  f_equal.
  rewrite !Util.eq_dec_neq. trivial.
  - intro. unfold unique_vector in H.
    apply unique_list_vector in H.
    specialize (H 1 2)%nat. simpl in H.
    assert (Some r1 = Some r2) by (f_equal; symmetry ; assumption).
    apply H in H8; lia.
  - intro. unfold unique_vector in H.
    apply unique_list_vector in H.
    specialize (H 2 0)%nat. simpl in H.
    assert (Some r2 = Some r) by (f_equal; assumption).
    apply H in H8; lia.
  - intro. unfold unique_vector in H. apply unique_list_vector in H.
    specialize (H 1 0)%nat. simpl in H.
    assert (Some r1 = Some r) by (f_equal; assumption).
    apply H in H8; lia.
Qed.


(* merge_cvir WF *)

Lemma merge_cvir_input_id_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_input_ids_WF ir1 -> cvir_input_ids_WF ir2 ->
  cvir_input_ids_WF (merge_cvir ir1 ir2).
Proof.
  unfold cvir_input_ids_WF.
  intros.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  Opaque Vec.splitat.
  simpl in *.
  rewrite 3 splitat_append in H1.
  apply in_app_iff in H1.
  rewrite 3 vector_in_app_iff.
  destruct H1 ; apply H in H1 + apply H0 in H1 ;
  rewrite vector_in_app_iff in H1 ; intuition.
Qed.


Lemma merge_cvir_output_id_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_output_ids_WF ir1 -> cvir_output_ids_WF ir2 ->
  cvir_output_ids_WF (merge_cvir ir1 ir2).
Proof.
  unfold cvir_output_ids_WF.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  Opaque Vec.splitat.
  simpl in *.
  rewrite 3 splitat_append in H1.
  apply in_app_iff in H1.
  rewrite 2 vector_in_app_iff.
  destruct H1 ;
  apply H with (bid:= bid) in H1 + apply H0 with (bid:= bid) in H1 ;
  auto ;
  rewrite !vector_in_app_iff ;
  rewrite !vector_in_app_iff in H1 ;
  intuition.
Qed.

Lemma merge_cvir_blocks :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2) vi1 vi2 vo1 vo2 vt1 vt2,
  blocks (merge_cvir ir1 ir2) (vi1++vi2) (vo1++vo2) (vt1++vt2) = (blocks ir1 vi1 vo1 vt1 ++ blocks ir2 vi2 vo2 vt2)%list.
Proof.
  intros.
  simpl.
  rewrite 3 splitat_append.
  reflexivity.
Qed.

Lemma merge_cvir_inputs_used :
  forall {ni1 no1 ni2 no2} (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_inputs_used ir1 -> cvir_inputs_used ir2 ->
  cvir_inputs_used (merge_cvir ir1 ir2).
Proof.
  unfold cvir_inputs_used.
  intros.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  rewrite merge_cvir_blocks.
  rewrite inputs_app.
  apply in_app_iff.
  do 2 setoid_rewrite vector_in_app_iff in H1.
  setoid_rewrite vector_in_app_iff in H.
  setoid_rewrite vector_in_app_iff in H0.
  intuition.
Qed.

Lemma merge_cvir_unique :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_input_ids_WF ir1 ->
  cvir_output_ids_WF ir1 ->
  cvir_input_ids_WF ir2 ->
  cvir_output_ids_WF ir2 ->
  unique_bid ir1 ->
  unique_bid ir2 ->
  unique_bid (merge_cvir ir1 ir2).
Proof.
  unfold unique_bid.
  intros ? ? ? ? ? ? H' H'' H0' H0'' H1 H2 vi vo vt b1 b2 H3 H4 H5 H6.
  assert (H : cvir_ids_WF ir1).
  { apply cvir_combine_in_out_ids_WF ; auto. }
  assert (H0: cvir_ids_WF ir2).
  { apply cvir_combine_in_out_ids_WF ; auto. }
  clear H'; clear H''; clear H0'; clear H0''.
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

Lemma merge_cvir_relabel_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_relabel_WF ir1 ->
  cvir_relabel_WF ir2 ->
  cvir_relabel_WF (merge_cvir ir1 ir2).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  split_vec vi ni1.
  split_vec vo no1.
  split_vec vt (n_int ir1).
  split_vec vi' ni1.
  split_vec vo' no1.
  split_vec vt' (n_int ir1).
  apply unique_vector_split6 in H1, H2. (* re-order automatically then split *)
  specialize (H vi1 vi'1 vo1 vo'1 vt1 vt'1 (proj1 H1) (proj1 H2)).
  specialize (H0 vi2 vi'2 vo2 vo'2 vt2 vt'2 (proj2 H1) (proj2 H2)).
  unfold ocfg_relabel.
  rewrite List.map_app.
  rewrite H, H0.
  set (m1 := (vec_build_map (vi1 ++ vo1 ++ vt1)%vec (vi'1 ++ vo'1 ++ vt'1)%vec)).
  set (m2 := (vec_build_map (vi2 ++ vo2 ++ vt2)%vec (vi'2 ++ vo'2 ++ vt'2)%vec)).
  fold (ocfg_relabel m (blocks ir1 vi1 vo1 vt1)).
  fold (ocfg_relabel m (blocks ir2 vi2 vo2 vt2)).
  f_equal.
  - subst m1 ; subst m.
    (* we would like a property establishing that if m maps ids which are not
      in the list block, we can ignore them and prune them away the map *)
    (* in other words, we can prune the irrelevant keys and we prove the the mapping
       is identical for the relevant keys *)
    admit.
  - subst m.
    admit.
Admitted.

(* sym_i and sym_o WF *)

Lemma sym_i_cvir_input_id_WF :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (sym_i_cvir ir).
Proof.
  unfold cvir_input_ids_WF. intros.
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
  rewrite 3 vector_in_app_iff. tauto.
Qed.


Lemma sym_i_cvir_output_id_WF :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (sym_i_cvir ir).
Proof.
  unfold cvir_output_ids_WF. intros.
  unfold sym_i_cvir in H0.
  split_vec vi ni1.
  split_vec vi2 ni3.
  rename vi21 into vi2, vi22 into vi3.
  simpl in H0.
  rewrite sym_vec_app in H0.
  apply H with (bid := bid) in H0.
  unfold In in H0.
  simpl in H0.
  rewrite 3 in_app_iff in H0.
  rewrite 3 vector_in_app_iff. tauto.
  intros. assumption.
Qed.


Lemma sym_i_cvir_id_WF :
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
  split; [ tauto |].
  intros. destruct H0 as [ _ H0 ]. apply H0 in H1.
  rewrite 4 in_app_iff in H1.
  rewrite 4 vector_in_app_iff.
  tauto.
Qed.


Lemma sym_o_cvir_input_id_WF :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (sym_o_cvir ir).
Proof.
  unfold cvir_input_ids_WF. intros.
  unfold sym_o_cvir in H0.
  split_vec vo no1.
  split_vec vo2 no3.
  rename vo21 into vo2, vo22 into vo3.
  simpl in H0.
  rewrite sym_vec_app in H0.
  apply H in H0.
  unfold In in H0.
  simpl in H0.
  rewrite in_app_iff in H0.
  rewrite vector_in_app_iff. tauto.
Qed.


Lemma sym_o_cvir_output_id_WF :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (sym_o_cvir ir).
Proof.
  unfold cvir_output_ids_WF. intros.
  unfold sym_o_cvir in H0.
  split_vec vo no1.
  split_vec vo2 no3.
  rename vo21 into vo2, vo22 into vo3.
  simpl in H0.
  rewrite sym_vec_app in H0.
  apply H with (bid := bid) in H0 ; auto.
  unfold In in H0.
  simpl in H0.
  rewrite !in_app_iff in H0.
  rewrite !vector_in_app_iff. intuition.
Qed.



Lemma sym_o_cvir_id_WF :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_ids_WF ir -> cvir_ids_WF (sym_o_cvir ir).
Proof.
  unfold cvir_ids_WF. intros.
  unfold sym_o_cvir in H0.
  split_vec vo no1.
  split_vec vo2 no3.
  rename vo21 into vo2, vo22 into vo3.
  simpl in H0.
  rewrite sym_vec_app in H0.
  apply H in H0.
  unfold In in H0.
  simpl in H0.
  split; [ tauto |].
  intros. destruct H0 as [ _ H0 ]. apply H0 in H1.
  rewrite 4 in_app_iff in H1.
  rewrite 4 vector_in_app_iff.
  tauto.
Qed.

Lemma sym_i_cvir_inputs_used :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_inputs_used ir ->
  cvir_inputs_used (sym_i_cvir ir).
Proof.
  unfold cvir_inputs_used.
  intros.
  simpl.
  apply H.
  rewrite vector_in_app_iff in H0.
  rewrite vector_in_app_iff.
  rewrite <- sym_vec_In.
  assumption.
Qed.

Lemma sym_o_cvir_inputs_used :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_inputs_used ir ->
  cvir_inputs_used (sym_o_cvir ir).
Proof.
  unfold cvir_inputs_used.
  intros.
  now apply H.
Qed.

Lemma sym_i_cvir_unique :
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

Lemma sym_o_cvir_unique :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  unique_bid ir ->
  unique_bid (sym_o_cvir ir).
Proof.
  unfold sym_o_cvir, unique_bid.
  intros.
  simpl in *.
  eapply H ; eassumption.
Qed.

Lemma sym_i_cvir_relabel_WF :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (sym_i_cvir ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  split_vec vi ni1.
  split_vec vi' ni1.
  split_vec vi2 ni3.
  split_vec vi'2 ni3.
  rewrite !sym_vec_app in *.
  specialize (H (vi1++vi22++vi21) (vi'1++vi'22++vi'21) vo vo' vt vt' ).
  assert (H0' : unique_vector ((vi1++vi22++vi21) ++ vo ++ vt)).
  {
  clear H; clear H1; clear m ;
  rewrite !unique_vector_assoc in H0;
  apply unique_vector_sym in H0;
  apply unique_vector_sym2 in H0;
  rewrite unique_vector_assoc in H0;
  rewrite unique_vector_assoc in H0;
  apply unique_vector_sym2 in H0;
  rewrite <- !unique_vector_assoc in H0;
  apply unique_vector_sym in H0;
  rewrite <- unique_vector_assoc in H0;
  apply unique_vector_sym in H0;
  rewrite <- unique_vector_assoc in H0;
  apply unique_vector_sym2 in H0;
  assumption.
  }
  assert (H1' : unique_vector ((vi'1++vi'22++vi'21) ++ vo' ++ vt')).
  {
  clear H; clear H0 ; clear H0' ; clear m ;
  rewrite !unique_vector_assoc in H1 ;
  apply unique_vector_sym in H1;
  apply unique_vector_sym2 in H1;
  rewrite unique_vector_assoc in H1;
  rewrite unique_vector_assoc in H1;
  apply unique_vector_sym2 in H1;
  rewrite <- !unique_vector_assoc in H1;
  apply unique_vector_sym in H1;
  rewrite <- unique_vector_assoc in H1;
  apply unique_vector_sym in H1;
  rewrite <- unique_vector_assoc in H1;
  apply unique_vector_sym2 in H1;
  assumption.
  }
  apply H in H0' ; auto.
  set (m' := (vec_build_map ((vi1 ++ vi22 ++ vi21) ++ vo ++ vt) ((vi'1 ++ vi'22 ++ vi'21) ++ vo' ++ vt'))).
  rewrite ocfg_relabel_equivalent with (m:= m) (m':= m').
  assumption.
  clear.
  subst m; subst m' ; intros.
  unfold map_equivalent.
  split ; intros ; (
  apply find_vec_build_map_comm in H; (* comm and comm2 are still unproved *)
  apply find_vec_build_map_assoc in H;
  apply find_vec_build_map_assoc in H;
  apply find_vec_build_map_comm in H;
  apply find_vec_build_map_comm2 in H;
  apply find_vec_build_map_assoc in H;
  apply find_vec_build_map_assoc in H;
  apply find_vec_build_map_comm in H;
  apply find_vec_build_map_assoc in H;
  assumption). (* ugly... *)
Qed.


Lemma sym_o_cvir_relabel_WF :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (sym_o_cvir ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  split_vec vo no1.
  split_vec vo' no1.
  split_vec vo2 no3.
  split_vec vo'2 no3.
  rewrite !sym_vec_app in *.
  specialize (H vi vi' (vo1++vo22++vo21) (vo'1++vo'22++vo'21) vt vt' ).
  assert (H0' : unique_vector (vi ++ (vo1++vo22++vo21) ++ vt)).
  { admit. } (* do it automatically *)
  assert (H1' : unique_vector (vi' ++ (vo'1++vo'22++vo'21) ++ vt')).
  { admit. } (* do it automatically *)
  apply H in H0' ; auto.
  (* subst m. *)
  set (m' := (vec_build_map (vi ++ (vo1 ++ vo22 ++ vo21) ++ vt) (vi' ++ (vo'1 ++ vo'22 ++ vo'21)++ vt'))).
  rewrite ocfg_relabel_equivalent with (m:= m) (m':= m').
  assumption.
  clear.
  subst m; subst m' ; intros.
  unfold map_equivalent.
  split ; intros.
  - admit. (* do it automatically *)
  - admit. (* do it automatically *)
Admitted.


(* cast_i and cast_o WF *)

Lemma cast_i_cvir_id_WF :
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


Lemma cast_i_cvir_input_id_WF :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (cast_i_cvir ir H).
Proof.
  unfold cvir_input_ids_WF. intros.
  cbn in H1.
  destruct vi.
  apply H0 in H1.
  apply H1.
Qed.

Lemma cast_i_cvir_output_id_WF :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (cast_i_cvir ir H).
Proof.
  unfold cvir_output_ids_WF. intros.
  cbn in H1.
  destruct vi.
  eapply H0 in H1 ; eauto.
Qed.


Lemma cast_o_cvir_id_WF :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  cvir_ids_WF ir -> cvir_ids_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_ids_WF. intros.
  simpl in H1.
  apply H0 in H1.
  apply H1.
Qed.

Lemma cast_o_cvir_input_id_WF :
  forall no no' ni (ir : cvir ni no) (H : no = no'),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_input_ids_WF. intros.
  cbn in H1.
  apply H0 in H1.
  apply H1.
Qed.

Lemma cast_o_cvir_output_id_WF :
  forall no no' ni (ir : cvir ni no) (H : no = no'),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_output_ids_WF. intros.
  cbn in H1.
  eapply H0 in H1 ; eauto.
Qed.


Lemma cast_i_cvir_inputs_used :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_inputs_used ir ->
  cvir_inputs_used (cast_i_cvir ir H).
Proof.
  unfold cvir_inputs_used.
  intros.
  destruct vi.
  apply H0.
  apply H1.
Qed.

Lemma cast_o_cvir_inputs_used :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  cvir_inputs_used ir ->
  cvir_inputs_used (cast_o_cvir ir H).
Proof.
  unfold cvir_inputs_used.
  intros.
  now apply H0.
Qed.

Lemma cast_i_cvir_unique :
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

Lemma cast_o_cvir_unique :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  unique_bid ir -> unique_bid (cast_o_cvir ir H).
Proof.
  unfold unique_bid. intros.
  simpl in *.
  eapply H0 ; try eassumption.
Qed.

Lemma cast_i_cvir_relabel_WF :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (cast_i_cvir ir H).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  erewrite ocfg_relabel_equivalent.
  apply H0.
  - destruct vi as [li Hli'].
    rewrite (cast_vec raw_id ni' ni li Hli' (eq_sym H)).
    rewrite H.
    apply H1.
  - destruct vi' as [li' Hli'].
    rewrite (cast_vec raw_id ni' ni li' Hli' (eq_sym H)).
    rewrite H.
    apply H2.
  - reflexivity.
Qed.


Lemma cast_o_cvir_relabel_WF :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  erewrite ocfg_relabel_equivalent.
  apply H0.
  - destruct vo as [lo Hlo'].
    rewrite (cast_vec raw_id no' no lo Hlo' (eq_sym H)).
    rewrite H.
    apply H1.
  - destruct vo' as [lo' Hlo'].
    rewrite (cast_vec raw_id no' no lo' Hlo' (eq_sym H)).
    rewrite H.
    apply H2.
  - reflexivity.
Qed.


(* focus_input WF *)

Lemma focus_input_cvir_id_WF :
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

Lemma focus_input_cvir_inputs_used :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_inputs_used ir -> cvir_inputs_used (focus_input_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_i_cvir_inputs_used.
  apply sym_i_cvir_inputs_used.
  apply cast_i_cvir_inputs_used.
  apply sym_i_cvir_inputs_used.
  apply cast_i_cvir_inputs_used.
  exact H.
Qed.

Lemma focus_input_cvir_unique :
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

Lemma focus_input_cvir_relabel_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (focus_input_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_i_cvir_relabel_WF.
  apply sym_i_cvir_relabel_WF.
  apply cast_i_cvir_relabel_WF.
  apply sym_i_cvir_relabel_WF.
  apply cast_i_cvir_relabel_WF.
  assumption.
Qed.


(* swap_i_input_n WF *)

Lemma swap_i_cvir_id_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_ids_WF ir -> cvir_ids_WF (swap_i_input_cvir i ir).
Proof.
  unfold cvir_ids_WF.
  unfold swap_i_input_cvir.
  intros.
  apply H in H0.
  clear H.
  destruct H0 as [ H1 H2 ].
  destruct vi ; subst.
  destruct vt ; subst.
  cbn in *.
  rewrite in_app_iff in H1.
  split.
  - clear H2.
    rewrite in_app_iff.
    destruct H1 as [ H1 | H2 ] ; auto.
    left.
    apply swap_vec_In in H1.
    apply cast_In in H1. auto.
  - intros. apply H2 in H.
    rewrite in_app_iff.
    rewrite in_app_iff in H.
    destruct H1 as [ H3 | H4 ] ; auto ;
    ( destruct H ; auto ;
    apply swap_vec_In in H ;
    apply cast_In in H ;auto).
Qed.

Lemma swap_i_cvir_input_id_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (swap_i_input_cvir i ir).
Proof.
  unfold cvir_input_ids_WF.
  unfold swap_i_input_cvir.
  intros.
  apply H in H0.
  clear H.
  destruct vi ; subst; cbn in *.
  destruct vt ; subst; cbn in *.
  rewrite ?in_app_iff in *.
  destruct H0 as [ H1 | H2 ] ; auto.
  apply swap_vec_In in H1.
  apply cast_In in H1. auto.
 Qed.

Lemma swap_i_cvir_output_id_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (swap_i_input_cvir i ir).
Proof.
  unfold cvir_output_ids_WF.
  unfold swap_i_input_cvir.
  intros.
  cbn in *.
  apply H with (bid:= bid) in H0 ; auto.
  destruct vi ; subst.
  destruct vt ; subst.
  cbn in *.
  rewrite ?in_app_iff in *.
  destruct H0 as [ H3 | H4 ] ; auto.
  apply swap_vec_In in H3 ;
  apply cast_In in H3 ; auto.
 Qed.

Lemma swap_i_cvir_inputs_used :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_inputs_used ir -> cvir_inputs_used (swap_i_input_cvir i ir).
Proof.
  unfold swap_i_input_cvir, cvir_inputs_used.
  intros.
  simpl in *.
  apply H.
  rewrite vector_in_app_iff.
  rewrite vector_in_app_iff in H0.
  destruct H0 ; auto.
  left. rewrite swap_i_In in H0.
  eapply H0.
Qed.

Lemma swap_i_cvir_unique :
  forall ni no (ir : cvir ni no) (i : fin ni),
  unique_bid ir ->
  unique_bid (swap_i_input_cvir i ir).
Proof.
  unfold swap_i_input_cvir, unique_bid.
  intros ; simpl in *.
  apply H with (vi := (swap_i i vi)) (vo := vo) (vt := vt) ; auto.
  clear -H0.
  (* should i defined a relation between unique_vector ? *)
Admitted.


Lemma swap_i_cvir_relabel_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_relabel_WF ir -> cvir_relabel_WF (swap_i_input_cvir i ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
Admitted.

(* focus_output WF *)

Lemma focus_output_cvir_id_WF :
  forall ni no (ir : cvir ni no) (i : fin no),
  cvir_ids_WF ir -> cvir_ids_WF (focus_output_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_o_cvir_id_WF.
  apply sym_o_cvir_id_WF.
  apply cast_o_cvir_id_WF.
  apply sym_o_cvir_id_WF.
  apply cast_o_cvir_id_WF.
  exact H.
Qed.

Lemma focus_output_cvir_inputs_used :
  forall ni no (ir : cvir ni no) (o : fin no),
  cvir_inputs_used ir -> cvir_inputs_used (focus_output_cvir ir o).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_o_cvir_inputs_used.
  apply sym_o_cvir_inputs_used.
  apply cast_o_cvir_inputs_used.
  apply sym_o_cvir_inputs_used.
  apply cast_o_cvir_inputs_used.
  exact H.
Qed.

Lemma focus_output_cvir_unique :
  forall ni no (ir : cvir ni no) (i : fin no),
  unique_bid ir -> unique_bid (focus_output_cvir ir i).
Proof.
  unfold focus_output_cvir.
  intros.
  apply cast_o_cvir_unique.
  apply sym_o_cvir_unique.
  apply cast_o_cvir_unique.
  apply sym_o_cvir_unique.
  apply cast_o_cvir_unique.
  exact H.
Qed.

Lemma focus_output_cvir_relabel_WF :
  forall ni no (ir : cvir ni no) (i : fin no),
  cvir_relabel_WF ir -> cvir_relabel_WF (focus_output_cvir ir i).
 Proof.
  unfold focus_output_cvir.
  intros.
  apply cast_o_cvir_relabel_WF;
  apply sym_o_cvir_relabel_WF;
  apply cast_o_cvir_relabel_WF;
  apply sym_o_cvir_relabel_WF;
  apply cast_o_cvir_relabel_WF;
  assumption.
Qed.


(* loop_cvir_open WF *)

Lemma loop_open_cvir_id_WF :
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
  apply in_app_iff in H2. simpl in H2. rewrite in_app_iff in H2.
  apply vector_in_app_iff. rewrite vector_in_app_iff.
  intuition.
  left. subst bid. apply In_hd.
Qed.

Lemma loop_open_cvir_input_id_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (loop_cvir_open ir).
Proof.
  unfold loop_cvir_open.
  unfold cvir_input_ids_WF.
  intros.
  simpl in *.
  specialize (H vi (hd vi :: vo) vt b).
  intuition.
Qed.

Lemma loop_open_cvir_output_id_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (loop_cvir_open ir).
Proof.
  unfold loop_cvir_open.
  unfold cvir_output_ids_WF.
  intros.
  simpl in *.
  specialize (H vi (hd vi :: vo) vt b).
  intuition.
  specialize (H2 _ H1).
  apply in_app_iff in H2. simpl in H2. rewrite in_app_iff in H2.
  apply vector_in_app_iff. rewrite vector_in_app_iff.
  intuition.
  left. subst bid. apply In_hd.
Qed.

Lemma loop_open_cvir_inputs_used :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_inputs_used ir -> cvir_inputs_used (loop_cvir_open ir).
Proof.
  unfold loop_cvir_open, cvir_inputs_used.
  intros.
  simpl in *.
  now apply H.
Qed.

Lemma loop_open_cvir_unique :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  unique_bid ir -> unique_bid (loop_cvir_open ir).
Proof.
  unfold loop_cvir_open, unique_bid.
  intros.
  simpl in *.
  eapply H with (vo := (hd vi :: vo)) ; try eassumption.
Qed.


Lemma loop_open_cvir_relabel_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (loop_cvir_open ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  split_vec vi 1 ; split_vec vi' 1.
  set (m' :=
         (vec_build_map
          ((vi1 ++ vi2) ++ (hd (vi1 ++ vi2) :: vo) ++ vt)
          ((vi'1 ++ vi'2) ++ (hd (vi'1 ++ vi'2) :: vo') ++ vt'))).
  rewrite ocfg_relabel_equivalent with (m' := m').
  shelve.

  (* First, prove that m and m' are equivalent *)
  unfold map_equivalent.
  cbn. intros.
  rewrite (hd_app vi1 vi2), (hd_app vi'1 vi'2).
  rewrite app_comm_cons.
  rewrite !combine_app ;
  try ( rewrite !vector_length ; auto) ;
  try ( simpl ; rewrite !app_length ; rewrite !vector_length ; auto).
  rewrite app_comm_cons.
  rewrite (combine_app (hd vi1 :: proj1_sig vo) (proj1_sig vt)
                       (hd vi'1 :: proj1_sig vo') (proj1_sig vt'))
  ; try (rewrite !vector_length)
  ; try (simpl ; rewrite !vector_length)
  ; auto .
  rewrite combine_cons.
  rewrite <- !app_assoc.

  assert (
  map_equivalent
  (combine (proj1_sig vi1) (proj1_sig vi'1) ++
  combine (proj1_sig vi2) (proj1_sig vi'2) ++
  combine (hd vi1 :: nil) (hd vi'1 :: nil) ++
  combine (proj1_sig vo) (proj1_sig vo') ++
  combine (proj1_sig vt) (proj1_sig vt'))%list
  (combine (hd vi1 :: nil) (hd vi'1 :: nil) ++
  combine (proj1_sig vi1) (proj1_sig vi'1) ++
  combine (proj1_sig vi2) (proj1_sig vi'2) ++
  combine (proj1_sig vo) (proj1_sig vo') ++
  combine (proj1_sig vt) (proj1_sig vt'))%list).
  {admit. } (* do it automatically using commutativity and assoc... *)
  unfold map_equivalent in H2 ; rewrite H2 ; clear H2.
  set (m0 := (combine (proj1_sig vi2) (proj1_sig vi'2) ++
                    combine (proj1_sig vo) (proj1_sig vo') ++
                    combine (proj1_sig vt) (proj1_sig vt'))%list).
  rewrite List.app_assoc.
  apply map_equivalent_app ; try (reflexivity).
  clear.
  simpl.
  unfold map_equivalent.
  intros.
  admit.
  (*
       prove that
       combine [hd vi1] [hd vi2] ++ (combine (proj1_sig vi1) (proj1_sig vi'1))
       ~=
       (combine (proj1_sig vi1) (proj1_sig vi'1))
   *)

  Unshelve.
  apply H ; auto.
  (* Here, unique_vector is clearly false... find another way to prove
     the lemma *)
Admitted.

(* loop_cvir WF *)

Lemma loop_cvir_input_id_WF :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  cvir_input_ids_WF ir -> cvir_input_ids_WF (loop_cvir n ir).
Proof.
  unfold loop_cvir.
  unfold cvir_input_ids_WF.
  intros.
  split_vec vt n.
  cbn in *.
  apply H in H0.
  destruct vi ; subst ; cbn in *.
  destruct vo ; subst ; cbn in *.
  destruct vt1 ; subst ; cbn in *.
  destruct vt2 ; subst ; cbn in *.
  rewrite !in_app_iff.
  rewrite !in_app_iff in H0.
  rewrite firstn_app in H0 ; cbn in *.
  rewrite skipn_app in H0 ; cbn in *.
  rewrite firstn_all in H0 ; cbn in *.
  rewrite skipn_all in H0 ; cbn in *.
  assert (length x1 - length x1 = 0).
  { lia. }
  rewrite H1 in H0. clear H1.
  rewrite firstn_O in H0.
  rewrite skipn_O in H0.
  rewrite app_nil_r in H0.
  intuition.
Qed.

Lemma loop_cvir_output_id_WF :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  cvir_output_ids_WF ir -> cvir_output_ids_WF (loop_cvir n ir).
Proof.
  unfold loop_cvir.
  unfold cvir_output_ids_WF.
  intros.
  split_vec vt n.
  cbn in *.
  apply H with (vi:= vt1++vi) (vo:=vt1++vo) (vt:=vt2) in H1.
  - destruct vi ; subst ; cbn in *.
    destruct vo ; subst ; cbn in *.
    destruct vt1 ; subst ; cbn in *.
    destruct vt2 ; subst ; cbn in *.
    rewrite !in_app_iff.
    rewrite !in_app_iff in H1.
    intuition.
  - destruct vi ; subst ; cbn in *.
    destruct vo ; subst ; cbn in *.
    destruct vt1 ; subst ; cbn in *.
    destruct vt2 ; subst ; cbn in *.
    rewrite splitat_append in H0.
    assumption.
Qed.


Lemma loop_cvir_inputs_used :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  cvir_inputs_used ir -> cvir_inputs_used (loop_cvir n ir).
Proof.
  unfold loop_cvir.
  unfold cvir_inputs_used.
  intros.
  split_vec vt n.
  simpl in *.
  destruct (splitat n (vt1 ++ vt2)) eqn:E.
  rewrite splitat_append in E.
  apply H. inv E.
  (* In up_to assoc/comm... easy but TODO automatically *)
Admitted.

Lemma loop_cvir_unique :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  unique_bid ir -> unique_bid (loop_cvir n ir).
Proof.
  unfold loop_cvir, unique_bid.
  intros.
  cbn in *.
  split_vec vt n.
  apply H with (vi:= vt1++vi) (vo:=vt1++vo) (vt:=vt2) ; auto.
  apply unique_vector_sym2 in H0.
  apply unique_vector_assoc in H0.
  apply unique_vector_sym in H0.
  apply unique_vector_assoc in H0.
  assumption.
 Qed.

Lemma loop_cvir_relabel_WF :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  cvir_relabel_WF ir -> cvir_relabel_WF (loop_cvir n ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  simpl in *.
  split_vec vt n ; split_vec vt' n.
  set (m' := (vec_build_map
              ((vt1 ++ vi) ++ (vt1 ++ vo) ++ vt2)
              ((vt'1 ++ vi') ++ (vt'1 ++ vo') ++ vt'2))).
  rewrite ocfg_relabel_equivalent with (m' := m').
  apply H.
  (* here, unique_vector is clearly not unique... find another way to
prove the lemma *)
Admitted.

(* join_cvir WF *)

Lemma join_cvir_input_id_WF :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_input_ids_WF ir ->
  cvir_input_ids_WF (join_cvir ir).
Proof.
  unfold join_cvir, cvir_input_ids_WF.
  intros.
  simpl in *.
  apply H in H0. tauto.
Qed.

Lemma join_cvir_output_id_WF :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_output_ids_WF ir ->
  cvir_output_ids_WF (join_cvir ir).
Proof.
  unfold join_cvir, cvir_output_ids_WF.
  intros.
  simpl in *.
  apply H with (bid:= bid) in H0 ; auto.
  apply in_app_iff in H0. simpl in H0. rewrite in_app_iff in H0.
  apply vector_in_app_iff. rewrite (vector_in_app_iff _ _ _ vo vt).
  intuition. subst. right. left. apply In_hd.
Qed.

Lemma join_cvir_id_WF :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_ids_WF ir ->
  cvir_ids_WF (join_cvir ir).
Proof.
  unfold join_cvir, cvir_ids_WF.
  intros.
  simpl in *.
  apply H in H0.
  split ; [ tauto |].
  intros.
  apply H0 in H1.
  apply in_app_iff in H1. simpl in H1. rewrite in_app_iff in H1.
  apply vector_in_app_iff. rewrite (vector_in_app_iff _ _ _ vo vt).
  intuition.
  subst bid.
  right. left. apply In_hd.
Qed.


Lemma join_cvir_inputs_used :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_inputs_used ir ->
  cvir_inputs_used (join_cvir ir).
Proof.
  unfold join_cvir, cvir_inputs_used.
  intros.
  simpl in *.
  now apply H.
Qed.

Lemma join_cvir_unique :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  unique_bid ir ->
  unique_bid (join_cvir ir).
Proof.
  unfold join_cvir, unique_bid.
  intros.
  simpl in *.
  eapply H ; eassumption.
Qed.

Lemma join_cvir_relabel_WF :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_relabel_WF ir ->
  cvir_relabel_WF (join_cvir ir).
Proof.
  unfold cvir_relabel_WF.
  intros.
  set (m := vec_build_map (vi++vo++vt) (vi'++vo'++vt')).
  split_vec vo 1; split_vec vo' 1.
  simpl.
  erewrite ocfg_relabel_equivalent.
  eapply H.
  (* Here again, unique_vector is clearly not true... *)
Admitted.



(** ----- Theorem WF combinators ---- *)

Theorem block_cvir_WF :
  forall c, cvir_WF (block_cvir c).
Proof.
  unfold cvir_WF. intros c.
  split. now apply block_cvir_unique.
  split. now apply block_cvir_input_id_WF.
  split. now apply block_cvir_output_id_WF.
  split. now apply block_cvir_inputs_used.
  now apply block_cvir_relabel_WF.
Qed.

Theorem branch_cvir_WF : forall c e, cvir_WF (branch_cvir c e).
Proof.
  unfold cvir_WF. intros c e.
  split. now apply branch_cvir_unique.
  split. now apply branch_cvir_input_id_WF.
  split. now apply branch_cvir_output_id_WF.
  split. now apply branch_cvir_inputs_used.
  now apply branch_cvir_relabel_WF.
Qed.

Theorem sym_i_cvir_WF :
  forall ni1 ni2 ni3 no (ir : cvir (ni1+(ni2+ni3)) no),
  cvir_WF ir -> cvir_WF (sym_i_cvir ir).
Proof.
  unfold cvir_WF ; intros ni1 ni2 ni3 no ir [? [? [? [? ?]]]].
  split. now apply sym_i_cvir_unique.
  split. now apply sym_i_cvir_input_id_WF.
  split. now apply sym_i_cvir_output_id_WF.
  split. now apply sym_i_cvir_inputs_used.
  now apply sym_i_cvir_relabel_WF.
Qed.

Theorem sym_o_cvir_WF :
  forall ni no1 no2 no3 (ir : cvir ni (no1+(no2+no3))),
  cvir_WF ir -> cvir_WF (sym_o_cvir ir).
Proof.
  unfold cvir_WF ; intros ni no1 no2 no3 ir [? [? [? [? ?]]]].
  split. now apply sym_o_cvir_unique.
  split. now apply sym_o_cvir_input_id_WF.
  split. now apply sym_o_cvir_output_id_WF.
  split. now apply sym_o_cvir_inputs_used.
  now apply sym_o_cvir_relabel_WF.
Qed.

Theorem cast_i_cvir_WF :
  forall ni ni' no (ir : cvir ni no) (H : ni = ni'),
  cvir_WF ir -> cvir_WF (cast_i_cvir ir H).
Proof.
  unfold cvir_WF ; intros ni ni' no ir H [? [? [? [? ?]]]].
  split. now apply cast_i_cvir_unique.
  split. now apply cast_i_cvir_input_id_WF.
  split. now apply cast_i_cvir_output_id_WF.
  split. now apply cast_i_cvir_inputs_used.
  now apply cast_i_cvir_relabel_WF.
Qed.

Theorem cast_o_cvir_WF :
  forall ni no no' (ir : cvir ni no) (H : no = no'),
  cvir_WF ir -> cvir_WF (cast_o_cvir ir H).
Proof.
  unfold cvir_WF ; intros ni no no' ir H [? [? [? [? ?]]]].
  split. now apply cast_o_cvir_unique.
  split. now apply cast_o_cvir_input_id_WF.
  split. now apply cast_o_cvir_output_id_WF.
  split. now apply cast_o_cvir_inputs_used.
  now apply cast_o_cvir_relabel_WF.
Qed.

Theorem focus_input_cvir_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_WF ir -> cvir_WF (focus_input_cvir ir i).
Proof.
  unfold focus_input_cvir.
  intros.
  apply cast_i_cvir_WF.
  apply sym_i_cvir_WF.
  apply cast_i_cvir_WF.
  apply sym_i_cvir_WF.
  apply cast_i_cvir_WF.
  assumption.
Qed.

Theorem focus_output_cvir_WF :
  forall ni no (ir : cvir ni no) (i : fin no),
  cvir_WF ir -> cvir_WF (focus_output_cvir ir i).
Proof.
  unfold focus_output_cvir.
  intros.
  apply cast_o_cvir_WF.
  apply sym_o_cvir_WF.
  apply cast_o_cvir_WF.
  apply sym_o_cvir_WF.
  apply cast_o_cvir_WF.
  assumption.
Qed.

Theorem swap_i_cvir_WF :
  forall ni no (ir : cvir ni no) (i : fin ni),
  cvir_WF ir -> cvir_WF (swap_i_input_cvir i ir).
Proof.
  unfold cvir_WF ; intros ni no ir i [? [? [? [? ?]]]].
  split. now apply swap_i_cvir_unique.
  split. now apply swap_i_cvir_input_id_WF.
  split. now apply swap_i_cvir_output_id_WF.
  split. now apply swap_i_cvir_inputs_used.
  now apply swap_i_cvir_relabel_WF.
Qed.

Theorem loop_cvir_WF :
  forall (ni no n : nat) (ir : cvir (n+ni) (n+no)),
  cvir_WF ir -> cvir_WF (loop_cvir n ir).
Proof.
  unfold cvir_WF ; intros ni no ir i [? [? [? [? ?]]]].
  split. now apply loop_cvir_unique.
  split. now apply loop_cvir_input_id_WF.
  split. now apply loop_cvir_output_id_WF.
  split. now apply loop_cvir_inputs_used.
  now apply loop_cvir_relabel_WF.
Qed.

Theorem loop_open_cvir_WF :
  forall (ni no : nat) (ir : cvir (S ni) (S no)),
  cvir_WF ir -> cvir_WF (loop_cvir_open ir).
Proof.
  unfold cvir_WF ; intros ni no ir [? [? [? [? ?]]]].
  split. now apply loop_open_cvir_unique.
  split. now apply loop_open_cvir_input_id_WF.
  split. now apply loop_open_cvir_output_id_WF.
  split. now apply loop_open_cvir_inputs_used.
  now apply loop_open_cvir_relabel_WF.
Qed.


Theorem merge_cvir_WF :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  cvir_WF ir1 -> cvir_WF ir2 ->
  cvir_WF (merge_cvir ir1 ir2).
Proof.
  unfold cvir_WF.
  intuition.
  now apply merge_cvir_unique.
  now apply merge_cvir_input_id_WF.
  now apply merge_cvir_output_id_WF.
  now apply merge_cvir_inputs_used.
  now apply merge_cvir_relabel_WF.
Qed.

Theorem seq_cvir_WF :
  forall ni n no (ir1 : cvir (S ni) n) (ir2 : cvir n no),
  cvir_WF ir1 -> cvir_WF ir2 ->
  cvir_WF (seq_cvir ir1 ir2).
Proof.
  unfold seq_cvir.
  intros.
  apply loop_cvir_WF.
  apply cast_o_cvir_WF.
  apply cast_i_cvir_WF.
  apply swap_i_cvir_WF.
  apply merge_cvir_WF ; assumption.
Qed.


Theorem join_cvir_WF :
  forall (ni no : nat) (ir : cvir ni (S (S no))),
  cvir_WF ir -> cvir_WF (join_cvir ir).
Proof.
  unfold cvir_WF ; intros ni no ir [? [? [? [? ?]]]].
  split. now apply join_cvir_unique.
  split. now apply join_cvir_input_id_WF.
  split. now apply join_cvir_output_id_WF.
  split. now apply join_cvir_inputs_used.
  now apply join_cvir_relabel_WF.
Qed.


(** TODO Documente these lemmas *)
Lemma cvir_inputs : forall {ni no} (ir : cvir ni no) vi vo vt i,
  cvir_ids_WF ir ->
  cvir_inputs_used ir ->
  List.In i (inputs (blocks ir vi vo vt)) <-> In i (vi ++ vt).
Proof.
  split; intros.
  - apply find_block_in_inputs in H1.
    destruct H1.
    apply find_block_has_id in H1 as ?. subst i.
    apply find_block_In in H1.
    now apply H in H1.
  - now apply H0.
Qed.

Lemma cvir_outputs : forall {ni no} (ir : cvir ni no) vi vo vt o,
  cvir_ids_WF ir ->
  List.In o (outputs (blocks ir vi vo vt)) -> In o (vi ++ vo ++ vt).
Proof.
  intros.
  unfold cvir_ids_WF in H.
  apply outputs_successors in H0. destruct H0 as (? & ? & ?).
  apply H in H0 as [_ ?].
  apply H0.
Admitted. (* easy, but I should probably get rid of out_blk_id *)

Theorem unique_bid_wf_ocfg_bid : forall ni no (ir : cvir ni no) vi vo vt,
(* maybe redefine unique_vector from NoDup to have this property for free? *)
  unique_bid ir ->
  unique_vector (vi ++ vt) ->
  wf_ocfg_bid (blocks ir vi vo vt).
Admitted.
