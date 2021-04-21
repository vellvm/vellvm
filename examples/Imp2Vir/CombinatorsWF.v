From Coq Require Import
     Lia
     List
     NArith.

From Vellvm Require Import Syntax.

From tutorial Require Import Fin.

Require Import Vector Combinators.

Open Scope nat_scope.
Open Scope vector_scope.

Arguments n_int : default implicits.
Arguments blocks : default implicits.

Definition unique_vector {A} {n} (v : Vector.t A n) : Prop :=
  forall i1 i2, nth v i1 = nth v i2 -> i1 = i2.

Definition unique_bid {ni no} ir : Prop :=
  forall (vi : Vector.t int ni) (vo : Vector.t int no) vt,
  forall b1 b2,
  unique_vector (vi ++ vt)%vector ->
  List.In b1 (blocks ir vi vo vt) ->
  List.In b2 (blocks ir vi vo vt) ->
  blk_id b1 = blk_id b2 ->
  b1 = b2.

Theorem vector_in_app_iff : forall A n n' (v : Vector.t A n) (v' : Vector.t A n') (a : A),
  Vector.In a (v ++ v')%vector <-> Vector.In a v \/ Vector.In a v'.
Proof.
  intros ? ? ? [] [] ?.
  unfold In in *. simpl in *.
  apply in_app_iff.
Qed.

Theorem nth_firstn : forall A (l : list A) i n (H : i < n) a,
  List.nth i l a = List.nth i (firstn n l) a.
Admitted.

Theorem merge_cvir_unique :
  forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2),
  unique_bid ir1 -> unique_bid ir2 -> unique_bid (merge_cvir ir1 ir2).
Proof.
  unfold unique_bid.
  unfold unique_vector.
  intros.
  apply in_app_iff in H2, H3.
  simpl in *.
  destruct H2, H3.
  - eapply H.
    2,3,4: eassumption.
    intros.
    destruct vi, vo, vt, i1, i2.
    apply Fin.unique_fin.
    simpl in *.
    unfold Vec.append in *.
    simpl in *.
    erewrite nth_rewrite in H5.
    erewrite nth_rewrite in H5.
    simpl in H5.
    assert (x2 < length (firstn ni1 x) \/ x2 >= length (firstn ni1 x)).
    lia.
    assert (x3 < length (firstn ni1 x) \/ x3 >= length (firstn ni1 x)).
    lia.
    destruct H6, H7.
    + erewrite 2 app_nth1 in H5 ; try assumption.
      rewrite firstn_length in H6,H7.
      epose (x2' := fi' x2). epose (x3' := fi' x3).
      specialize (H1 x2' x3').
      erewrite 2 nth_rewrite in H1.
      simpl in H1.
      rewrite 2 app_nth1 in H1 ; try lia.
      rewrite<- 2 nth_firstn in H5 ; try lia.
      apply H1 in H5.
      injection H5 as ?.
      exact H5.
   + erewrite app_nth1 in H5 ; try assumption.
     erewrite app_nth2 in H5 ; try assumption.
     rewrite firstn_length in H5,H6,H7.
     epose (x2' := fi' x2). epose (x3' := fi' (ni2 + x3)).
     specialize (H1 x2' x3').
     erewrite 2 nth_rewrite in H1.
     simpl in H1.
     rewrite app_nth1 in H1 ; try lia.
     rewrite app_nth2 in H1 ; try lia.
     rewrite<- 2 nth_firstn in H5 ; try lia.
     rewrite min_l in H5 ; try lia.
     replace (x3 - ni1) with (ni2 + x3 - length x ) in H5 by lia.
     apply H1 in H5.
     injection H5 as ?.
Admitted.