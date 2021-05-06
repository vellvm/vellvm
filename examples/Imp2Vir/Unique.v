From Coq Require Import
    Lia
    List.

From tutorial Require Import Fin.

Require Import Vec.

Section Unique.

Definition unique_list {A} (l : list A) : Prop :=
  forall i1 i2, i1 < length l -> i2 < length l ->
  List.nth_error l i1 = List.nth_error l i2 -> i1 = i2.

Ltac nth_error_app123 H :=
  (rewrite nth_error_app1 in H ; [|lia]) +
  (rewrite nth_error_app2 in H ; [|lia] ; (
    rewrite nth_error_app1 in H +
    rewrite nth_error_app2 in H) ; [|lia]
  ).

Theorem unique_list_sym2 : forall A (l1 l2 l3 : list A),
  unique_list (l1 ++ l2 ++ l3) -> unique_list (l1 ++ l3 ++ l2).
Proof.
  unfold unique_list.
  intros.
  assert (i1 < length l1 \/
    (i1 >= length l1 /\ i1 < length l1 + length l3) \/
    i1 >= length l1 + length l3) by lia.
  assert (i2 < length l1 \/
    (i2 >= length l1 /\ i2 < length l1 + length l3) \/
    i2 >= length l1 + length l3) by lia.
  destruct H3 as [?|[?|?]], H4 as [?|[?|?]].
  all: nth_error_app123 H2; nth_error_app123 H2.
  all: match type of H3 with
  | ?i1 < length ?l1 => specialize (H i1)
  | (?i1 >= length ?l1 /\ ?i1 < length ?l1 + length ?l3) => specialize (H (length l2 + i1))
  | (?i1 >= length ?l1 + length ?l3) => specialize (H (i1 - length l3))
  end.
  all: match type of H4 with
  | ?i1 < List.length ?l1 => specialize (H i1)
  | (?i1 >= length ?l1 /\ ?i1 < length ?l1 + length ?l3) => specialize (H (length l2 + i1))
  | (?i1 >= length ?l1 + length ?l3) => specialize (H (i1 - length l3))
  end.
  all: rewrite 2 app_length in *.
  all: lapply H; [ intro | try lia ].
  all: lapply H5; [ intro | lia ].
  all: nth_error_app123 H6; nth_error_app123 H6.
  all: replace (length l2 + i1 - length l1 - length l2) with (i1 - length l1) in * by lia.
  all: replace (i1 - length l3 - length l1) with (i1 - length l1 - length l3) in * by lia.
  all: lapply H6; [lia | rewrite H2; f_equal; lia].
Qed.

Theorem unique_list_sym : forall A (l1 l2 : list A),
  unique_list (l1 ++ l2) -> unique_list (l2 ++ l1).
Proof.
  intros.
  rewrite <- app_nil_l.
  apply unique_list_sym2.
  simpl.
  assumption.
Qed.

Definition unique_vector {A} {n} (v : Vec.t A n) : Prop :=
  forall i1 i2, nth v i1 = nth v i2 -> i1 = i2.

Theorem unique_list_vector : forall A n (v : Vec.t A n),
  unique_list (proj1_sig v) <-> unique_vector v.
Proof.
  unfold unique_vector, unique_list.
  split ; intros.
  - specialize (H (proj1_sig i1) (proj1_sig i2)).
    rewrite vector_length in H.
    specialize (H (proj2_sig i1) (proj2_sig i2)).
    rewrite nth_destruct_eq in H0.
    apply H in H0.
    apply unique_fin.
    exact H0.
  - rewrite vector_length in H0, H1.
    specialize (H (exist _ i1 H0) (exist _ i2 H1)).
    rewrite nth_destruct_eq in H.
    apply H in H2.
    inversion H2.
    reflexivity.
Qed.

Theorem unique_vector_sym : forall A n1 n2 (v1 : Vec.t A n1) (v2 : Vec.t A n2),
  unique_vector (v1 ++ v2)%vec -> unique_vector (v2 ++ v1)%vec.
Proof.
  intros.
  apply unique_list_vector.
  apply unique_list_vector in H.
  simpl in *.
  apply unique_list_sym.
  exact H.
Qed.

Theorem unique_vector_sym2 :
  forall A n1 n2 n3 (v1 : Vec.t A n1) (v2 : Vec.t A n2) (v3 : Vec.t A n3),
  unique_vector (v1 ++ v2 ++ v3)%vec -> unique_vector (v1 ++ v3 ++ v2)%vec.
Proof.
  intros.
  apply unique_list_vector.
  apply unique_list_vector in H.
  simpl in *.
  apply unique_list_sym2.
  exact H.
Qed.

Theorem unique_vector_app1 :
  forall A n1 n2 (v1 : Vec.t A n1) (v2 : Vec.t A n2),
  unique_vector (v1 ++ v2)%vec -> unique_vector v1.
Proof.
  unfold unique_vector.
  intros.
  destruct v1, v2.
  apply unique_fin. simpl.
  specialize (H (L n2 i1) (L n2 i2)).
  lapply H.
  - destruct i1, i2.
    simpl in *.
    intro.
    inversion H1.
    reflexivity.
  - rewrite 2 vector_app_nth1.
    exact H0.
Qed.

Theorem unique_vector_app2 :
  forall A n1 n2 (v1 : Vec.t A n1) (v2 : Vec.t A n2),
  unique_vector (v1 ++ v2)%vec -> unique_vector v2.
Proof.
  unfold unique_vector.
  intros.
  destruct v1, v2.
  apply unique_fin. simpl.
  specialize (H (R n1 i1) (R n1 i2)).
  lapply H.
  - destruct i1, i2.
    simpl in *.
    intro.
    inversion H1.
    lia.
  - rewrite 2 vector_app_nth2.
    exact H0.
Qed.

End Unique.