From Coq Require Import
     Lia
     Lists.List
     Arith
     ZArith.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util.

From Imp2Vir Require Import Fin.

Section Vec.

Open Scope nat_scope.

(* t is the type of list A of size n *)
Definition t (A : Type) (n : nat) : Type := { l : list A | length l = n }.


Notation vec := (exist (fun l' : list _ => _)).
Notation vec' l := (exist (fun l' : list _ => _) l _).


(* (v : t A n) is a list A of size n *)
(* v -> (a:list A, Ha proof of P a), where is "a" the witnesses and "Ha" the
proof that a respects the property (here, length a = n) *)


Theorem vector_proj1_unique : forall A n (v v' : t A n),
    proj1_sig v = proj1_sig v' -> v = v'.
Proof.
  intros.
  destruct v, v'.
  simpl in *.
  destruct H.
  f_equal.
  subst. rewrite Eqdep_dec.UIP_refl_nat.
  reflexivity.
Qed.

Theorem vector_length : forall A n (v : t A n),
  length (proj1_sig v) = n.
Proof.
  destruct v.
  simpl.
  exact e.
Qed.

Program Definition cast {A} {n n'} (v : t A n) (H : n = n') : t A n' :=
  exist _ (proj1_sig v) _.
Next Obligation.
  apply vector_length.
Defined.

Theorem cast_vec : forall A n n' (l : list A) (H : length l = n) (H' : n = n'),
  cast (vec l H) H' = vec l (eq_trans H H').
Proof.
  intros.
  unfold cast.
  simpl.
  apply vector_proj1_unique.
  reflexivity.
Qed.

Program Definition empty (A : Type) : t A 0 := vec' nil.

Program Definition cons {A} {n} h (v : t A n) : t A (S n) := vec' (h::v).
Next Obligation.
  destruct v. simpl in *.
  f_equal.
  assumption.
Defined.

Program Definition hd {A} {n} (v : t A (S n)) : A :=
  match proj1_sig v with
  | h :: _ => h
  | nil => _
  end.
Next Obligation.
  destruct v.
  destruct x.
  - discriminate e.
  - exact a.
Qed.

Program Definition tl {A} {n} (v : t A (S n)) : t A n :=
  match proj1_sig v with
  | _ :: v' => vec' v'
  | nil => _
  end.
Next Obligation.
  destruct v.
  simpl in *. subst. simpl in e. injection e as e. exact e.
Defined.
Next Obligation.
  destruct v.
  destruct x.
  - discriminate e.
  - simpl in *. discriminate Heq_anonymous.
Qed.

Program Definition nth {A} {n} (v : t A n) (i : fin n) : A :=
  match proj1_sig v with
  | h :: l => List.nth i v h
  | nil => _
  end.
Next Obligation.
  destruct n. destruct i.
  - lia.
  - destruct v. simpl in *. subst. discriminate e.
Qed.

Theorem nth_destruct : forall A n (v : t A n) i a, nth v i = List.nth (proj1_sig i) (proj1_sig v) a.
Proof.
  intros ? ? [] [] ?.
  subst.
  simpl.
  unfold nth. simpl. destruct x eqn:?.
  - simpl in l. lia.
  - subst. rewrite (nth_indep _ a a0 l). reflexivity.
Qed.

Theorem nth_rewrite_error : forall A n (v : t A n) i, List.nth_error (proj1_sig v) (proj1_sig i) = Some (nth v i).
Proof.
  intros ? ? [] [].
  erewrite nth_destruct.
  simpl in *.
  apply nth_error_nth'.
  lia.
  Unshelve. destruct x ; [ simpl in * ; lia | assumption ].
Qed.

Theorem nth_destruct_error : forall A n (v : t A n) i a, nth v i = a <-> List.nth_error (proj1_sig v) (proj1_sig i) = Some a.
Proof.
  intros ? ? [] [] ?.
  split ; intro ; subst ; simpl.
  - rewrite <- nth_rewrite_error. simpl. reflexivity.
  - rewrite nth_rewrite_error in H. inversion H. reflexivity.
Qed.

Theorem nth_destruct_eq : forall A n n' (v : t A n) (v' : t A n') i i', nth v i = nth v' i' <-> List.nth_error (proj1_sig v) (proj1_sig i) = List.nth_error (proj1_sig v') (proj1_sig i').
Proof.
  split ; intros ; subst ; simpl.
  - rewrite 2 nth_rewrite_error.
    f_equal. assumption.
  - rewrite 2 nth_rewrite_error in H.
    inversion H.
    reflexivity.
Qed.

Program Definition append {A} {n n'} (v : t A n) (v' : t A n') :
  t A (n + n') := vec' ((proj1_sig v) ++ proj1_sig v').
Next Obligation.
  rewrite app_length. destruct v, v'. simpl. subst. reflexivity.
Defined.

Theorem vector_app_destruct : forall A (l l' : list A) n n' (H : length l = n) (H' : length l' = n') (H'' : length (l ++ l') = n + n'),
  vec (l ++ l') H'' = append (vec l H) (vec l' H').
Proof.
  intros.
  unfold append.
  apply vector_proj1_unique.
  simpl.
  reflexivity.
Qed.

Definition In {A} {n} a (v : t A n) := List.In a (proj1_sig v).

Theorem vector_in_app_iff : forall A n n' (v : t A n) (v' : t A n') (a : A),
  In a (append v v') <-> In a v \/ In a v'.
Proof.
  intros ? ? ? [] [] ?.
  unfold In in *. simpl in *.
  apply in_app_iff.
Qed.

Theorem vector_app_nth1 :
  forall A n n' (v : t A n) (v' : t A n') (k : fin n), nth (append v v') (L n' k) = nth v k.
Proof.
  intros.
  apply nth_destruct_eq.
  destruct v, v', k.
  simpl in *.
  apply nth_error_app1.
  lia.
Qed.

Theorem vector_app_nth2 :
  forall A n n' (v : t A n) (v' : t A n') (k : fin n'), nth (append v v') (R n k) = nth v' k.
Proof.
  intros.
  apply nth_destruct_eq.
  destruct v, v', k.
  simpl in *.
  replace x1 with (n + x1 - length x) at 2 by lia.
  apply nth_error_app2.
  lia.
Qed.

Theorem In_nth :
  forall A n (v : t A n) (x : A), In x v -> exists n : fin n, nth v n = x.
Proof.
  intros.
  eapply In_nth_error in H.
  destruct H as [ n0 H ].
  eexists (fi' n0).
  eapply nth_destruct_error.
  exact H.
  Unshelve. apply Util.nth_error_in in H. rewrite <- vector_length with (v := v). assumption.
Qed.

Program Definition firstn {A} i {j} (v : t A (i+j)) : t A i :=
  vec' (firstn i (proj1_sig v)).
Next Obligation.
  destruct v. simpl in *. rewrite firstn_length. rewrite e.
  rewrite (plus_n_O i) at 1. rewrite Nat.add_min_distr_l. rewrite Nat.min_0_l.
  apply Nat.add_0_r.
Defined.

Theorem firstn_app_exact : forall {A} {i} {j} (v : t A i) (v' : t A j),
  firstn i (append v v') = v.
Proof.
  intros.
  destruct v, v'.
  unfold firstn.
  apply vector_proj1_unique.
  cbn.
  subst.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite Nat.sub_diag.
  now rewrite app_nil_r.
Qed.

Program Definition skipn {A} i {j} (v : t A (i+j)) : t A j :=
  vec' (skipn i (proj1_sig v)).
Next Obligation.
  destruct v. simpl in *. rewrite skipn_length. apply Nat.add_sub_eq_l. auto.
Defined.

Theorem skipn_app_exact : forall {A} {i} {j} (v : t A i) (v' : t A j),
  skipn i (append v v') = v'.
Proof.
  intros.
  destruct v, v'.
  unfold skipn.
  apply vector_proj1_unique.
  cbn.
  subst.
  rewrite skipn_app.
  rewrite skipn_all.
  now rewrite Nat.sub_diag.
Qed.

(* FIXME i could be an implicit argument *)
Definition splitat {A} i {j} (v : t A (i+j)) :
  t A i * t A j :=
  (firstn i v, skipn i v).

Program Definition splitat' {A} {k} (i : fin (k+1)) (v : t A k) :
  t A i * t A (k-i) :=
  splitat i (cast v _).
Next Obligation.
  destruct i. simpl. lia.
Defined.

Theorem splitat_append : forall A n n' (v : t A n) (v' : t A n'),
  splitat n (append v v') = (v,v').
Proof.
  unfold splitat.
  intros.
  f_equal.
  - apply firstn_app_exact.
  - apply skipn_app_exact.
Qed.

Theorem append_splitat : forall A n n' (v : t A n) (v' : t A n') (v'' : t A (n+n')),
  splitat n v'' = (v, v') -> v'' = append v v'.
Proof.
  intros.
  destruct v, v', v''.
  unfold splitat, append in *.
  simpl in *.
  injection H as ?.
  subst x x0.
  apply vector_proj1_unique. simpl.
  rewrite (firstn_skipn n x1).
  reflexivity.
Qed.

Theorem append_splitat' : forall A n (n' : fin (n+1)) (v : t A (proj1_sig n')) (v' : t A (n-(proj1_sig n'))) (v'' : t A n),
  splitat' n' v'' = (v, v') -> proj1_sig v'' = proj1_sig (append v v').
Proof.
  intros.
  simpl.
  apply append_splitat in H.
  inversion H.
  reflexivity.
Qed.

Program Definition uncons {A} {n} (v : t A (S n)) : A * t A n :=
  match proj1_sig v with
  | a :: t => (a, vec' t)
  | _ => _
  end.
Next Obligation.
  destruct v as [[] ?].
  discriminate e.
  simpl in *.
  injection Heq_anonymous as ?.
  subst.
  auto.
Defined.
Next Obligation.
  destruct v as [[] ?].
  discriminate e.
  simpl in *. injection e as ?.
  refine (a, vec' l). exact H0.
Defined.

Theorem uncons_cons : forall A n (v : t A n) a, uncons (cons a v) = (a, v).
Proof.
  intros.
  unfold uncons.
  simpl.
  f_equal.
  apply vector_proj1_unique.
  simpl.
  reflexivity.
Qed.

Theorem cons_uncons : forall A n (v : t A (S n)) (v' : t A n) a, uncons v = (a, v') -> v = cons a v'.
Proof.
  intros.
  destruct v, v'.
  unfold uncons in H.
  destruct x.
  - simpl in e. lia.
  - simpl in *.
    unfold cons.
    simpl.
    inversion H.
    subst.
    apply vector_proj1_unique.
    reflexivity.
Qed.

Theorem In_hd : forall A n (v : t A (S n)), In (hd v) v.
Proof.
  intros.
  destruct (uncons v) eqn:?.
  apply cons_uncons in Heqp.
  subst v.
  unfold In, hd, cons.
  simpl.
  tauto.
Qed.

Program Definition rev {A} {n} (v : t A n) : t A n :=
  vec' (rev (proj1_sig v)).
Next Obligation.
  destruct v.
  rewrite rev_length.
  auto.
Defined.

Program Definition seq (start len : nat) : t nat len :=
  vec' (List.seq start len).
Next Obligation.
  rewrite seq_length.
  reflexivity.
Defined.

Program Definition map {A B} {n} (f : A -> B) (v : t A n) : t B n :=
  vec' (map f (proj1_sig v)).
Next Obligation.
  destruct v.
  rewrite map_length.
  auto.
Defined.

Definition sym_vec {A} {n1 n2 n3} (v : Vec.t A (n1 + (n2 + n3))) : Vec.t A (n1 + (n3 + n2)) :=
  let '(v1,v23) := Vec.splitat n1 v in
  let '(v2,v3) := Vec.splitat n2 v23 in
  (append v1 (append v3 v2)).

Theorem sym_vec_app : forall {A} {n1 n2 n3} (v1 : Vec.t A n1) (v2 : Vec.t A n2) (v3 : Vec.t A n3),
  sym_vec (append v1 (append v2 v3)) = (append v1 (append v3 v2)).
Proof.
  intros.
  unfold sym_vec.
  rewrite splitat_append.
  rewrite splitat_append.
  reflexivity.
Qed.

(* Misc lemmas about fin *)

Lemma split_fin_sum_inl :
  forall n m f l, split_fin_sum n m f = inl l -> f = L m l.
Proof.
  intros.
  unfold split_fin_sum in H.
  break_match; [| discriminate ].
  inv H.
  now apply unique_fin.
Qed.

Lemma split_fin_sum_inr :
  forall n m f r, split_fin_sum n m f = inr r -> f = R n r.
Proof.
  intros.
  unfold split_fin_sum in H.
  break_match; [ discriminate |].
  inv H.
  apply unique_fin.
  simpl.
  lia.
Qed.

End Vec.

Ltac destruct_vec0 v :=
  let H := fresh "H" in
  let l := fresh "l" in
  destruct v as [l H]; apply length_zero_iff_nil in H as ?; subst l.

Ltac destruct_vec1 v :=
  let H := fresh "H" in
  let H' := fresh "H'" in
  let l := fresh "l" in
  destruct v as [[] H]; [
    simpl in H; lia |
    simpl in H; apply eq_add_S in H as H'; apply length_zero_iff_nil in H'; subst l
  ].

Ltac destruct_vec2 v :=
  let H := fresh "H" in
  let H' := fresh "H'" in
  let H'' := fresh "H''" in
  let l := fresh "l" in
  destruct v as [[] H]; [
  simpl in H; lia |
  destruct l ;
  [ simpl in H ; lia |
    simpl in H; apply eq_add_S in H as H'; apply eq_add_S in H' as H'';
    apply length_zero_iff_nil in H''; subst l]].


Ltac split_vec v n1 :=
  let vp := fresh "vp" in
  let v1 := fresh v "1" in
  let v2 := fresh v "2" in
  remember (splitat n1 v) as vp eqn:?Heqvp;
  destruct vp as [ v1 v2 ] eqn:?Heq;
  subst vp;
  symmetry in Heqvp;
  apply append_splitat in Heqvp;
  subst v.

Theorem sym_vec_In : forall {A} {n1 n2 n3} (v : Vec.t A (n1 + (n2 + n3))) a,
  In a v <-> In a (sym_vec v).
Proof.
  intros.
  split_vec v n1.
  split_vec v2 n2.
  rewrite sym_vec_app.
  rewrite !vector_in_app_iff. tauto.
Qed.

From ExtLib Require Import FMapAList.
From Vellvm Require Import Utils.AListFacts.

Definition vec_build_map {A n} (v v' : Vec.t A n) : alist A A :=
  List.combine (proj1_sig v) (proj1_sig v').


(* Theorem vec_build_map_assoc : *)
(*   forall A n1 n2 n3 (v1 v1': Vec.t A n1) (v2 v2': Vec.t A n2) (v3 v3': Vec.t A n3), *)
(*   vec_build_map (append (append v1 v2) v3) (append (append v1' v2') v3') *)
(*   = *)
(*   vec_build_map (append v1 (append v2 v3)) (append v1' (append v2' v3')). *)
(* Proof. *)
(*   intros. *)
(*   destruct v1 ; subst ; cbn in *. *)
(*   destruct v2 ; subst ; cbn in *. *)
(*   destruct v3 ; subst ; cbn in *. *)
(*   destruct v1' ; subst ; cbn in *. *)
(*   destruct v2' ; subst ; cbn in *. *)
(*   destruct v3' ; subst ; cbn in *. *)
(*   rewrite !List.app_assoc ; auto. *)
(* Qed. *)



(* Swap vectors *)
Definition swap_vec {A} {n1 n2} (v : Vec.t A (n1 + n2)) : Vec.t A (n2 + n1) :=
  let '(v1,v2) := Vec.splitat n1 v in
  append v2 v1.

Theorem swap_vec_app : forall {A} {n1 n2} (v1 : Vec.t A n1) (v2 : Vec.t A n2),
  swap_vec (append v1 v2) = (append v2 v1).
Proof.
  intros.
  unfold swap_vec.
  rewrite splitat_append.
  reflexivity.
Qed.


Theorem swap_vec_In : forall {A} {n1 n2} (v : Vec.t A (n1 + n2)) a,
  In a v <-> In a (swap_vec v).
Proof.
  intros.
  split_vec v n1.
  rewrite swap_vec_app.
  rewrite !vector_in_app_iff. tauto.
Qed.



Theorem cast_In : forall {A} {n n'} (v : Vec.t A n) (H : n=n') a,
  In a v <-> In a (cast v H).
Proof.
  intros.
  destruct v.
  unfold cast. subst.
  cbn. tauto.
Qed.

(* [0,1,...,i-1,i,i+1,...,n] ->
   [i,i+1,...,n,0,1,...,i-1] *)
Program Definition swap_i {A} {n} (i : Fin.fin n) (v : t A n) : t A n :=
  let v' := Vec.cast v (_ : n = (proj1_sig i + (n-proj1_sig i))) in
  let v'' := swap_vec v' in
  Vec.cast v'' (_ : _ = n).
Next Obligation.
destruct i ; simpl in * ; lia.
Qed.
Next Obligation.
  destruct i ; simpl in * ; lia.
Qed.

Theorem swap_i_In : forall {A} {n} (i: Fin.fin n) (v : Vec.t A n) a,
  In a v <-> In a (swap_i i v).
Proof.
  intros.
  unfold swap_i.
  split ; intros.
  - apply cast_In.
    rewrite <- swap_vec_In.
    apply cast_In. assumption.
  - apply cast_In in H.
    rewrite <- swap_vec_In in H.
    apply cast_In in H. assumption.
Qed.


Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Notation "h :: t" := (cons h t) (at level 60, right associativity).
Infix "++" := append : vec_scope.
Notation vec' l := (exist (fun l' : list _ => _) l _).
