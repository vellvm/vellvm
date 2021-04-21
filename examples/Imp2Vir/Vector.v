From Coq Require Import
     Lia
     Lists.List
     Arith
     ZArith.

From Vellvm Require Import
     Syntax.

From tutorial Require Import Fin.

Section Vector.

Open Scope nat_scope.

Definition t (A : Type) (n : nat) : Type := { l : list A | length l = n }.

Notation vec' l := (exist (fun l' : list _ => _) l _).

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

Theorem nth_rewrite : forall A n (v : t A n) i a, nth v i = List.nth (proj1_sig i) (proj1_sig v) a.
Proof.
  intros ? ? [] [] ?.
  subst.
  simpl.
  unfold nth. simpl. destruct x eqn:?.
  - simpl in l. lia.
  - subst. rewrite (nth_indep _ a a0 l). reflexivity.
Qed.

(*Definition unique_vector {A} {n} (v : t A n) : Prop :=
  forall i1 i2, nth v i1 = nth v i2 -> i1 = i2.*)

Program Definition append {A} {n n'} (v : t A n) (v' : t A n') :
  t A (n + n') := vec' ((proj1_sig v) ++ proj1_sig v').
Next Obligation.
  rewrite app_length. destruct v, v'. simpl. subst. reflexivity.
Defined.

Definition In {A} {n} a (v : t A n) := List.In a (proj1_sig v).

Program Definition splitat {A} i {j} (v : t A (i+j)) :
  t A i * t A j :=
  (vec' (firstn i (proj1_sig v)), vec' (skipn i (proj1_sig v))).
Next Obligation.
  destruct v. simpl in *. rewrite firstn_length. rewrite e.
  rewrite (plus_n_O i) at 1. rewrite Nat.add_min_distr_l. rewrite Nat.min_0_l.
  apply Nat.add_0_r.
Defined.
Next Obligation.
  destruct v. simpl in *. rewrite skipn_length. apply Nat.add_sub_eq_l. auto.
Defined.

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

End Vector.

Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "h :: t" := (cons h t) (at level 60, right associativity).
Infix "++" := append : vector_scope.
Notation vec' l := (exist (fun l' : list _ => _) l _).