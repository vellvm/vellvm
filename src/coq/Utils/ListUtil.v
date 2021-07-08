From Coq Require Import List Lia ZArith.

Import ListNotations.

(* TODO: Move. Also, do I really have to define this? *)
Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
  := match xs, ys with
     | [], _        => []
     | _, []        => []
     | a::xs', b::ys' => f a b :: zipWith f xs' ys'
     end.

Definition zip {X Y} (xs : list X) (ys : list Y) := zipWith (fun a b => (a, b)) xs ys.

Lemma map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
Proof.
  induction l.
  - exact [].
  - refine (f a _ :: IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Lemma list_sum_map :
  forall {X} (f : X -> nat) x xs,
    In x xs ->
    list_sum (map f xs) >= f x.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs H).
    unfold list_sum in IHxs.
    lia.
Qed.

Fixpoint Zseq (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S x => start :: Zseq (Z.succ start) x
  end.

Fixpoint Nseq (start : N) (len : nat) : list N :=
  match len with
  | O => []
  | S x => start :: Nseq (N.succ start) x
  end.

Fixpoint drop {A} (n : N) (l : list A) : list A
  := match l with
     | [] => []
     | (x::xs) =>
       if N.eqb 0 n
       then l
       else drop (N.pred n) xs
     end.

Fixpoint take {A} (n : N) (l : list A) : list A
  := match l with
     | [] => []
     | (x::xs) =>
       if N.eqb 0 n
       then []
       else x :: take (N.pred n) xs
     end.

Definition between {A} (lo hi : N) (l : list A) : list A
  := take (hi - lo) (drop lo l).
