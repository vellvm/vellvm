(** Some utility functions and lemmas for QC. *)
Require Import Ceres.Ceres.

(* From QuickChick Require Import QuickChick. *)
From QuickChick Require Import Generators Producer.
Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor Applicative Monads.

Require Import ExtLib.Data.Monads.StateMonad.

From Vellvm Require Import LLVMAst Util AstLib Syntax.CFG.
From Vellvm Require Import Semantics.DynamicValues.


Require Import List.


Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import Lia.

Open Scope Z_scope.

Fixpoint max_nat_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x::rest => max x (max_nat_list rest)
  end.

(* TODO: how big should lists be? *)
Fixpoint sizeof_typ (t : typ) : nat :=
  match t with
  | TYPE_Pointer t            => S (sizeof_typ t)
  | TYPE_Array sz t           => S (sizeof_typ t)
  | TYPE_Function ret args _  => max (sizeof_typ ret) (max_nat_list (map sizeof_typ args))
  | TYPE_Struct fields        => max_nat_list (map sizeof_typ fields)
  | TYPE_Packed_struct fields => max_nat_list (map sizeof_typ fields)
  | TYPE_Vector sz t          => S (sizeof_typ t)
  | _                         => 0
  end.

(* TODO: Move these *)
Fixpoint find_pred {A} (p : A -> bool) (l : list A) : option A
  := match l with
     | []   => None
     | x::xs =>
       if p x
       then Some x
       else find_pred p xs
     end.

Lemma list_sum_map :
  forall {X} (f : X -> nat) x xs,
    In x xs ->
    (list_sum (map f xs) >= f x)%nat.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs H).
    unfold list_sum in IHxs.
    lia.
Qed.
