From ITree Require Import
     Basics.HeterogeneousRelations.

From Coq Require Import
  RelationClasses
  Relation_Definitions.

Infix"×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

#[global] Instance TT_Reflexive {A} : Reflexive (@TT A).
Proof.
  intro.
  reflexivity.
Qed.

#[global] Instance TT_Transitive {A} : Transitive (@TT A).
Proof.
  intro.
  auto.
Qed.

#[global] Instance TT_Symmetric {A} : Symmetric (@TT A).
Proof.
  intro.
  auto.
Qed.

#[global] Instance TT_Equivalence {A} : Equivalence (@TT A).
Proof.
  split; typeclasses eauto.
Qed.
