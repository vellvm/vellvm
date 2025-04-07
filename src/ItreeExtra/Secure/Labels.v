(* Shared definitions for the Secure component. *)

From ITree Require Import
  Basics.Utils
  Axioms.

Variant nonempty (A : Type) : Prop := ne (a : A).

Variant empty (A : Type) : Prop := emp : (A -> False) -> empty A.

Lemma classic_empty : forall A, empty A \/ nonempty A.
Proof.
  intros. destruct (classic (nonempty A)); eauto.
  left. constructor. intros. apply H. constructor; auto.
Qed.

Class Preorder :=
  {
    L : Type;
    leq : L -> L -> Prop;
  }.

Ltac contra_size :=
  match goal with
  | [ Hemp : empty ?A, Hne : nonempty ?A |- _ ] => inv Hemp; inv Hne; contradiction
  | [ Hemp : empty ?A, a :?A |- _] => inv Hemp; contradiction
  end
.
