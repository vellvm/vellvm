From Coq Require Import List.

Variant NonEmpty A :=
| nempty : A -> list A -> NonEmpty A
.

Arguments nempty {A}.

Definition head {A : Type} (ne : NonEmpty A) : A
  := match ne with
     | nempty x xs => x
     end.

Definition tail {A : Type} (ne : NonEmpty A) : list A
  := match ne with
     | nempty x xs => xs
     end.

Definition nth_error {A : Type} (ne : NonEmpty A) (n : nat) : option A
  := match n with
     | O => Some (head ne)
     | S x => List.nth_error (tail ne) x
     end.

Definition nth {A : Type} (n : nat) (ne : NonEmpty A) (def : A) : A
  := match n with
     | O => head ne
     | S x => List.nth x (tail ne) def
     end.
