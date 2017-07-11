Require Import String.

Definition err (A : Type) : Type := (string + A)%type.
Definition err_bind {A B : Type}
           (MA : err A) (f: A -> B) (MB : err B) :=
  match MA with
  | inl err => inl err
  | inr x => inr (f x)
  end.
Definition err_ret {A : Type} (a : A) : err A :=
  inr a.
