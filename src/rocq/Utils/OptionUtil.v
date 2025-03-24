From ExtLib Require Import
  Structures.Foldable.

Definition guard_opt (x : bool) : option unit
  := if x then Some tt else None.

Definition from_option {A} (def : A) (opt : option A) : A
  := match opt with
     | Some x => x
     | None => def
     end.

Definition option_rel2 {X1 X2 : Type} (R : X1 -> X2 -> Prop) : (option X1 -> option X2 -> Prop) :=
  fun mx my => match mx,my with
            | Some x, Some y => R x y
            | None, None => True
            | _, _ => False
            end.
#[export] Hint Unfold option_rel2 : core.

Import Monoid.
#[global] Instance Foldable_option {a} : Foldable (option a) a.
split.
intros m M conv oa.
apply (match oa with | Some a => conv a | None => (monoid_unit M) end).
Defined.

Definition maybe {a b} (def : b) (f : a -> b) (oa : option a) : b
  := match oa with
     | Some a => f a
     | None => def
     end.
