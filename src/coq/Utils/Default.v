From Coq Require Import ZArith List.

Import ListNotations.

Class Default A : Type :=
  { def : A
  }.

Instance DefaultN : Default N :=
  { def := 0 }.

Instance DefaultNat : Default nat :=
  { def := 0 }.

Instance DefaultZ : Default Z :=
  { def := 0 }.

Instance DefaultList {A} : Default (list A) :=
  { def := [] }.
