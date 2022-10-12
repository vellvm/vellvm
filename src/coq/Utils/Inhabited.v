Require Import ZArith.

Class Inhabited (X : Type) :=
  { inhabitant : X
  }.

#[global] Instance Inhabited_unit : Inhabited unit :=
  { inhabitant := tt
  }.

#[global] Instance Inhabited_nat : Inhabited nat :=
  { inhabitant := 0
  }.

#[global] Instance Inhabited_prod {X Y} `{IX : Inhabited X} `{IY : Inhabited Y} : Inhabited (X * Y)%type :=
  { inhabitant := (inhabitant, inhabitant)
  }.

#[global] Instance Inhabited_list {X} : Inhabited (list X)%type :=
  { inhabitant := nil
  }.

#[global] Instance Inhabited_N : Inhabited N :=
  { inhabitant := 0%N
  }.
