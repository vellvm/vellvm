From Vellvm Require Import
  DynamicTypes
  Utils.Error
  Utils.Monads.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.

Import MonadNotation.

Inductive Poisonable (A : Type) : Type :=
| Unpoisoned : A -> Poisonable A
| Poison : forall (dt : dtyp), Poisonable A
.

Arguments Unpoisoned {A} a.
Arguments Poison {A}.

#[global] Instance MonadPoisonable : Monad Poisonable
  := { ret  := @Unpoisoned;
       bind := fun _ _ ma mab => match ma with
                              | Poison dt => Poison dt
                              | Unpoisoned v => mab v
                              end
  }.

Class RAISE_POISON (M : Type -> Type) :=
  { raise_poison : forall {A}, dtyp -> M A }.

#[global] Instance RAISE_POISON_Poisonable : RAISE_POISON Poisonable :=
  { raise_poison := fun A dt => Poison dt }.

#[global] Instance RAISE_POISON_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_POISON M} : RAISE_POISON (MT M) :=
  { raise_poison := fun A dt => lift (raise_poison dt);
  }.
