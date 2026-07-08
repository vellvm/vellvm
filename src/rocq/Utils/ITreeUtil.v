From ITree Require Import ITree Eq.

Definition void_elim {A} : void -> A :=
  fun v => match v: void with end.

Definition trigger_cast' {E : Type -> Type} {A : Type} (e : E void) : itree E A :=
  ITree.bind (ITree.trigger e) void_elim.

Notation trigger_cast e := (trigger_cast' (subevent _ e)).


