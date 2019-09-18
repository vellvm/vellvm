From Coq Require Import Ensembles.
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Section PropMonad.

  Definition PropT (m: Type -> Type): Type -> Type :=
    fun X => Ensemble (m X).

  Global Instance Functor_Prop {M} {MM : Functor M}
    : Functor (PropT M) :=
    {| fmap := fun A B f PA b => exists (a: M A), PA a /\ b = fmap f a |}.

  Global Instance Monad_Prop {M} {MM : Monad M}
    : Monad (PropT M) :=
    {|
      ret := fun _ x y =>  y = ret x
      ; bind := fun A B PA K b => exists (a: A), PA (ret a) /\ K a b
    |}.



End PropMonad.
