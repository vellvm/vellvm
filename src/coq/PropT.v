From Coq Require Import Ensembles.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import Basics.Basics.

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

  Global Polymorphic Instance MonadIter_Prop {M} {MM: MonadIter M} : MonadIter (PropT M) :=
    fun R I step i r =>
      exists (step': I -> M (I + R)%type),
        (forall j, step j (step' j)) /\ iter step' i = r.

  (* Look on Steve's github what he did last summer *)
End PropMonad.
