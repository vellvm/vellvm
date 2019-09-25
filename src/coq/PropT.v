From Coq Require Import Ensembles.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.MonadTrans
Data.Monads.EitherMonad.

From ITree Require Import
     Basics.Basics
     ITree.

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

  Global Instance MonadT_PropT {M}: MonadT (PropT M) M :=
    {| lift := fun _ m m' => m = m' |}.

  Global Polymorphic Instance MonadIter_Prop {M} {MM: MonadIter M} : MonadIter (PropT M) :=
    fun R I step i r =>
      exists (step': I -> M (I + R)%type),
        (forall j, step j (step' j)) /\ CategoryOps.iter step' i = r.

  Definition interp_prop {E M}
             {FM : Functor M} {MM : Monad M}
             {IM : MonadIter M} (h : E ~> PropT M) :
    itree E ~> PropT M := interp h.

  (* YZ TODO: Look on Steve's github what he did last summer in relation
     to working up to an equivalence relation *)

End PropMonad.
