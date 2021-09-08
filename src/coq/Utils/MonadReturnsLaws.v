From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Monad.

From ExtLib Require Import
     Structures.Monads.

From Vellvm.Utils Require Import MonadExcLaws PropT.

Set Primitive Projections.

Section Laws.

  Context (M : Type -> Type).
  Context {Monad : Monad M}.
  Context {Eq1 : @Eq1 M}.

  Local Open Scope monad_scope.

  Class MonadReturns :=
    { MReturns : forall {A} (x : A) (ma : M A), Prop;

      MReturns_bind : forall {A B} (a : A) (b : B) (ma : M A) (k : A -> M B),
          MReturns a ma -> MReturns b (k a) -> MReturns b (bind ma k);

      MReturns_bind_inv : forall {A B} (ma : M A) (k : A -> M B) (b : B),
          MReturns b (bind ma k) -> exists a : A , MReturns a ma /\ MReturns b (k a);

      MReturns_ret : forall {A} (a : A) (ma : M A),
        eq1 ma (ret a) -> MReturns a ma;

      MReturns_ret_inv : forall {A} (x y : A),
          MReturns x (ret y) -> x = y
    }.

End Laws.

Arguments MReturns {M _ _ _ _}.
Arguments MReturns_bind {M _ _ _ _}.
Arguments MReturns_bind_inv {M _ _ _ _}.
Arguments MReturns_ret {M _ _ _ _}.
Arguments MReturns_ret_inv {M _ _ _ _}.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Instance ITree_MonadReturns {E} : MonadReturns (itree E)
  := { MReturns := fun A => Returns;
       MReturns_bind := Returns_bind E;
       MReturns_bind_inv := fun A B => Returns_bind_inversion;
       MReturns_ret := fun A => ReturnsRet;
       MReturns_ret_inv := Returns_ret_inv
     }.
