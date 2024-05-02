From Coq Require Import
     String
     Morphisms.

From ExtLib Require Import
     Structures.Monads.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Eq
     ITree.

From Vellvm Require Import 
  Utils.Tactics.

Require Import Coq.Program.Equality.

Require Import Paco.paco.

Section Laws.
  Variable M : Type -> Type.
  Context `{HM : Monad M}.
  Context `{EQM : Eq1 M}.
  Variable MSG : Type.
  Variable rbm_raise : forall {X}, MSG -> M X.

  Class RaiseBindM :=
    { rbm_raise_bind :
      forall A B (f : A -> M B) (x : MSG),
        eq1 (bind (rbm_raise x) f) (rbm_raise x);
      rbm_raise_ret_inv :
      forall A (x : MSG) (y : A),
        ~ eq1 (rbm_raise x) (ret y);
    }.
End Laws.

