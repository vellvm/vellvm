From Vellvm.Utils Require Import
     Monads.

From ExtLib Require Import
     Structures.Monads.

From Coq Require Import
     Relations
     RelationClasses
     Morphisms.

Import Monad.
Import MonadNotation.
Open Scope monad_scope.

(* Whether a monadic computation M contains something in B *)
Class Within {M : Type -> Type} `{EQM : Eq1 M} (B : Type -> Type) (PreState PostState : Type) : Type :=
  { within {A} (m : M A) (pre : PreState) (b : B A) (post : PostState) : Prop;
    within_eq1_Proper {A} :>
      Proper (@eq1 M EQM A ==> eq ==> eq ==> eq ==> iff) within;
  }.

Notation "b ∈ m" := (exists pre post, within m pre b post) (at level 99).
Notation "b ∉ m" := (~ (exists pre post, within m pre b post)) (at level 99).
Notation "b ⦉ pre ⦊ ∈ ⦉ post ⦊ m" := (within m pre b post) (at level 99).
Notation "b ⦉ pre ⦊ ∉ ⦉ post ⦊ m" := (~ (within m pre b post)) (at level 99).
Notation "b {{ pre }} ∈ {{ post }} m" := (within m pre b post) (at level 99).
Notation "b {{ pre }} ∉ {{ post }} m" := (~ (within m pre b post)) (at level 99).    

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable rw_raise : forall {X}, MSG -> M X.

  Class RaiseWithin :=
    { rw_ret_nin_raise :
      forall X (msg : MSG) (x : X),
        @ret B HMB X x ∉ @rw_raise X msg;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable rw_raise : forall {X}, MSG -> B X.

  Class RetWithin :=
    { rw_raise_nin_ret :
      forall X (msg : MSG) (x : X),
        @rw_raise X msg ∉ ret x;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable raise1 : forall {X}, MSG -> B X.
  Variable raise2 : forall {X}, MSG -> M X.

  Class DisjointRaiseWithin :=
    { disjoint_raise_within :
      forall X (msg1 msg2 : MSG),
        @raise1 X msg1 ∉ @raise2 X msg2;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.

  Class Within_ret_inv : Prop :=
    { within_ret_ret : forall {A} (x y : A), ret x ∈ ret y -> x = y;
      within_ret_refl : forall {A} (x : A), ret x ∈ ret x;
    }.
End Laws.
