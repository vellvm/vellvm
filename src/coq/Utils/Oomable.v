From Vellvm Require Import
  DynamicTypes
  Utils.Error
  Utils.Monads.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.

Import MonadNotation.

Inductive Oomable (A : Type) : Type :=
| Unoomed : A -> Oomable A
| Oomed : forall (dt : dtyp), Oomable A
.

Arguments Unoomed {A} a.
Arguments Oomed {A}.

#[global] Instance MonadOomable : Monad Oomable
  := { ret  := @Unoomed;
       bind := fun _ _ ma mab => match ma with
                              | Oomed dt => Oomed dt
                              | Unoomed v => mab v
                              end
  }.

Class RAISE_OOMABLE (M : Type -> Type) :=
  { raise_oomable : forall {A}, dtyp -> M A }.

#[global] Instance RAISE_OOMABLE_Oomable : RAISE_OOMABLE Oomable :=
  { raise_oomable := fun A dt => Oomed dt }.

#[global] Instance RAISE_OOMABLE_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_OOMABLE M} : RAISE_OOMABLE (MT M) :=
  { raise_oomable := fun A dt => lift (raise_oomable dt);
  }.

Inductive OomableT (m : Type -> Type) (A : Type) : Type :=
  mkOomableT
    { unMkOomableT : m (Oomable A)
    }.

Arguments mkOomableT {m A}.
Arguments unMkOomableT {m A}.

#[global] Instance MonadT_OomableT (m : Type -> Type) `{Monad m} : MonadT (OomableT m) m :=
  { lift := fun T c => mkOomableT (liftM ret c) }.

Definition lift_OOMABLE {M : Type -> Type} `{Monad M} `{RAISE_OOMABLE M} {A} (dt : dtyp) (ma : OOM A) : M A
  := match ma with
     | NoOom a => ret a
     | Oom s => raise_oomable dt
     end.

#[global] Instance Monad_OomableT (m : Type -> Type) `{Monad m} : Monad (OomableT m) :=
  {
    ret := fun T x => mkOomableT (ret (Unoomed x));
    bind := fun A B ma mab =>
              mkOomableT
                (oom_a <- unMkOomableT ma;;
                 match oom_a with
                 | Oomed dt =>
                     ret (Oomed dt)
                 | Unoomed a =>
                     unMkOomableT (mab a)
                 end
                )
  }.

#[global] Instance RAISE_OOMABLE_OomableT m `{Monad m} : RAISE_OOMABLE (OomableT m) :=
  { raise_oomable := fun A dt => mkOomableT (ret (Oomed dt)) }.
