From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads
     Structures.MonadExc
     Data.Monads.EitherMonad.

From Vellvm.Utils Require Import Error.

(* TODO: move these and use them in more places, so I'm less
       confused by what string is which, e.g., in undef_or_err *)
Inductive UB_MESSAGE :=
| UB_message : string -> UB_MESSAGE
.

Inductive ERR_MESSAGE :=
| ERR_message : string -> ERR_MESSAGE
.

Notation UB := (sum UB_MESSAGE).
Notation ERR := (sum ERR_MESSAGE).

Instance Exception_UB : MonadExc UB_MESSAGE UB := Exception_either UB_MESSAGE.
Instance Exception_ERR : MonadExc ERR_MESSAGE ERR := Exception_either ERR_MESSAGE.

Class VErrorM (M : Type -> Type) : Type :=
  { raise_error : forall {A}, string -> M A }.

Class UBM (M : Type -> Type) : Type :=
  { raise_ub : forall {A}, string -> M A }.

#[global] Instance VErrorM_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{VErrorM M} : VErrorM (MT M) :=
  { raise_error := fun A e => lift (raise_error e);
  }.

#[global] Instance UBM_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{UBM M} : UBM (MT M) :=
  { raise_ub := fun A e => lift (raise_ub e);
  }.

#[global] Instance VErrorM_MonadExc {M} `{MonadExc ERR_MESSAGE M} : VErrorM M
  := { raise_error := fun _ msg => MonadExc.raise (ERR_message msg) }.

#[global] Instance UBM_MonadExc {M} `{MonadExc UB_MESSAGE M} : UBM M
  := { raise_ub := fun _ msg => MonadExc.raise (UB_message msg) }.

Instance Exception_UB_string : MonadExc string UB :=
  {| MonadExc.raise := fun _ msg => inl (UB_message msg);
     catch := fun T c h =>
                match c with
                | inl (UB_message msg) => h msg
                | inr _ => c
                end
  |}.

Instance Exception_ERR_string : MonadExc string ERR :=
  {| MonadExc.raise := fun _ msg => inl (ERR_message msg);
     catch := fun T c h =>
                match c with
                | inl (ERR_message msg) => h msg
                | inr _ => c
                end
  |}.

Definition err_to_ERR {A} (e : err A) : ERR A
  := match e with
     | inl e => inl (ERR_message e)
     | inr x => inr x
     end.

Definition lift_err {M A} `{MonadExc string M} `{Monad M} (e : err A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.

Definition lift_ERR {M A} `{MonadExc ERR_MESSAGE M} `{Monad M} (e : ERR A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.
