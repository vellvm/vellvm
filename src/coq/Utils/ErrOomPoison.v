From Vellvm Require Import
  DynamicTypes
  Utils.Error
  Utils.Monads
  Utils.Oomable
  Utils.Poisonable.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.

From Coq Require Import
  String.

Import MonadNotation.

Definition ErrOOMPoison := eitherT ERR_MESSAGE (OomableT Poisonable).

Definition ErrOOMPoison_handle_poison_and_oom {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_OOM M} {A} (poison_handler : dtyp -> A) (ep : ErrOOMPoison A) : M A
  := match unMkOomableT (unEitherT ep) with
     | Unpoisoned edv =>
         match edv with
         (* TODO: Should we use lazy OOM, or should we raise OOM here? *)
         | Oomed dt => raise_oom "ErrOOMPoison_handle_poison_and_oom: OOM."
         | Unoomed (inl (ERR_message msg)) => raise_error msg
         | Unoomed (inr val) => ret val
         end
     | Poison dt => ret (poison_handler dt)
     end.
