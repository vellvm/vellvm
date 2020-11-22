open Datatypes
open EitherMonad
open Monad
open MonadExc

type __ = Obj.t

(** val coq_Monad_err : (char list, __) sum coq_Monad **)

let coq_Monad_err =
  coq_Monad_either

(** val coq_Exception_err : (char list, (char list, __) sum) coq_MonadExc **)

let coq_Exception_err =
  coq_Exception_either

(** val trywith :
    'a3 coq_Monad -> ('a1, 'a3) coq_MonadExc -> 'a1 -> 'a2 option -> 'a3 **)

let trywith h h0 e = function
| Some x -> ret h x
| None -> raise h0 e

(** val failwith :
    'a2 coq_Monad -> (char list, 'a2) coq_MonadExc -> char list -> 'a2 **)

let failwith _ =
  raise

type 'b undef = (char list, 'b) sum

type 'a undef_or_err = (char list, (char list, __) sum, 'a) eitherT

(** val coq_Monad_undef_or_err : __ undef_or_err coq_Monad **)

let coq_Monad_undef_or_err =
  coq_Monad_eitherT coq_Monad_err
