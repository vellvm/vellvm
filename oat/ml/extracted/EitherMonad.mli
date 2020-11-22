open Datatypes
open Monad
open MonadExc
open MonadFix
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadWriter
open Monoid

type __ = Obj.t

val coq_Monad_either : ('a1, __) sum coq_Monad

val coq_Exception_either : ('a1, ('a1, __) sum) coq_MonadExc

type ('t, 'm, 'a) eitherT =
  'm
  (* singleton inductive, whose constructor was mkEitherT *)

val eitherT_rect : ('a2 -> 'a4) -> ('a1, 'a2, 'a3) eitherT -> 'a4

val eitherT_rec : ('a2 -> 'a4) -> ('a1, 'a2, 'a3) eitherT -> 'a4

val unEitherT : ('a1, 'a2, 'a3) eitherT -> 'a2

val coq_Monad_eitherT : 'a2 coq_Monad -> ('a1, 'a2, __) eitherT coq_Monad

val coq_Exception_eitherT :
  'a2 coq_Monad -> ('a1, ('a1, 'a2, __) eitherT) coq_MonadExc

val coq_MonadPlus_eitherT :
  'a2 coq_Monad -> ('a1, 'a2, __) eitherT coq_MonadPlus

val coq_MonadT_eitherT :
  'a2 coq_Monad -> (('a1, 'a2, __) eitherT, 'a2) coq_MonadT

val coq_MonadState_eitherT :
  'a2 coq_Monad -> ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __) eitherT)
  coq_MonadState

val coq_MonadReader_eitherT :
  'a2 coq_Monad -> ('a3, 'a2) coq_MonadReader -> ('a3, ('a1, 'a2, __)
  eitherT) coq_MonadReader

val coq_MonadWriter_eitherT :
  'a2 coq_Monad -> 'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3,
  ('a1, 'a2, __) eitherT) coq_MonadWriter

val coq_MonadFix_eitherT :
  'a2 coq_MonadFix -> ('a1, 'a2, __) eitherT coq_MonadFix
