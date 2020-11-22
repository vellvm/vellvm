open Monad
open MonadExc
open MonadFix
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadWriter
open MonadZero
open Monoid

type __ = Obj.t

type ('s, 't) reader =
  's -> 't
  (* singleton inductive, whose constructor was mkReader *)

val runReader : ('a1, 'a2) reader -> 'a1 -> 'a2

val coq_Monad_reader : ('a1, __) reader coq_Monad

val coq_MonadReader_reader : ('a1, ('a1, __) reader) coq_MonadReader

type ('s, 'm, 't) readerT =
  's -> 'm
  (* singleton inductive, whose constructor was mkReaderT *)

val runReaderT : ('a1, 'a2, 'a3) readerT -> 'a1 -> 'a2

val coq_Monad_readerT : 'a2 coq_Monad -> ('a1, 'a2, __) readerT coq_Monad

val coq_MonadReader_readerT :
  'a2 coq_Monad -> ('a1, ('a1, 'a2, __) readerT) coq_MonadReader

val coq_MonadT_readerT : (('a1, 'a2, __) readerT, 'a2) coq_MonadT

val coq_MonadZero_readerT :
  'a2 coq_MonadZero -> ('a1, 'a2, __) readerT coq_MonadZero

val coq_MonadState_readerT :
  ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __) readerT) coq_MonadState

val coq_MonadWriter_readerT :
  'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3, ('a1, 'a2, __)
  readerT) coq_MonadWriter

val coq_MonadExc_readerT :
  ('a3, 'a2) coq_MonadExc -> ('a3, ('a1, 'a2, __) readerT) coq_MonadExc

val coq_MonadPlus_readerT :
  'a2 coq_MonadPlus -> ('a1, 'a2, __) readerT coq_MonadPlus

val coq_MonadFix_readerT :
  'a2 coq_MonadFix -> ('a1, 'a2, __) readerT coq_MonadFix

val coq_MonadReader_lift_readerT :
  ('a1, 'a3) coq_MonadReader -> ('a1, ('a2, 'a3, __) readerT) coq_MonadReader
