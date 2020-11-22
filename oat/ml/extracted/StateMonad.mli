open Datatypes
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

type ('s, 't) state =
  's -> 't * 's
  (* singleton inductive, whose constructor was mkState *)

val runState : ('a1, 'a2) state -> 'a1 -> 'a2 * 'a1

val evalState : ('a1, 'a2) state -> 'a1 -> 'a2

val execState : ('a1, 'a2) state -> 'a1 -> 'a1

val coq_Monad_state : ('a1, __) state coq_Monad

val coq_MonadState_state : ('a1, ('a1, __) state) coq_MonadState

type ('s, 'm, 't) stateT =
  's -> 'm
  (* singleton inductive, whose constructor was mkStateT *)

val runStateT : ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2

val evalStateT : 'a2 coq_Monad -> ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2

val execStateT : 'a2 coq_Monad -> ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2

val coq_Monad_stateT : 'a2 coq_Monad -> ('a1, 'a2, __) stateT coq_Monad

val coq_MonadState_stateT :
  'a2 coq_Monad -> ('a1, ('a1, 'a2, __) stateT) coq_MonadState

val coq_MonadT_stateT :
  'a2 coq_Monad -> (('a1, 'a2, __) stateT, 'a2) coq_MonadT

val coq_State_State_stateT :
  'a2 coq_Monad -> ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __) stateT)
  coq_MonadState

val coq_MonadReader_stateT :
  'a2 coq_Monad -> ('a3, 'a2) coq_MonadReader -> ('a3, ('a1, 'a2, __) stateT)
  coq_MonadReader

val coq_MonadWriter_stateT :
  'a2 coq_Monad -> 'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3,
  ('a1, 'a2, __) stateT) coq_MonadWriter

val coq_Exc_stateT :
  'a2 coq_Monad -> ('a3, 'a2) coq_MonadExc -> ('a3, ('a1, 'a2, __) stateT)
  coq_MonadExc

val coq_MonadZero_stateT :
  'a2 coq_Monad -> 'a2 coq_MonadZero -> ('a1, 'a2, __) stateT coq_MonadZero

val coq_MonadFix_stateT :
  'a2 coq_MonadFix -> ('a1, 'a2, __) stateT coq_MonadFix

val coq_MonadPlus_stateT :
  'a2 coq_Monad -> 'a2 coq_MonadPlus -> ('a1, 'a2, __) stateT coq_MonadPlus
