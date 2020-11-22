open Datatypes
open EitherMonad
open Functor
open Monad
open OptionMonad
open ReaderMonad
open StateMonad

type __ = Obj.t

val idM : 'a1 -> 'a1

module Monads :
 sig
  type 'a identity = 'a

  type ('s, 'm, 'a) stateT = 's -> 'm

  type ('s, 'a) state = 's -> 's * 'a

  type ('r, 'm, 'a) readerT = 'r -> 'm

  type ('r, 'a) reader = 'r -> 'a

  type ('w, 'm, 'a) writerT = 'm

  type ('a, 'b) writer = 'a * 'b

  val coq_Functor_stateT :
    'a1 coq_Functor -> ('a2, 'a1, __) stateT coq_Functor

  val coq_Monad_stateT : 'a1 coq_Monad -> ('a2, 'a1, __) stateT coq_Monad
 end

type 'm coq_MonadIter = __ -> __ -> (__ -> 'm) -> __ -> 'm

val iter : 'a1 coq_MonadIter -> ('a3 -> 'a1) -> 'a3 -> 'a1

val coq_MonadIter_stateT :
  'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
  stateT) -> 'a4 -> ('a2, 'a1, 'a3) stateT

val coq_MonadIter_stateT0 :
  'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
  Monads.stateT) -> 'a4 -> ('a2, 'a1, 'a3) Monads.stateT

val coq_MonadIter_readerT :
  'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum) readerT) -> 'a4 ->
  ('a2, 'a1, 'a3) readerT

val coq_MonadIter_optionT :
  'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a3 -> ('a1, ('a3, 'a2) sum)
  optionT) -> 'a3 -> ('a1, 'a2) optionT

val coq_MonadIter_eitherT :
  'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
  eitherT) -> 'a4 -> ('a2, 'a1, 'a3) eitherT
