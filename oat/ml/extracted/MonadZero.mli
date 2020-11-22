open Monad

type __ = Obj.t

type 'm coq_MonadZero =
  __ -> 'm
  (* singleton inductive, whose constructor was Build_MonadZero *)

val mzero : 'a1 coq_MonadZero -> 'a1

val coq_assert : 'a1 coq_Monad -> 'a1 coq_MonadZero -> bool -> 'a1
