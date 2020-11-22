open Monad

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_MonadZero =
  __ -> 'm
  (* singleton inductive, whose constructor was Build_MonadZero *)

(** val mzero : 'a1 coq_MonadZero -> 'a1 **)

let mzero monadZero =
  monadZero __

(** val coq_assert : 'a1 coq_Monad -> 'a1 coq_MonadZero -> bool -> 'a1 **)

let coq_assert monad_m zero_m = function
| true -> ret monad_m ()
| false -> mzero zero_m
