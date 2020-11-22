open Datatypes

type __ = Obj.t

type 'm coq_MonadFix =
  __ -> __ -> ((__ -> 'm) -> __ -> 'm) -> __ -> 'm
  (* singleton inductive, whose constructor was Build_MonadFix *)

val mfix : 'a1 coq_MonadFix -> (('a2 -> 'a1) -> 'a2 -> 'a1) -> 'a2 -> 'a1

type 'r ftype = __

type tuple = __

val wrap : __ list -> (tuple -> 'a1) -> 'a1 ftype

val apply : __ list -> 'a1 ftype -> tuple -> 'a1

val mfix_multi :
  'a1 coq_MonadFix -> __ list -> ('a1 ftype -> 'a1 ftype) -> 'a1 ftype

val mfix2 :
  'a1 coq_MonadFix -> (('a2 -> 'a3 -> 'a1) -> 'a2 -> 'a3 -> 'a1) -> 'a2 ->
  'a3 -> 'a1

val mfix3 :
  'a1 coq_MonadFix -> (('a2 -> 'a3 -> 'a4 -> 'a1) -> 'a2 -> 'a3 -> 'a4 ->
  'a1) -> 'a2 -> 'a3 -> 'a4 -> 'a1
