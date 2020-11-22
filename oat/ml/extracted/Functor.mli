
type __ = Obj.t

type 'f coq_Functor =
  __ -> __ -> (__ -> __) -> 'f -> 'f
  (* singleton inductive, whose constructor was Build_Functor *)

val fmap : 'a1 coq_Functor -> ('a2 -> 'a3) -> 'a1 -> 'a1

module FunctorNotation :
 sig
 end
