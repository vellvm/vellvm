
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'f coq_Functor =
  __ -> __ -> (__ -> __) -> 'f -> 'f
  (* singleton inductive, whose constructor was Build_Functor *)

(** val fmap : 'a1 coq_Functor -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let fmap functor0 x x0 =
  Obj.magic functor0 __ __ x x0

module FunctorNotation =
 struct
 end
