
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('m, 'mt) coq_MonadT =
  __ -> 'mt -> 'm
  (* singleton inductive, whose constructor was Build_MonadT *)

(** val lift : ('a1, 'a2) coq_MonadT -> 'a2 -> 'a1 **)

let lift monadT x =
  monadT __ x
