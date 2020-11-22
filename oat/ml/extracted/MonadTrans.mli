
type __ = Obj.t

type ('m, 'mt) coq_MonadT =
  __ -> 'mt -> 'm
  (* singleton inductive, whose constructor was Build_MonadT *)

val lift : ('a1, 'a2) coq_MonadT -> 'a2 -> 'a1
