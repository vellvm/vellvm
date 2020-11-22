
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

(** val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2 **)

let raise monadExc x =
  monadExc.raise __ x

(** val catch : ('a1, 'a2) coq_MonadExc -> 'a2 -> ('a1 -> 'a2) -> 'a2 **)

let catch monadExc x x0 =
  monadExc.catch __ x x0
