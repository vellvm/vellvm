
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_True_rect : 'a1 -> 'a1 **)

let coq_True_rect f =
  f

(** val coq_True_rec : 'a1 -> 'a1 **)

let coq_True_rec f =
  f

(** val coq_False_rect : __ -> 'a1 **)

let coq_False_rect _ =
  assert false (* absurd case *)

(** val coq_False_rec : __ -> 'a1 **)

let coq_False_rec _ =
  assert false (* absurd case *)

(** val and_rect : (__ -> __ -> 'a1) -> 'a1 **)

let and_rect f =
  f __ __

(** val and_rec : (__ -> __ -> 'a1) -> 'a1 **)

let and_rec f =
  f __ __

(** val eq_rect : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rect _ f _ =
  f

(** val eq_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rec _ f _ =
  f

(** val eq_rec_r : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rec_r _ h _ =
  h

(** val eq_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rect_r _ h _ =
  h

module EqNotations =
 struct
 end
