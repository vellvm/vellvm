open Bool

type 't coq_RelDec =
  't -> 't -> bool
  (* singleton inductive, whose constructor was Build_RelDec *)

(** val rel_dec : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool **)

let rel_dec relDec =
  relDec

(** val eq_dec : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool **)

let eq_dec =
  rel_dec

(** val rel_dec_p : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool **)

let rel_dec_p rD x y =
  bool_dec (rel_dec rD x y) true

(** val neg_rel_dec_p : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool **)

let neg_rel_dec_p rD x y =
  let s = rel_dec_p rD x y in if s then false else true

(** val coq_RelDec_from_dec : ('a1 -> 'a1 -> bool) -> 'a1 coq_RelDec **)

let coq_RelDec_from_dec f a b =
  if f a b then true else false
