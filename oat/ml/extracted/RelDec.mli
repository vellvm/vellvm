open Bool

type 't coq_RelDec =
  't -> 't -> bool
  (* singleton inductive, whose constructor was Build_RelDec *)

val rel_dec : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool

val eq_dec : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool

val rel_dec_p : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool

val neg_rel_dec_p : 'a1 coq_RelDec -> 'a1 -> 'a1 -> bool

val coq_RelDec_from_dec : ('a1 -> 'a1 -> bool) -> 'a1 coq_RelDec
