
type __ = Obj.t

val coq_True_rect : 'a1 -> 'a1

val coq_True_rec : 'a1 -> 'a1

val coq_False_rect : __ -> 'a1

val coq_False_rec : __ -> 'a1

val and_rect : (__ -> __ -> 'a1) -> 'a1

val and_rec : (__ -> __ -> 'a1) -> 'a1

val eq_rect : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rec : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rec_r : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a2

module EqNotations :
 sig
 end
