
type __ = Obj.t

val coq_Acc_rect : ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val coq_Acc_rec : ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val well_founded_induction_type :
  ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val well_founded_induction : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val coq_Fix_F : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val coq_Fix : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val coq_Fix_F_2 :
  ('a1 -> 'a2 -> ('a1 -> 'a2 -> __ -> 'a3) -> 'a3) -> 'a1 -> 'a2 -> 'a3

val well_founded_induction_type_2 :
  ('a1 -> 'a2 -> ('a1 -> 'a2 -> __ -> 'a3) -> 'a3) -> 'a1 -> 'a2 -> 'a3
