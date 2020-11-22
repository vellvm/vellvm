open Datatypes

type ('a, 'b) coq_Fun = 'a -> 'b

val apply_Fun : ('a1, 'a2) coq_Fun -> 'a1 -> 'a2

val coq_Id_Fun : ('a1, 'a1) coq_Fun

val coq_Cat_Fun :
  ('a1, 'a2) coq_Fun -> ('a2, 'a3) coq_Fun -> ('a1, 'a3) coq_Fun

val coq_Initial_void : (coq_Empty_set, 'a1) coq_Fun

val case_sum :
  ('a1, 'a3) coq_Fun -> ('a2, 'a3) coq_Fun -> (('a1, 'a2) sum, 'a3) coq_Fun

val sum_inl : ('a1, ('a1, 'a2) sum) coq_Fun

val sum_inr : ('a2, ('a1, 'a2) sum) coq_Fun
