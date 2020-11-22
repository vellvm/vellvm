
type 's coq_Monoid = { monoid_plus : ('s -> 's -> 's); monoid_unit : 's }

(** val monoid_plus : 'a1 coq_Monoid -> 'a1 -> 'a1 -> 'a1 **)

let monoid_plus m =
  m.monoid_plus

(** val monoid_unit : 'a1 coq_Monoid -> 'a1 **)

let monoid_unit m =
  m.monoid_unit
