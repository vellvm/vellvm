
type 's coq_Monoid = { monoid_plus : ('s -> 's -> 's); monoid_unit : 's }

val monoid_plus : 'a1 coq_Monoid -> 'a1 -> 'a1 -> 'a1

val monoid_unit : 'a1 coq_Monoid -> 'a1
