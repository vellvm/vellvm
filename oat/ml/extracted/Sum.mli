
type __ = Obj.t

type ('e1, 'e2, 'x) sum1 =
| Coq_inl1 of 'e1
| Coq_inr1 of 'e2

val elim_void1 : __ -> 'a1
