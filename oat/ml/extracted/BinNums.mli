
type positive =
| Coq_xI of positive
| Coq_xO of positive
| Coq_xH

val positive_rect :
  (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive ->
  'a1

val positive_rec :
  (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive ->
  'a1

type coq_N =
| N0
| Npos of positive

val coq_N_rect : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1

val coq_N_rec : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1

type coq_Z =
| Z0
| Zpos of positive
| Zneg of positive

val coq_Z_rect : 'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1

val coq_Z_rec : 'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1
