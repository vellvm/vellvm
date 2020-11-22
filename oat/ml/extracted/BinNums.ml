
type positive =
| Coq_xI of positive
| Coq_xO of positive
| Coq_xH

(** val positive_rect :
    (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive
    -> 'a1 **)

let rec positive_rect f f0 f1 = function
| Coq_xI p0 -> f p0 (positive_rect f f0 f1 p0)
| Coq_xO p0 -> f0 p0 (positive_rect f f0 f1 p0)
| Coq_xH -> f1

(** val positive_rec :
    (positive -> 'a1 -> 'a1) -> (positive -> 'a1 -> 'a1) -> 'a1 -> positive
    -> 'a1 **)

let rec positive_rec f f0 f1 = function
| Coq_xI p0 -> f p0 (positive_rec f f0 f1 p0)
| Coq_xO p0 -> f0 p0 (positive_rec f f0 f1 p0)
| Coq_xH -> f1

type coq_N =
| N0
| Npos of positive

(** val coq_N_rect : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1 **)

let coq_N_rect f f0 = function
| N0 -> f
| Npos x -> f0 x

(** val coq_N_rec : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1 **)

let coq_N_rec f f0 = function
| N0 -> f
| Npos x -> f0 x

type coq_Z =
| Z0
| Zpos of positive
| Zneg of positive

(** val coq_Z_rect :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_rect f f0 f1 = function
| Z0 -> f
| Zpos x -> f0 x
| Zneg x -> f1 x

(** val coq_Z_rec :
    'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_rec f f0 f1 = function
| Z0 -> f
| Zpos x -> f0 x
| Zneg x -> f1 x
