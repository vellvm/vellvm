open Datatypes

type ('a, 'b) coq_Fun = 'a -> 'b

(** val apply_Fun : ('a1, 'a2) coq_Fun -> 'a1 -> 'a2 **)

let apply_Fun f =
  f

(** val coq_Id_Fun : ('a1, 'a1) coq_Fun **)

let coq_Id_Fun a =
  a

(** val coq_Cat_Fun :
    ('a1, 'a2) coq_Fun -> ('a2, 'a3) coq_Fun -> ('a1, 'a3) coq_Fun **)

let coq_Cat_Fun f g a =
  g (f a)

(** val coq_Initial_void : (coq_Empty_set, 'a1) coq_Fun **)

let coq_Initial_void _ =
  assert false (* absurd case *)

(** val case_sum :
    ('a1, 'a3) coq_Fun -> ('a2, 'a3) coq_Fun -> (('a1, 'a2) sum, 'a3) coq_Fun **)

let case_sum f g = function
| Coq_inl a -> f a
| Coq_inr b -> g b

(** val sum_inl : ('a1, ('a1, 'a2) sum) coq_Fun **)

let sum_inl x =
  Coq_inl x

(** val sum_inr : ('a2, ('a1, 'a2) sum) coq_Fun **)

let sum_inr x =
  Coq_inr x
