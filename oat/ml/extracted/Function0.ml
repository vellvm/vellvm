open Sum

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('e, 'f) coq_IFun = __ -> 'e -> 'f

(** val apply_IFun : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2 **)

let apply_IFun f =
  f __

(** val apply_IFun' : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2 **)

let apply_IFun' f x =
  f __ x

(** val as_IFun : (__ -> 'a1 -> 'a2) -> 'a1 -> 'a2 **)

let as_IFun f x =
  f __ x

(** val coq_Id_IFun : 'a1 -> 'a1 **)

let coq_Id_IFun e =
  e

(** val coq_Cat_IFun :
    ('a1, 'a2) coq_IFun -> ('a2, 'a3) coq_IFun -> 'a1 -> 'a3 **)

let coq_Cat_IFun f1 f2 e =
  f2 __ (f1 __ e)

(** val coq_Initial_void1 : __ -> 'a1 **)

let coq_Initial_void1 _ =
  elim_void1 __

(** val case_sum1 :
    (__ -> 'a1 -> 'a3) -> (__ -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4) sum1 -> 'a3 **)

let case_sum1 f g = function
| Coq_inl1 a -> f __ a
| Coq_inr1 b -> g __ b

(** val coq_Case_sum1 :
    ('a1, 'a3) coq_IFun -> ('a2, 'a3) coq_IFun -> ('a1, 'a2, 'a4) sum1 -> 'a3 **)

let coq_Case_sum1 =
  case_sum1

(** val coq_Inl_sum1 : 'a1 -> ('a1, 'a2, 'a3) sum1 **)

let coq_Inl_sum1 x =
  Coq_inl1 x

(** val coq_Inr_sum1 : 'a2 -> ('a1, 'a2, 'a3) sum1 **)

let coq_Inr_sum1 x =
  Coq_inr1 x
