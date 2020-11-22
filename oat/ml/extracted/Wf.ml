
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Acc_rect :
    ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Acc_rect f x =
  f x __ (fun y _ -> coq_Acc_rect f y)

(** val coq_Acc_rec :
    ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Acc_rec f x =
  f x __ (fun y _ -> coq_Acc_rec f y)

(** val well_founded_induction_type :
    ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec well_founded_induction_type x a =
  x a (fun y _ -> well_founded_induction_type x y)

(** val well_founded_induction :
    ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec well_founded_induction x a =
  x a (fun y _ -> well_founded_induction x y)

(** val coq_Fix_F : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix_F f x =
  f x (fun y _ -> coq_Fix_F f y)

(** val coq_Fix : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix f x =
  f x (fun y _ -> coq_Fix f y)

(** val coq_Fix_F_2 :
    ('a1 -> 'a2 -> ('a1 -> 'a2 -> __ -> 'a3) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let rec coq_Fix_F_2 f x x' =
  f x x' (fun y y' _ -> coq_Fix_F_2 f y y')

(** val well_founded_induction_type_2 :
    ('a1 -> 'a2 -> ('a1 -> 'a2 -> __ -> 'a3) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let well_founded_induction_type_2 =
  coq_Fix_F_2
