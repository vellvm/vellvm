open Datatypes

(** val zerop : nat -> bool **)

let zerop = function
| O -> true
| S _ -> false

(** val lt_eq_lt_dec : nat -> nat -> bool option **)

let rec lt_eq_lt_dec n m =
  match n with
  | O -> (match m with
          | O -> Some false
          | S _ -> Some true)
  | S n0 -> (match m with
             | O -> None
             | S m0 -> lt_eq_lt_dec n0 m0)

(** val gt_eq_gt_dec : nat -> nat -> bool option **)

let gt_eq_gt_dec =
  lt_eq_lt_dec

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
  | O -> true
  | S n0 -> (match m with
             | O -> false
             | S m0 -> le_lt_dec n0 m0)

(** val le_le_S_dec : nat -> nat -> bool **)

let le_le_S_dec =
  le_lt_dec

(** val le_ge_dec : nat -> nat -> bool **)

let le_ge_dec =
  le_lt_dec

(** val le_gt_dec : nat -> nat -> bool **)

let le_gt_dec =
  le_lt_dec

(** val le_lt_eq_dec : nat -> nat -> bool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Some s0 -> s0
   | None -> assert false (* absurd case *))

(** val le_dec : nat -> nat -> bool **)

let le_dec =
  le_gt_dec

(** val lt_dec : nat -> nat -> bool **)

let lt_dec n m =
  le_dec (S n) m

(** val gt_dec : nat -> nat -> bool **)

let gt_dec n m =
  lt_dec m n

(** val ge_dec : nat -> nat -> bool **)

let ge_dec n m =
  le_dec m n

(** val nat_compare_alt : nat -> nat -> comparison **)

let nat_compare_alt n m =
  match lt_eq_lt_dec n m with
  | Some s -> if s then Lt else Eq
  | None -> Gt
