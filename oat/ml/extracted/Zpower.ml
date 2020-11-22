open BinInt
open BinNums
open BinPos
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Zpower_nat : coq_Z -> nat -> coq_Z **)

let rec coq_Zpower_nat z = function
| O -> Zpos Coq_xH
| S n0 -> Z.mul z (coq_Zpower_nat z n0)

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n z =
  match n with
  | O -> z
  | S n0 -> Coq_xO (shift_nat n0 z)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n z =
  Pos.iter (fun x -> Coq_xO x) z n

(** val shift : coq_Z -> positive -> positive **)

let shift n z =
  match n with
  | Zpos p -> Pos.iter (fun x -> Coq_xO x) z p
  | _ -> z

(** val two_power_nat : nat -> coq_Z **)

let two_power_nat n =
  Zpos (shift_nat n Coq_xH)

(** val two_power_pos : positive -> coq_Z **)

let two_power_pos x =
  Zpos (shift_pos x Coq_xH)

(** val two_p : coq_Z -> coq_Z **)

let two_p = function
| Z0 -> Zpos Coq_xH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val coq_Zdiv_rest_aux :
    ((coq_Z * coq_Z) * coq_Z) -> (coq_Z * coq_Z) * coq_Z **)

let coq_Zdiv_rest_aux = function
| (p, d) ->
  let (q, r) = p in
  ((match q with
    | Z0 -> (Z0, r)
    | Zpos p0 ->
      (match p0 with
       | Coq_xI n -> ((Zpos n), (Z.add d r))
       | Coq_xO n -> ((Zpos n), r)
       | Coq_xH -> (Z0, (Z.add d r)))
    | Zneg p0 ->
      (match p0 with
       | Coq_xI n -> ((Z.sub (Zneg n) (Zpos Coq_xH)), (Z.add d r))
       | Coq_xO n -> ((Zneg n), r)
       | Coq_xH -> ((Zneg Coq_xH), (Z.add d r)))),
  (Z.mul (Zpos (Coq_xO Coq_xH)) d))

(** val coq_Zdiv_rest : coq_Z -> positive -> coq_Z * coq_Z **)

let coq_Zdiv_rest x p =
  let (qr, _) = Pos.iter coq_Zdiv_rest_aux ((x, Z0), (Zpos Coq_xH)) p in qr

type coq_Zdiv_rest_proofs =
| Zdiv_rest_proof of coq_Z * coq_Z

(** val coq_Zdiv_rest_proofs_rect :
    coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
    coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rect _ _ f = function
| Zdiv_rest_proof (x, x0) -> f x x0 __ __ __

(** val coq_Zdiv_rest_proofs_rec :
    coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
    coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rec _ _ f = function
| Zdiv_rest_proof (x, x0) -> f x x0 __ __ __

(** val coq_Zdiv_rest_correct : coq_Z -> positive -> coq_Zdiv_rest_proofs **)

let coq_Zdiv_rest_correct x p =
  let p0 = Pos.iter coq_Zdiv_rest_aux ((x, Z0), (Zpos Coq_xH)) p in
  let (p1, _) = p0 in let (q, r) = p1 in Zdiv_rest_proof (q, r)
