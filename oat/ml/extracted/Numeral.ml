open Decimal
open Hexadecimal

type uint =
| UIntDec of Decimal.uint
| UIntHex of Hexadecimal.uint

type int =
| IntDec of Decimal.int
| IntHex of Hexadecimal.int

type numeral =
| Dec of decimal
| Hex of hexadecimal

(** val uint_beq : uint -> uint -> bool **)

let uint_beq x y =
  match x with
  | UIntDec u ->
    (match y with
     | UIntDec u0 -> Decimal.uint_beq u u0
     | UIntHex _ -> false)
  | UIntHex u ->
    (match y with
     | UIntDec _ -> false
     | UIntHex u0 -> uint_beq u u0)

(** val uint_eq_dec : uint -> uint -> bool **)

let uint_eq_dec x y =
  let b = uint_beq x y in if b then true else false

(** val int_beq : int -> int -> bool **)

let int_beq x y =
  match x with
  | IntDec i ->
    (match y with
     | IntDec i0 -> Decimal.int_beq i i0
     | IntHex _ -> false)
  | IntHex i -> (match y with
                 | IntDec _ -> false
                 | IntHex i0 -> int_beq i i0)

(** val int_eq_dec : int -> int -> bool **)

let int_eq_dec x y =
  let b = int_beq x y in if b then true else false

(** val numeral_beq : numeral -> numeral -> bool **)

let numeral_beq x y =
  match x with
  | Dec d -> (match y with
              | Dec d0 -> decimal_beq d d0
              | Hex _ -> false)
  | Hex h -> (match y with
              | Dec _ -> false
              | Hex h0 -> hexadecimal_beq h h0)

(** val numeral_eq_dec : numeral -> numeral -> bool **)

let numeral_eq_dec x y =
  let b = numeral_beq x y in if b then true else false

(** val uint_of_uint : uint -> uint **)

let uint_of_uint i =
  i

(** val int_of_int : int -> int **)

let int_of_int i =
  i
