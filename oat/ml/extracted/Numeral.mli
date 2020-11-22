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

val uint_beq : uint -> uint -> bool

val uint_eq_dec : uint -> uint -> bool

val int_beq : int -> int -> bool

val int_eq_dec : int -> int -> bool

val numeral_beq : numeral -> numeral -> bool

val numeral_eq_dec : numeral -> numeral -> bool

val uint_of_uint : uint -> uint

val int_of_int : int -> int
