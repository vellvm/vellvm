open Datatypes

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val uint_rect :
  'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1)
  -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> uint -> 'a1

val uint_rec :
  'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1)
  -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> uint -> 'a1

type int =
| Pos of uint
| Neg of uint

type decimal =
| Decimal of int * uint
| DecimalExp of int * uint * int

val uint_beq : uint -> uint -> bool

val uint_eq_dec : uint -> uint -> bool

val int_beq : int -> int -> bool

val int_eq_dec : int -> int -> bool

val decimal_beq : decimal -> decimal -> bool

val decimal_eq_dec : decimal -> decimal -> bool

val nb_digits : uint -> nat

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : int -> int

val opp : int -> int

val revapp : uint -> uint -> uint

val rev : uint -> uint

val app : uint -> uint -> uint

val app_int : int -> uint -> int

val nztail : uint -> uint * nat

val nztail_int : int -> int * nat

val del_head : nat -> uint -> uint

val del_head_int : nat -> int -> uint

val del_tail : nat -> uint -> uint

val del_tail_int : nat -> int -> int

module Little :
 sig
  val succ : uint -> uint

  val double : uint -> uint

  val succ_double : uint -> uint
 end

val uint_of_uint : uint -> uint

val int_of_int : int -> int
