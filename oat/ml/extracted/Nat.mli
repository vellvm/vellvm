open Datatypes
open Decimal
open Hexadecimal
open Numeral

type t = nat

val zero : nat

val one : nat

val two : nat

val succ : nat -> nat

val pred : nat -> nat

val add : nat -> nat -> nat

val double : nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : nat -> nat -> bool

val leb : nat -> nat -> bool

val ltb : nat -> nat -> bool

val compare : nat -> nat -> comparison

val max : nat -> nat -> nat

val min : nat -> nat -> nat

val even : nat -> bool

val odd : nat -> bool

val pow : nat -> nat -> nat

val tail_add : nat -> nat -> nat

val tail_addmul : nat -> nat -> nat -> nat

val tail_mul : nat -> nat -> nat

val of_uint_acc : Decimal.uint -> nat -> nat

val of_uint : Decimal.uint -> nat

val of_hex_uint_acc : Hexadecimal.uint -> nat -> nat

val of_hex_uint : Hexadecimal.uint -> nat

val of_num_uint : uint -> nat

val to_little_uint : nat -> Decimal.uint -> Decimal.uint

val to_uint : nat -> Decimal.uint

val to_little_hex_uint : nat -> Hexadecimal.uint -> Hexadecimal.uint

val to_hex_uint : nat -> Hexadecimal.uint

val to_num_uint : nat -> uint

val to_num_hex_uint : nat -> uint

val of_int : Decimal.int -> nat option

val of_hex_int : Hexadecimal.int -> nat option

val of_num_int : int -> nat option

val to_int : nat -> Decimal.int

val to_hex_int : nat -> Hexadecimal.int

val to_num_int : nat -> int

val divmod : nat -> nat -> nat -> nat -> nat * nat

val div : nat -> nat -> nat

val modulo : nat -> nat -> nat

val gcd : nat -> nat -> nat

val square : nat -> nat

val sqrt_iter : nat -> nat -> nat -> nat -> nat

val sqrt : nat -> nat

val log2_iter : nat -> nat -> nat -> nat -> nat

val log2 : nat -> nat

val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

val div2 : nat -> nat

val testbit : nat -> nat -> bool

val shiftl : nat -> nat -> nat

val shiftr : nat -> nat -> nat

val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

val coq_land : nat -> nat -> nat

val coq_lor : nat -> nat -> nat

val ldiff : nat -> nat -> nat

val coq_lxor : nat -> nat -> nat
