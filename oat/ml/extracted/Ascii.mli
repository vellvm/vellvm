open BinNat
open BinNums
open Bool
open Datatypes

val ascii_rect :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  char -> 'a1

val ascii_rec :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  char -> 'a1

val zero : char

val one : char

val shift : bool -> char -> char

val eqb_spec : char -> char -> reflect

val ascii_of_pos : positive -> char

val ascii_of_N : coq_N -> char

val ascii_of_nat : nat -> char

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : char -> coq_N

val nat_of_ascii : char -> nat

module AsciiSyntax :
 sig
 end

val coq_Space : char

val coq_DoubleQuote : char

val coq_Beep : char
