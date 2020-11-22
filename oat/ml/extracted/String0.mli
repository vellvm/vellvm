open Ascii
open Bool
open Datatypes
open List0

val string_rect :
  'a1 -> (char -> char list -> 'a1 -> 'a1) -> char list -> 'a1

val string_rec : 'a1 -> (char -> char list -> 'a1 -> 'a1) -> char list -> 'a1

val string_dec : char list -> char list -> bool

val eqb : char list -> char list -> bool

val eqb_spec : char list -> char list -> reflect

val append : char list -> char list -> char list

val length : char list -> nat

val get : nat -> char list -> char option

val substring : nat -> nat -> char list -> char list

val concat : char list -> char list list -> char list

val prefix : char list -> char list -> bool

val index : nat -> char list -> char list -> nat option

val findex : nat -> char list -> char list -> nat

val string_of_list_ascii : char list -> char list

val list_ascii_of_string : char list -> char list

val string_of_list_byte : char list -> char list

val list_byte_of_string : char list -> char list

module StringSyntax :
 sig
 end

val coq_HelloWorld : char list
