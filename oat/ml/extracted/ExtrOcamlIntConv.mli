open BinNums
open Datatypes

val int_of_nat : nat -> int

val int_of_pos : positive -> int

val int_of_z : coq_Z -> int

val int_of_n : coq_N -> int

val int_natlike_rec : 'a1 -> ('a1 -> 'a1) -> int -> 'a1

val nat_of_int : int -> nat

val int_poslike_rec : 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1) -> int -> 'a1

val pos_of_int : int -> positive

val int_zlike_case : 'a1 -> (int -> 'a1) -> (int -> 'a1) -> int -> 'a1

val z_of_int : int -> coq_Z

val n_of_int : int -> coq_N
