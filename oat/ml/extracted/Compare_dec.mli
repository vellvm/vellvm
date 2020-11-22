open Datatypes

val zerop : nat -> bool

val lt_eq_lt_dec : nat -> nat -> bool option

val gt_eq_gt_dec : nat -> nat -> bool option

val le_lt_dec : nat -> nat -> bool

val le_le_S_dec : nat -> nat -> bool

val le_ge_dec : nat -> nat -> bool

val le_gt_dec : nat -> nat -> bool

val le_lt_eq_dec : nat -> nat -> bool

val le_dec : nat -> nat -> bool

val lt_dec : nat -> nat -> bool

val gt_dec : nat -> nat -> bool

val ge_dec : nat -> nat -> bool

val nat_compare_alt : nat -> nat -> comparison
