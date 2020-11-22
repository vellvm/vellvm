open BinInt
open BinNums
open Datatypes
open Sumbool

type __ = Obj.t

val coq_Dcompare_inf : comparison -> bool option

val coq_Zcompare_rect :
  coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val coq_Zcompare_rec :
  coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val coq_Z_lt_dec : coq_Z -> coq_Z -> bool

val coq_Z_le_dec : coq_Z -> coq_Z -> bool

val coq_Z_gt_dec : coq_Z -> coq_Z -> bool

val coq_Z_ge_dec : coq_Z -> coq_Z -> bool

val coq_Z_lt_ge_dec : coq_Z -> coq_Z -> bool

val coq_Z_lt_le_dec : coq_Z -> coq_Z -> bool

val coq_Z_le_gt_dec : coq_Z -> coq_Z -> bool

val coq_Z_gt_le_dec : coq_Z -> coq_Z -> bool

val coq_Z_ge_lt_dec : coq_Z -> coq_Z -> bool

val coq_Z_le_lt_eq_dec : coq_Z -> coq_Z -> bool

val coq_Zlt_cotrans : coq_Z -> coq_Z -> coq_Z -> bool

val coq_Zlt_cotrans_pos : coq_Z -> coq_Z -> bool

val coq_Zlt_cotrans_neg : coq_Z -> coq_Z -> bool

val not_Zeq_inf : coq_Z -> coq_Z -> bool

val coq_Z_dec : coq_Z -> coq_Z -> bool option

val coq_Z_dec' : coq_Z -> coq_Z -> bool option

val coq_Z_zerop : coq_Z -> bool

val coq_Z_notzerop : coq_Z -> bool

val coq_Z_noteq_dec : coq_Z -> coq_Z -> bool
