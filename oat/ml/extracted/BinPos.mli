open BinNums
open BinPosDef
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Nat
open Numeral

type __ = Obj.t

module Pos :
 sig
  type t = positive

  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred : positive -> positive

  val pred_N : positive -> coq_N

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val pred_mask : mask -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val square : positive -> positive

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size_nat : positive -> nat

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val min : positive -> positive -> positive

  val max : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val leb : positive -> positive -> bool

  val ltb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive * mask) ->
    positive * mask

  val sqrtrem : positive -> positive * mask

  val sqrt : positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val ggcdn : nat -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val coq_Nsucc_double : coq_N -> coq_N

  val coq_Ndouble : coq_N -> coq_N

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> coq_N

  val ldiff : positive -> positive -> coq_N

  val coq_lxor : positive -> positive -> coq_N

  val shiftl_nat : positive -> nat -> positive

  val shiftr_nat : positive -> nat -> positive

  val shiftl : positive -> coq_N -> positive

  val shiftr : positive -> coq_N -> positive

  val testbit_nat : positive -> nat -> bool

  val testbit : positive -> coq_N -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive

  val of_uint_acc : Decimal.uint -> positive -> positive

  val of_uint : Decimal.uint -> coq_N

  val of_hex_uint_acc : Hexadecimal.uint -> positive -> positive

  val of_hex_uint : Hexadecimal.uint -> coq_N

  val of_num_uint : uint -> coq_N

  val of_int : Decimal.int -> positive option

  val of_hex_int : Hexadecimal.int -> positive option

  val of_num_int : int -> positive option

  val to_little_uint : positive -> Decimal.uint

  val to_uint : positive -> Decimal.uint

  val to_little_hex_uint : positive -> Hexadecimal.uint

  val to_hex_uint : positive -> Hexadecimal.uint

  val to_num_uint : positive -> uint

  val to_int : positive -> Decimal.int

  val to_hex_int : positive -> Hexadecimal.int

  val to_num_int : positive -> int

  val eq_dec : positive -> positive -> bool

  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1

  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1

  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView

  val peanoView : positive -> coq_PeanoView

  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1

  val eqb_spec : positive -> positive -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : positive -> positive -> reflect

  val ltb_spec0 : positive -> positive -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1

    val max_dec : positive -> positive -> bool

    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
      'a1 -> 'a1 -> 'a1

    val min_dec : positive -> positive -> bool
   end

  val max_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val max_dec : positive -> positive -> bool

  val min_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1

  val min_dec : positive -> positive -> bool
 end
