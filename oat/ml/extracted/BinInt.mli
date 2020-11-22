open BinNat
open BinNums
open BinPos
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Numeral

type __ = Obj.t

module Z :
 sig
  type t = coq_Z

  val zero : coq_Z

  val one : coq_Z

  val two : coq_Z

  val double : coq_Z -> coq_Z

  val succ_double : coq_Z -> coq_Z

  val pred_double : coq_Z -> coq_Z

  val pos_sub : positive -> positive -> coq_Z

  val add : coq_Z -> coq_Z -> coq_Z

  val opp : coq_Z -> coq_Z

  val succ : coq_Z -> coq_Z

  val pred : coq_Z -> coq_Z

  val sub : coq_Z -> coq_Z -> coq_Z

  val mul : coq_Z -> coq_Z -> coq_Z

  val pow_pos : coq_Z -> positive -> coq_Z

  val pow : coq_Z -> coq_Z -> coq_Z

  val square : coq_Z -> coq_Z

  val compare : coq_Z -> coq_Z -> comparison

  val sgn : coq_Z -> coq_Z

  val leb : coq_Z -> coq_Z -> bool

  val ltb : coq_Z -> coq_Z -> bool

  val geb : coq_Z -> coq_Z -> bool

  val gtb : coq_Z -> coq_Z -> bool

  val eqb : coq_Z -> coq_Z -> bool

  val max : coq_Z -> coq_Z -> coq_Z

  val min : coq_Z -> coq_Z -> coq_Z

  val abs : coq_Z -> coq_Z

  val abs_nat : coq_Z -> nat

  val abs_N : coq_Z -> coq_N

  val to_nat : coq_Z -> nat

  val to_N : coq_Z -> coq_N

  val of_nat : nat -> coq_Z

  val of_N : coq_N -> coq_Z

  val to_pos : coq_Z -> positive

  val of_uint : Decimal.uint -> coq_Z

  val of_hex_uint : Hexadecimal.uint -> coq_Z

  val of_num_uint : uint -> coq_Z

  val of_int : Decimal.int -> coq_Z

  val of_hex_int : Hexadecimal.int -> coq_Z

  val of_num_int : int -> coq_Z

  val to_int : coq_Z -> Decimal.int

  val to_hex_int : coq_Z -> Hexadecimal.int

  val to_num_int : coq_Z -> int

  val iter : coq_Z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : positive -> coq_Z -> coq_Z * coq_Z

  val div_eucl : coq_Z -> coq_Z -> coq_Z * coq_Z

  val div : coq_Z -> coq_Z -> coq_Z

  val modulo : coq_Z -> coq_Z -> coq_Z

  val quotrem : coq_Z -> coq_Z -> coq_Z * coq_Z

  val quot : coq_Z -> coq_Z -> coq_Z

  val rem : coq_Z -> coq_Z -> coq_Z

  val even : coq_Z -> bool

  val odd : coq_Z -> bool

  val div2 : coq_Z -> coq_Z

  val quot2 : coq_Z -> coq_Z

  val log2 : coq_Z -> coq_Z

  val sqrtrem : coq_Z -> coq_Z * coq_Z

  val sqrt : coq_Z -> coq_Z

  val gcd : coq_Z -> coq_Z -> coq_Z

  val ggcd : coq_Z -> coq_Z -> coq_Z * (coq_Z * coq_Z)

  val testbit : coq_Z -> coq_Z -> bool

  val shiftl : coq_Z -> coq_Z -> coq_Z

  val shiftr : coq_Z -> coq_Z -> coq_Z

  val coq_lor : coq_Z -> coq_Z -> coq_Z

  val coq_land : coq_Z -> coq_Z -> coq_Z

  val ldiff : coq_Z -> coq_Z -> coq_Z

  val coq_lxor : coq_Z -> coq_Z -> coq_Z

  val eq_dec : coq_Z -> coq_Z -> bool

  module Private_BootStrap :
   sig
   end

  val leb_spec0 : coq_Z -> coq_Z -> reflect

  val ltb_spec0 : coq_Z -> coq_Z -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1

    val max_case :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1

    val max_dec : coq_Z -> coq_Z -> bool

    val min_case_strong :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1

    val min_case :
      coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1

    val min_dec : coq_Z -> coq_Z -> bool
   end

  val max_case_strong : coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1

  val max_dec : coq_Z -> coq_Z -> bool

  val min_case_strong : coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1

  val min_dec : coq_Z -> coq_Z -> bool

  val sqrt_up : coq_Z -> coq_Z

  val log2_up : coq_Z -> coq_Z

  module Private_NZDiv :
   sig
   end

  module Private_Div :
   sig
    module Quot2Div :
     sig
      val div : coq_Z -> coq_Z -> coq_Z

      val modulo : coq_Z -> coq_Z -> coq_Z
     end

    module NZQuot :
     sig
     end
   end

  val lcm : coq_Z -> coq_Z -> coq_Z

  val eqb_spec : coq_Z -> coq_Z -> reflect

  val b2z : bool -> coq_Z

  val setbit : coq_Z -> coq_Z -> coq_Z

  val clearbit : coq_Z -> coq_Z -> coq_Z

  val lnot : coq_Z -> coq_Z

  val ones : coq_Z -> coq_Z
 end

module Pos2Z :
 sig
 end

module Z2Pos :
 sig
 end
