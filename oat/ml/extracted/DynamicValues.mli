open BinNums
open Datatypes
open Integers

module Int64 :
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_P_mod_two_p : positive -> nat -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> coq_Z -> coq_Z

  val coq_Zzero_ext : coq_Z -> coq_Z -> coq_Z

  val coq_Zsign_ext : coq_Z -> coq_Z -> coq_Z

  val zero_ext : coq_Z -> int -> int

  val sign_ext : coq_Z -> int -> int

  val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> coq_Z -> bool

  val powerserie : coq_Z list -> coq_Z

  val int_of_one_bits : int list -> int

  val no_overlap : int -> coq_Z -> int -> coq_Z -> bool

  val coq_Zsize : coq_Z -> coq_Z

  val size : int -> coq_Z

  val iwordsize' : Int.int

  val shl' : int -> Int.int -> int

  val shru' : int -> Int.int -> int

  val shr' : int -> Int.int -> int

  val rol' : int -> Int.int -> int

  val shrx' : int -> Int.int -> int

  val shr_carry' : int -> Int.int -> int

  val one_bits' : int -> Int.int list

  val is_power2' : int -> Int.int option

  val int_of_one_bits' : Int.int list -> int

  val loword : int -> Int.int

  val hiword : int -> Int.int

  val ofwords : Int.int -> Int.int -> int

  val mul' : Int.int -> Int.int -> int
 end

type int64 = Int64.int

type var = char list

type ovalue =
| OVALUE_Void
| OVALUE_Bool of bool
| OVALUE_Int of int64
| OVALUE_Str of char list
| OVALUE_Array of ovalue list

val ovalue_rect :
  'a1 -> (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (ovalue
  list -> 'a1) -> ovalue -> 'a1

val ovalue_rec :
  'a1 -> (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (ovalue
  list -> 'a1) -> ovalue -> 'a1
