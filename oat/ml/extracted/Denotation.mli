open Ast
open BinNums
open CategoryKleisli
open CategoryOps
open Datatypes
open DynamicValues
open Error
open Function0
open ITreeDefinition
open Integers
open List0
open Monad
open OatEvents
open Recursion
open String0
open Subevent
open Util

type __ = Obj.t

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

type expr = exp

type stmt = Ast.stmt

type unop = Ast.unop

type binop = Ast.binop

type vdecl = Ast.vdecl

val neq : int64 -> int64 -> bool

val lte : int64 -> int64 -> bool

val gt : int64 -> int64 -> bool

val gte : int64 -> int64 -> bool

val denote_uop : unop -> ovalue -> (__ coq_OatE, ovalue) itree

val denote_bop : binop -> ovalue -> ovalue -> (__ coq_OatE, ovalue) itree

val fcall_return_or_fail : expr -> ovalue list -> (__ coq_OatE, ovalue) itree

val denote_expr : expr -> (__ coq_OatE, ovalue) itree

val seq :
  stmt node list -> (stmt -> (__ coq_OatE, (unit, 'a1) sum) itree) -> (__
  coq_OatE, (unit, 'a1) sum) itree

type stmt_t = (unit, ovalue) sum

type cont_stmt = (unit, stmt_t) sum

val coq_while :
  (__ coq_OatE, (unit, stmt_t) sum) itree -> (__ coq_OatE, stmt_t) itree

val end_loop : (__ coq_OatE, (unit, stmt_t) sum) itree

val cont_loop_silent : (__ coq_OatE, (unit, stmt_t) sum) itree

val cont_loop_end : ovalue -> (__ coq_OatE, (unit, stmt_t) sum) itree

val for_loop_pre : vdecl list -> (__ coq_OatE, unit) itree

val lift_eff :
  (__ coq_OatE, 'a1) itree -> (__ coq_OatE, (unit, 'a1) sum) itree

val denote_stmt : stmt -> (__ coq_OatE, (unit, ovalue) sum) itree

val denote_block_acc :
  (__ coq_OatE, (unit, ovalue) sum) itree -> block -> (__ coq_OatE, ovalue)
  itree

val denote_block : block -> (__ coq_OatE, ovalue) itree

type fdecl_denotation = ovalue list -> (__ coq_OatE, ovalue) itree

val combine_lists_err :
  'a1 list -> 'a2 list -> (char list, ('a1 * 'a2) list) sum

type function_denotation = ovalue list -> (__ coq_OatE, ovalue) itree

val t : (id * ovalue) list -> (__ coq_OStackE, unit) itree

val t' : (id * ovalue) list -> block -> (__ coq_OatE, ovalue) itree

val denote_fdecl : fdecl -> function_denotation

val lookup : id -> (id * 'a1) list -> 'a1 option

val interp_away_calls :
  (id * function_denotation) list -> char list -> ovalue list -> (__
  coq_OatE', value) itree
