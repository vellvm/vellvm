open Ascii
open Basics
open BinNums
open BinPos
open Compare_dec
open Datatypes
open List0
open Monad
open PeanoNat
open RelDec
open String0

type __ = Obj.t

val get_last_digit : nat -> char list

val string_of_nat_aux_F :
  (char list -> nat -> char list) -> char list -> nat -> char list

val string_of_nat_aux_terminate : char list -> nat -> char list

val string_of_nat_aux : char list -> nat -> char list

type coq_R_string_of_nat_aux =
| R_string_of_nat_aux_0 of char list * nat
| R_string_of_nat_aux_1 of char list * nat * nat * char list
   * coq_R_string_of_nat_aux

val coq_R_string_of_nat_aux_rect :
  (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __ ->
  char list -> coq_R_string_of_nat_aux -> 'a1 -> 'a1) -> char list -> nat ->
  char list -> coq_R_string_of_nat_aux -> 'a1

val coq_R_string_of_nat_aux_rec :
  (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __ ->
  char list -> coq_R_string_of_nat_aux -> 'a1 -> 'a1) -> char list -> nat ->
  char list -> coq_R_string_of_nat_aux -> 'a1

val string_of_nat_aux_rect :
  (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __ ->
  'a1 -> 'a1) -> char list -> nat -> 'a1

val string_of_nat_aux_rec :
  (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __ ->
  'a1 -> 'a1) -> char list -> nat -> 'a1

val coq_R_string_of_nat_aux_correct :
  char list -> nat -> char list -> coq_R_string_of_nat_aux

val string_of_nat : nat -> char list

val string_of_Z : coq_Z -> char list

val string_of_nat_bin : nat -> char list

val monad_fold_right :
  'a1 coq_Monad -> ('a3 -> 'a2 -> 'a1) -> 'a2 list -> 'a3 -> 'a1

val monad_app_fst : 'a1 coq_Monad -> ('a2 -> 'a1) -> ('a2 * 'a3) -> 'a1

val monad_app_snd : 'a1 coq_Monad -> ('a3 -> 'a1) -> ('a2 * 'a3) -> 'a1

val map_monad : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1

val map_monad_ : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val forall2b : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val coq_Forall_dec : ('a1 -> bool) -> 'a1 list -> bool

val replace : 'a1 list -> nat -> 'a1 -> 'a1 list

val replicate : 'a1 -> nat -> 'a1 list

val interval : nat -> nat -> nat list

val trim : 'a1 option list -> 'a1 list

val nth_f : 'a2 -> ('a1 -> 'a2) -> nat -> 'a1 list -> 'a2

val assoc : 'a1 coq_RelDec -> 'a1 -> ('a1 * 'a2) list -> 'a2 option

val snoc : 'a1 -> 'a1 list -> 'a1 list

val map_option : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val find_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option

val opt_compose : ('a2 -> 'a3) -> ('a1 -> 'a2 option) -> 'a1 -> 'a3 option

val option_iter : ('a1 -> 'a1 option) -> 'a1 -> nat -> 'a1 option

val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val option_bind2 :
  ('a1 * 'a2) option -> ('a1 -> 'a2 -> 'a3 option) -> 'a3 option

module OptionNotations :
 sig
 end

val map_prod : ('a1 * 'a2) -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 * 'a4

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

val comp : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val map_snd : ('a2 -> 'a3) -> ('a1 * 'a2) list -> ('a1 * 'a3) list
