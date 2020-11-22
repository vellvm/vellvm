open BinNums
open Datatypes
open Integers

module Int64 = Int64

type int64 = Int64.int

type var = char list

type ovalue =
| OVALUE_Void
| OVALUE_Bool of bool
| OVALUE_Int of int64
| OVALUE_Str of char list
| OVALUE_Array of ovalue list

(** val ovalue_rect :
    'a1 -> (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (ovalue
    list -> 'a1) -> ovalue -> 'a1 **)

let ovalue_rect f f0 f1 f2 f3 = function
| OVALUE_Void -> f
| OVALUE_Bool x -> f0 x
| OVALUE_Int x -> f1 x
| OVALUE_Str x -> f2 x
| OVALUE_Array x -> f3 x

(** val ovalue_rec :
    'a1 -> (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (ovalue
    list -> 'a1) -> ovalue -> 'a1 **)

let ovalue_rec f f0 f1 f2 f3 = function
| OVALUE_Void -> f
| OVALUE_Bool x -> f0 x
| OVALUE_Int x -> f1 x
| OVALUE_Str x -> f2 x
| OVALUE_Array x -> f3 x
