Require Import Integers.
Require Import Integers String ZArith.
From ExtLib Require Import Data.Map.FMapAList.

Module Int64 := Integers.Int64. 
Definition int64 := Int64.int. 

Open Scope list_scope.
Open Scope program_scope.
Local Open Scope string_scope.
(******************************* Oat Values *******************************)
(**
   We'll try to define all the possible kinds of values an Oat Program can 
   manipulate.
*)

 (* Variable names are just strings *)
Definition var : Set := string.

(* (o)AT (value)s can be one of the following *)
(**
   You'll notice that we can technically produce invalid OAT types, e.g. an 
   array of [true; 12]... We should try to prove that a well formed OAT programs
   can't have this behaviour
 *)
Inductive ovalue : Type :=
| OVALUE_Void (* Void return type *)
| OVALUE_Bool (b: bool)
| OVALUE_Int (i: int64)
| OVALUE_Str (s : string)
| OVALUE_Ref (r : ovalue_ref) 
with ovalue_ref :=
| REF_Null
| REF_Array (elts: list ovalue) 
| REF_Struct (id: string) (elts: alist string ovalue)
(* Can only have functions in the global scope - can just look it up and call it *) 
| REF_Fun (name: string)
.
