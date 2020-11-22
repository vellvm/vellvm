open Ast
open Datatypes
open DynamicValues
open Exception
open Function0
open ITreeDefinition
open Sum

type __ = Obj.t

type value = ovalue

type 'x coq_OLocalE =
| OLocalRead of var
| OLocalWrite of var * value

type 'x coq_OCallE =
| OCall of var * value list

type 'x coq_OStackE =
| OStackPush of (id * ovalue) list
| OStackPop

type 'x coq_FailureE = (char list, 'x) exceptE

val raise : (__ coq_FailureE, 'a1) coq_IFun -> char list -> ('a1, 'a2) itree

val lift_err :
  (__ coq_FailureE, 'a3) coq_IFun -> ('a1 -> ('a3, 'a2) itree) -> (char list,
  'a1) sum -> ('a3, 'a2) itree

type 'x coq_OatE =
  (__ coq_OCallE, (__ coq_OLocalE, (__ coq_OStackE, __ coq_FailureE, __)
  sum1, __) sum1, 'x) sum1

type 'x coq_OatE' =
  (__ coq_OLocalE, (__ coq_OStackE, __ coq_FailureE, __) sum1, 'x) sum1
