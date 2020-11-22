open Function0
open ITreeDefinition
open Subevent

type __ = Obj.t

type ('err, 'x) exceptE =
  'err
  (* singleton inductive, whose constructor was Throw *)

val throw : (('a1, __) exceptE, 'a2) coq_IFun -> 'a1 -> ('a2, 'a3) itree
