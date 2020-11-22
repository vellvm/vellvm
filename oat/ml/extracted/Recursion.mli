open Datatypes
open ITreeDefinition
open Sum

type __ = Obj.t

val interp_mrec :
  (__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> (('a1, 'a2, __) sum1,
  'a3) itree -> ('a2, 'a3) itree

val mrec :
  (__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> 'a1 -> ('a2, 'a3) itree

val trigger_inl1 : 'a1 -> (('a1, 'a2, __) sum1, 'a3) itree

val mrec_fix :
  ((__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> __ -> 'a1 -> (('a1, 'a2,
  __) sum1, __) itree) -> 'a1 -> ('a2, 'a3) itree

type ('a, 'b, 'x) callE =
  'a
  (* singleton inductive, whose constructor was Call *)

val callE_rect : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3

val callE_rec : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3

val unCall : ('a1, 'a2, 'a3) callE -> 'a1

val calling : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3

val calling' :
  ('a1 -> ('a3, 'a2) itree) -> ('a1, 'a2, 'a4) callE -> ('a3, 'a4) itree

val coq_rec :
  ('a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 -> ('a1,
  'a3) itree

val call : 'a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree

val rec_fix :
  (('a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 ->
  ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 -> ('a1, 'a3)
  itree
