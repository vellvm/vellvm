open Datatypes
open Monad

type __ = Obj.t

type 'm coq_MonadPlus =
  __ -> __ -> 'm -> 'm -> 'm
  (* singleton inductive, whose constructor was Build_MonadPlus *)

val mplus : 'a1 coq_MonadPlus -> 'a1 -> 'a1 -> 'a1

val mjoin : 'a1 coq_Monad -> 'a1 coq_MonadPlus -> 'a1 -> 'a1 -> 'a1

module MonadPlusNotation :
 sig
 end
