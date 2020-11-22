open Datatypes
open Monad

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_MonadPlus =
  __ -> __ -> 'm -> 'm -> 'm
  (* singleton inductive, whose constructor was Build_MonadPlus *)

(** val mplus : 'a1 coq_MonadPlus -> 'a1 -> 'a1 -> 'a1 **)

let mplus monadPlus x x0 =
  monadPlus __ __ x x0

(** val mjoin : 'a1 coq_Monad -> 'a1 coq_MonadPlus -> 'a1 -> 'a1 -> 'a1 **)

let mjoin m mP a b =
  bind m (mplus mP a b) (fun x ->
    match x with
    | Coq_inl x0 -> ret m x0
    | Coq_inr x0 -> ret m x0)

module MonadPlusNotation =
 struct
 end
