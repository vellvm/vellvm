open Basics0
open CategoryOps
open Datatypes
open Function
open Monad

let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('m, 'a, 'b) coq_Kleisli = 'a -> 'm

(** val coq_Kleisli_arrow : ('a2 -> 'a1) -> ('a1, 'a2, 'a3) coq_Kleisli **)

let coq_Kleisli_arrow f =
  f

(** val coq_Kleisli_apply : ('a1, 'a2, 'a3) coq_Kleisli -> 'a2 -> 'a1 **)

let coq_Kleisli_apply f =
  f

(** val pure :
    'a1 coq_Monad -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) coq_Kleisli **)

let pure h f x =
  ret h (f x)

(** val coq_Cat_Kleisli :
    'a1 coq_Monad -> ('a1, 'a2, 'a3) coq_Kleisli -> ('a1, 'a3, 'a4)
    coq_Kleisli -> ('a1, 'a2, 'a4) coq_Kleisli **)

let coq_Cat_Kleisli h u v x =
  bind h (u x) v

(** val map :
    'a1 coq_Monad -> ('a3 -> 'a4) -> ('a1, 'a2, 'a3) coq_Kleisli -> ('a1,
    'a2, 'a4) coq_Kleisli **)

let map h g ab =
  cat (fun _ _ _ -> coq_Cat_Kleisli h) __ __ __ ab (pure h (Obj.magic g))

(** val coq_Initial_Kleisli : ('a1, coq_Empty_set, 'a2) coq_Kleisli **)

let coq_Initial_Kleisli _ =
  assert false (* absurd case *)

(** val coq_Id_Kleisli : 'a1 coq_Monad -> ('a1, 'a2, 'a2) coq_Kleisli **)

let coq_Id_Kleisli h =
  pure h id

(** val coq_Case_Kleisli :
    ('a1, 'a2, 'a4) coq_Kleisli -> ('a1, 'a3, 'a4) coq_Kleisli -> ('a1, ('a2,
    'a3) sum, 'a4) coq_Kleisli **)

let coq_Case_Kleisli =
  case_sum

(** val coq_Inl_Kleisli :
    'a1 coq_Monad -> ('a1, 'a2, ('a2, 'a3) sum) coq_Kleisli **)

let coq_Inl_Kleisli h =
  pure h (fun x -> Coq_inl x)

(** val coq_Inr_Kleisli :
    'a1 coq_Monad -> ('a1, 'a3, ('a2, 'a3) sum) coq_Kleisli **)

let coq_Inr_Kleisli h =
  pure h (fun x -> Coq_inr x)

(** val coq_Iter_Kleisli :
    'a1 coq_MonadIter -> ('a1, 'a2, ('a2, 'a3) sum) coq_Kleisli -> ('a1, 'a2,
    'a3) coq_Kleisli **)

let coq_Iter_Kleisli =
  Basics0.iter
