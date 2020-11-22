open Basics0
open CategoryOps
open Datatypes
open Function
open Monad

type ('m, 'a, 'b) coq_Kleisli = 'a -> 'm

val coq_Kleisli_arrow : ('a2 -> 'a1) -> ('a1, 'a2, 'a3) coq_Kleisli

val coq_Kleisli_apply : ('a1, 'a2, 'a3) coq_Kleisli -> 'a2 -> 'a1

val pure : 'a1 coq_Monad -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) coq_Kleisli

val coq_Cat_Kleisli :
  'a1 coq_Monad -> ('a1, 'a2, 'a3) coq_Kleisli -> ('a1, 'a3, 'a4) coq_Kleisli
  -> ('a1, 'a2, 'a4) coq_Kleisli

val map :
  'a1 coq_Monad -> ('a3 -> 'a4) -> ('a1, 'a2, 'a3) coq_Kleisli -> ('a1, 'a2,
  'a4) coq_Kleisli

val coq_Initial_Kleisli : ('a1, coq_Empty_set, 'a2) coq_Kleisli

val coq_Id_Kleisli : 'a1 coq_Monad -> ('a1, 'a2, 'a2) coq_Kleisli

val coq_Case_Kleisli :
  ('a1, 'a2, 'a4) coq_Kleisli -> ('a1, 'a3, 'a4) coq_Kleisli -> ('a1, ('a2,
  'a3) sum, 'a4) coq_Kleisli

val coq_Inl_Kleisli : 'a1 coq_Monad -> ('a1, 'a2, ('a2, 'a3) sum) coq_Kleisli

val coq_Inr_Kleisli : 'a1 coq_Monad -> ('a1, 'a3, ('a2, 'a3) sum) coq_Kleisli

val coq_Iter_Kleisli :
  'a1 coq_MonadIter -> ('a1, 'a2, ('a2, 'a3) sum) coq_Kleisli -> ('a1, 'a2,
  'a3) coq_Kleisli
