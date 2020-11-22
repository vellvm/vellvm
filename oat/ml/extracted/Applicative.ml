open Functor

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 't coq_Applicative = { pure : (__ -> __ -> 't);
                            ap : (__ -> __ -> 't -> 't -> 't) }

(** val pure : 'a1 coq_Applicative -> 'a2 -> 'a1 **)

let pure applicative x =
  Obj.magic applicative.pure __ x

(** val ap : 'a1 coq_Applicative -> 'a1 -> 'a1 -> 'a1 **)

let ap applicative x x0 =
  applicative.ap __ __ x x0

module ApplicativeNotation =
 struct
 end

(** val liftA : 'a1 coq_Applicative -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let liftA aT f aT0 =
  ap aT (pure aT f) aT0

(** val liftA2 :
    'a1 coq_Applicative -> ('a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 **)

let liftA2 aT f aT0 bT =
  ap aT (liftA aT f aT0) bT

(** val coq_Functor_Applicative : 'a1 coq_Applicative -> 'a1 coq_Functor **)

let coq_Functor_Applicative aT _ _ =
  liftA aT
