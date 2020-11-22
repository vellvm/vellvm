open Functor

type __ = Obj.t

type 't coq_Applicative = { pure : (__ -> __ -> 't);
                            ap : (__ -> __ -> 't -> 't -> 't) }

val pure : 'a1 coq_Applicative -> 'a2 -> 'a1

val ap : 'a1 coq_Applicative -> 'a1 -> 'a1 -> 'a1

module ApplicativeNotation :
 sig
 end

val liftA : 'a1 coq_Applicative -> ('a2 -> 'a3) -> 'a1 -> 'a1

val liftA2 : 'a1 coq_Applicative -> ('a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1

val coq_Functor_Applicative : 'a1 coq_Applicative -> 'a1 coq_Functor
