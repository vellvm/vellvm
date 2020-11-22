open Applicative
open Functor

type __ = Obj.t

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 coq_Monad -> 'a2 -> 'a1

val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

val liftM : 'a1 coq_Monad -> ('a2 -> 'a3) -> 'a1 -> 'a1

val liftM2 : 'a1 coq_Monad -> ('a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1

val liftM3 :
  'a1 coq_Monad -> ('a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 -> 'a1

val apM : 'a1 coq_Monad -> 'a1 -> 'a1 -> 'a1

val mcompose : 'a1 coq_Monad -> ('a2 -> 'a1) -> ('a3 -> 'a1) -> 'a2 -> 'a1

module MonadBaseNotation :
 sig
 end

module MonadNotation :
 sig
 end

module MonadLetNotation :
 sig
 end

val coq_Functor_Monad : 'a1 coq_Monad -> 'a1 coq_Functor

val coq_Applicative_Monad : 'a1 coq_Monad -> 'a1 coq_Applicative
