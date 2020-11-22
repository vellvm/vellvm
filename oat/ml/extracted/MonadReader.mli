open Monad

type __ = Obj.t

type ('t, 'm) coq_MonadReader = { local : (__ -> ('t -> 't) -> 'm -> 'm);
                                  ask : 'm }

val local : ('a1, 'a2) coq_MonadReader -> ('a1 -> 'a1) -> 'a2 -> 'a2

val ask : ('a1, 'a2) coq_MonadReader -> 'a2

val asks : 'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2 -> 'a3) -> 'a1

val coq_ReaderProd :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2 -> 'a3) -> ('a3 -> 'a2
  -> 'a2) -> ('a3, 'a1) coq_MonadReader
