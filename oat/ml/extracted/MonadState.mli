open Monad

type ('t, 'm) coq_MonadState = { get : 'm; put : ('t -> 'm) }

val get : ('a1, 'a2) coq_MonadState -> 'a2

val put : ('a1, 'a2) coq_MonadState -> 'a1 -> 'a2

val modify : 'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a2) -> 'a1

val gets : 'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a3) -> 'a1

val coq_StateProd :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a3) -> ('a3 -> 'a2
  -> 'a2) -> ('a3, 'a1) coq_MonadState
