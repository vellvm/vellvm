open Monad

type ('t, 'm) coq_MonadState = { get : 'm; put : ('t -> 'm) }

(** val get : ('a1, 'a2) coq_MonadState -> 'a2 **)

let get monadState =
  monadState.get

(** val put : ('a1, 'a2) coq_MonadState -> 'a1 -> 'a2 **)

let put monadState =
  monadState.put

(** val modify :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a2) -> 'a1 **)

let modify m mS f =
  bind m mS.get (fun x -> bind m (mS.put (f x)) (fun _ -> ret m x))

(** val gets :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a3) -> 'a1 **)

let gets m mS f =
  bind m mS.get (fun x -> ret m (f x))

(** val coq_StateProd :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2 -> 'a3) -> ('a3 -> 'a2
    -> 'a2) -> ('a3, 'a1) coq_MonadState **)

let coq_StateProd m mS f g =
  { get = (gets m mS f); put = (fun x ->
    bind m mS.get (fun s -> mS.put (g x s))) }
