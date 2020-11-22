open Monad

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('t, 'm) coq_MonadReader = { local : (__ -> ('t -> 't) -> 'm -> 'm);
                                  ask : 'm }

(** val local : ('a1, 'a2) coq_MonadReader -> ('a1 -> 'a1) -> 'a2 -> 'a2 **)

let local monadReader x x0 =
  monadReader.local __ x x0

(** val ask : ('a1, 'a2) coq_MonadReader -> 'a2 **)

let ask monadReader =
  monadReader.ask

(** val asks :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2 -> 'a3) -> 'a1 **)

let asks m mR f =
  bind m mR.ask (fun x -> ret m (f x))

(** val coq_ReaderProd :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2 -> 'a3) -> ('a3 ->
    'a2 -> 'a2) -> ('a3, 'a1) coq_MonadReader **)

let coq_ReaderProd m mR f g =
  { local = (fun _ up c -> local mR (fun s -> g (up (f s)) s) c); ask =
    (asks m mR f) }
