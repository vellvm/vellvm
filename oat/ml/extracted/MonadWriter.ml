open Datatypes
open Monad
open Monoid

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('t, 'm) coq_MonadWriter = { tell : ('t -> 'm);
                                  listen : (__ -> 'm -> 'm);
                                  pass : (__ -> 'm -> 'm) }

(** val tell : 'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a1 -> 'a2 **)

let tell _ monadWriter =
  monadWriter.tell

(** val listen :
    'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a2 -> 'a2 **)

let listen _ monadWriter x =
  monadWriter.listen __ x

(** val pass : 'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a2 -> 'a2 **)

let pass _ monadWriter x =
  monadWriter.pass __ x

(** val listens :
    'a1 coq_Monad -> 'a2 coq_Monoid -> ('a2, 'a1) coq_MonadWriter -> ('a2 ->
    'a4) -> 'a1 -> 'a1 **)

let listens monad_m monoid_S writer_m f c =
  liftM monad_m (fun x -> ((fst x), (f (snd x)))) (listen monoid_S writer_m c)

(** val censor :
    'a1 coq_Monad -> 'a2 coq_Monoid -> ('a2, 'a1) coq_MonadWriter -> ('a2 ->
    'a2) -> 'a1 -> 'a1 **)

let censor monad_m monoid_S writer_m f c =
  pass monoid_S writer_m (liftM monad_m (fun x -> (x, f)) c)
