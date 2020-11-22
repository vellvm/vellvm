open Datatypes
open Monad
open Monoid

type __ = Obj.t

type ('t, 'm) coq_MonadWriter = { tell : ('t -> 'm);
                                  listen : (__ -> 'm -> 'm);
                                  pass : (__ -> 'm -> 'm) }

val tell : 'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a1 -> 'a2

val listen : 'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a2 -> 'a2

val pass : 'a1 coq_Monoid -> ('a1, 'a2) coq_MonadWriter -> 'a2 -> 'a2

val listens :
  'a1 coq_Monad -> 'a2 coq_Monoid -> ('a2, 'a1) coq_MonadWriter -> ('a2 ->
  'a4) -> 'a1 -> 'a1

val censor :
  'a1 coq_Monad -> 'a2 coq_Monoid -> ('a2, 'a1) coq_MonadWriter -> ('a2 ->
  'a2) -> 'a1 -> 'a1
