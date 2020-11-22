open Applicative
open Datatypes
open Functor
open Monad

type __ = Obj.t

type ('e, 'r, 'itree) itreeF =
| RetF of 'r
| TauF of 'itree
| VisF of 'e * (__ -> 'itree)

type ('e, 'r) itree = ('e, 'r) __itree Lazy.t
and ('e, 'r) __itree =
| Coq_go of ('e, 'r, ('e, 'r) itree) itreeF

val _observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF

val observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF

module ITree :
 sig
  val _bind :
    ('a2 -> ('a1, 'a3) itree) -> (('a1, 'a2) itree -> ('a1, 'a3) itree) ->
    ('a1, 'a2, ('a1, 'a2) itree) itreeF -> ('a1, 'a3) itree

  val bind' :
    ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a2) itree -> ('a1, 'a3) itree

  val cat :
    ('a2 -> ('a1, 'a3) itree) -> ('a3 -> ('a1, 'a4) itree) -> 'a2 -> ('a1,
    'a4) itree

  val iter : ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree

  val map : ('a2 -> 'a3) -> ('a1, 'a2) itree -> ('a1, 'a3) itree

  val trigger : 'a1 -> ('a1, 'a2) itree

  val ignore : ('a1, 'a2) itree -> ('a1, unit) itree

  val spin : ('a1, 'a2) itree

  val forever : ('a1, 'a2) itree -> ('a1, 'a3) itree
 end

module ITreeNotations :
 sig
 end

val coq_Functor_itree : ('a1, __) itree coq_Functor

val coq_Applicative_itree : ('a1, __) itree coq_Applicative

val coq_Monad_itree : ('a1, __) itree coq_Monad

val coq_MonadIter_itree :
  ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree

val hexploit_mp : 'a1 -> ('a1 -> 'a2) -> 'a2

val burn : nat -> ('a1, 'a2) itree -> ('a1, 'a2) itree
