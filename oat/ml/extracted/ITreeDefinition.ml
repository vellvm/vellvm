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

(** val _observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF **)

let _observe i =
  let Coq_go _observe0 = Lazy.force i in _observe0

(** val observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF **)

let observe =
  _observe

module ITree =
 struct
  (** val _bind :
      ('a2 -> ('a1, 'a3) itree) -> (('a1, 'a2) itree -> ('a1, 'a3) itree) ->
      ('a1, 'a2, ('a1, 'a2) itree) itreeF -> ('a1, 'a3) itree **)

  let _bind k bind0 = function
  | RetF r -> k r
  | TauF t -> lazy (Coq_go (TauF (bind0 t)))
  | VisF (e, h) -> lazy (Coq_go (VisF (e, (fun x -> bind0 (h x)))))

  (** val bind' :
      ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let rec bind' k t =
    _bind k (bind' k) (observe t)

  (** val cat :
      ('a2 -> ('a1, 'a3) itree) -> ('a3 -> ('a1, 'a4) itree) -> 'a2 -> ('a1,
      'a4) itree **)

  let cat k h t =
    bind' h (k t)

  (** val iter :
      ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree **)

  let rec iter step i =
    bind' (fun lr ->
      match lr with
      | Coq_inl l -> lazy (Coq_go (TauF (iter step l)))
      | Coq_inr r -> lazy (Coq_go (RetF r))) (step i)

  (** val map : ('a2 -> 'a3) -> ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let map f t =
    bind' (fun x -> lazy (Coq_go (RetF (f x)))) t

  (** val trigger : 'a1 -> ('a1, 'a2) itree **)

  let trigger e =
    lazy (Coq_go (VisF (e, (fun x -> lazy (Coq_go (RetF (Obj.magic x)))))))

  (** val ignore : ('a1, 'a2) itree -> ('a1, unit) itree **)

  let ignore x =
    map (fun _ -> ()) x

  (** val spin : ('a1, 'a2) itree **)

  let rec spin =
    lazy (Coq_go (TauF spin))

  (** val forever : ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let rec forever t =
    bind' (fun _ -> lazy (Coq_go (TauF (forever t)))) t
 end

module ITreeNotations =
 struct
 end

(** val coq_Functor_itree : ('a1, __) itree coq_Functor **)

let coq_Functor_itree _ _ =
  ITree.map

(** val coq_Applicative_itree : ('a1, __) itree coq_Applicative **)

let coq_Applicative_itree =
  { pure = (fun _ x -> lazy (Coq_go (RetF x))); ap = (fun _ _ f x ->
    ITree.bind' (fun f0 ->
      ITree.bind' (fun x0 -> lazy (Coq_go (RetF (Obj.magic f0 x0)))) x) f) }

(** val coq_Monad_itree : ('a1, __) itree coq_Monad **)

let coq_Monad_itree =
  { ret = (fun _ x -> lazy (Coq_go (RetF x))); bind = (fun _ _ t k ->
    ITree.bind' k t) }

(** val coq_MonadIter_itree :
    ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree **)

let coq_MonadIter_itree =
  ITree.iter

(** val hexploit_mp : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let hexploit_mp x x0 =
  x0 x

(** val burn : nat -> ('a1, 'a2) itree -> ('a1, 'a2) itree **)

let rec burn n t =
  match n with
  | O -> t
  | S n0 ->
    (match observe t with
     | TauF t' -> burn n0 t'
     | x -> lazy (Coq_go x))
