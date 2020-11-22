open Datatypes
open EitherMonad
open Functor
open Monad
open OptionMonad
open ReaderMonad
open StateMonad

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val idM : 'a1 -> 'a1 **)

let idM e =
  e

module Monads =
 struct
  type 'a identity = 'a

  type ('s, 'm, 'a) stateT = 's -> 'm

  type ('s, 'a) state = 's -> 's * 'a

  type ('r, 'm, 'a) readerT = 'r -> 'm

  type ('r, 'a) reader = 'r -> 'a

  type ('w, 'm, 'a) writerT = 'm

  type ('a, 'b) writer = 'a * 'b

  (** val coq_Functor_stateT :
      'a1 coq_Functor -> ('a2, 'a1, __) stateT coq_Functor **)

  let coq_Functor_stateT fm _ _ f run s =
    fmap fm (fun sa -> ((fst sa), (f (snd sa)))) (run s)

  (** val coq_Monad_stateT :
      'a1 coq_Monad -> ('a2, 'a1, __) stateT coq_Monad **)

  let coq_Monad_stateT fm =
    { ret = (fun _ a s -> ret fm (s, a)); bind = (fun _ _ t k s ->
      bind fm (t s) (fun sa -> k (snd sa) (fst sa))) }
 end

type 'm coq_MonadIter = __ -> __ -> (__ -> 'm) -> __ -> 'm

(** val iter : 'a1 coq_MonadIter -> ('a3 -> 'a1) -> 'a3 -> 'a1 **)

let iter monadIter x x0 =
  Obj.magic monadIter __ __ x x0

(** val coq_MonadIter_stateT :
    'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
    stateT) -> 'a4 -> ('a2, 'a1, 'a3) stateT **)

let coq_MonadIter_stateT mM aM step i s =
  iter aM (fun is ->
    let i0 = fst is in
    let s0 = snd is in
    bind mM (runStateT (step i0) s0) (fun is' ->
      ret mM
        (match fst is' with
         | Coq_inl i' -> Coq_inl (i', (snd is'))
         | Coq_inr r -> Coq_inr (r, (snd is'))))) (i, s)

(** val coq_MonadIter_stateT0 :
    'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
    Monads.stateT) -> 'a4 -> ('a2, 'a1, 'a3) Monads.stateT **)

let coq_MonadIter_stateT0 mM aM step i s =
  iter aM (fun si ->
    let s0 = fst si in
    let i0 = snd si in
    bind mM (step i0 s0) (fun si' ->
      ret mM
        (match snd si' with
         | Coq_inl i' -> Coq_inl ((fst si'), i')
         | Coq_inr r -> Coq_inr ((fst si'), r)))) (s, i)

(** val coq_MonadIter_readerT :
    'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum) readerT) -> 'a4
    -> ('a2, 'a1, 'a3) readerT **)

let coq_MonadIter_readerT aM step i s =
  iter aM (fun i0 -> runReaderT (step i0) s) i

(** val coq_MonadIter_optionT :
    'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a3 -> ('a1, ('a3, 'a2) sum)
    optionT) -> 'a3 -> ('a1, 'a2) optionT **)

let coq_MonadIter_optionT mM aM step i =
  iter aM (fun i0 ->
    bind mM (unOptionT (step i0)) (fun oi ->
      ret mM
        (match oi with
         | Some y ->
           (match y with
            | Coq_inl i1 -> Coq_inl i1
            | Coq_inr r -> Coq_inr (Some r))
         | None -> Coq_inr None))) i

(** val coq_MonadIter_eitherT :
    'a1 coq_Monad -> 'a1 coq_MonadIter -> ('a4 -> ('a2, 'a1, ('a4, 'a3) sum)
    eitherT) -> 'a4 -> ('a2, 'a1, 'a3) eitherT **)

let coq_MonadIter_eitherT mM aM step i =
  iter aM (fun i0 ->
    bind mM (unEitherT (step i0)) (fun ei ->
      ret mM
        (match ei with
         | Coq_inl e -> Coq_inr (Coq_inl e)
         | Coq_inr y ->
           (match y with
            | Coq_inl i1 -> Coq_inl i1
            | Coq_inr r -> Coq_inr (Coq_inr r))))) i
