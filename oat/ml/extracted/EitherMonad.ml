open Datatypes
open Monad
open MonadExc
open MonadFix
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadWriter
open Monoid

type __ = Obj.t

(** val coq_Monad_either : ('a1, __) sum coq_Monad **)

let coq_Monad_either =
  { ret = (fun _ v -> Coq_inr v); bind = (fun _ _ c1 c2 ->
    match c1 with
    | Coq_inl v -> Coq_inl v
    | Coq_inr v -> c2 v) }

(** val coq_Exception_either : ('a1, ('a1, __) sum) coq_MonadExc **)

let coq_Exception_either =
  { raise = (fun _ v -> Coq_inl v); catch = (fun _ c h ->
    match c with
    | Coq_inl v -> h v
    | Coq_inr _ -> c) }

type ('t, 'm, 'a) eitherT =
  'm
  (* singleton inductive, whose constructor was mkEitherT *)

(** val eitherT_rect : ('a2 -> 'a4) -> ('a1, 'a2, 'a3) eitherT -> 'a4 **)

let eitherT_rect f =
  f

(** val eitherT_rec : ('a2 -> 'a4) -> ('a1, 'a2, 'a3) eitherT -> 'a4 **)

let eitherT_rec f =
  f

(** val unEitherT : ('a1, 'a2, 'a3) eitherT -> 'a2 **)

let unEitherT e =
  e

(** val coq_Monad_eitherT :
    'a2 coq_Monad -> ('a1, 'a2, __) eitherT coq_Monad **)

let coq_Monad_eitherT m =
  { ret = (fun _ x -> ret m (Coq_inr x)); bind = (fun _ _ c f ->
    bind m (unEitherT c) (fun xM ->
      match xM with
      | Coq_inl x -> ret m (Coq_inl x)
      | Coq_inr x -> unEitherT (f x))) }

(** val coq_Exception_eitherT :
    'a2 coq_Monad -> ('a1, ('a1, 'a2, __) eitherT) coq_MonadExc **)

let coq_Exception_eitherT m =
  { raise = (fun _ v -> ret m (Coq_inl v)); catch = (fun _ c h ->
    bind m (unEitherT c) (fun xM ->
      match xM with
      | Coq_inl x -> unEitherT (h x)
      | Coq_inr x -> ret m (Coq_inr x))) }

(** val coq_MonadPlus_eitherT :
    'a2 coq_Monad -> ('a1, 'a2, __) eitherT coq_MonadPlus **)

let coq_MonadPlus_eitherT m _ _ mA mB =
  bind m (unEitherT mA) (fun x ->
    match x with
    | Coq_inl _ ->
      bind m (unEitherT mB) (fun y ->
        match y with
        | Coq_inl t -> ret m (Coq_inl t)
        | Coq_inr b -> ret m (Coq_inr (Coq_inr b)))
    | Coq_inr a -> ret m (Coq_inr (Coq_inl a)))

(** val coq_MonadT_eitherT :
    'a2 coq_Monad -> (('a1, 'a2, __) eitherT, 'a2) coq_MonadT **)

let coq_MonadT_eitherT m _ c =
  liftM m (ret coq_Monad_either) c

(** val coq_MonadState_eitherT :
    'a2 coq_Monad -> ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __)
    eitherT) coq_MonadState **)

let coq_MonadState_eitherT m mS =
  { get = (lift (coq_MonadT_eitherT m) mS.get); put = (fun v ->
    lift (coq_MonadT_eitherT m) (mS.put v)) }

(** val coq_MonadReader_eitherT :
    'a2 coq_Monad -> ('a3, 'a2) coq_MonadReader -> ('a3, ('a1, 'a2, __)
    eitherT) coq_MonadReader **)

let coq_MonadReader_eitherT m mR =
  { local = (fun _ f cmd -> local mR f (unEitherT cmd)); ask =
    (lift (coq_MonadT_eitherT m) mR.ask) }

(** val coq_MonadWriter_eitherT :
    'a2 coq_Monad -> 'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3,
    ('a1, 'a2, __) eitherT) coq_MonadWriter **)

let coq_MonadWriter_eitherT m mon mW =
  { tell = (fun x -> lift (coq_MonadT_eitherT m) (mW.tell x)); listen =
    (fun _ c ->
    bind m (listen mon mW (unEitherT c)) (fun x ->
      let (y, t) = x in
      (match y with
       | Coq_inl l -> ret m (Coq_inl l)
       | Coq_inr a -> ret m (Coq_inr (a, t))))); pass = (fun _ c ->
    bind m (unEitherT c) (fun x ->
      match x with
      | Coq_inl s -> ret m (Coq_inl s)
      | Coq_inr y -> let (a, f) = y in pass mon mW (ret m ((Coq_inr a), f)))) }

(** val coq_MonadFix_eitherT :
    'a2 coq_MonadFix -> ('a1, 'a2, __) eitherT coq_MonadFix **)

let coq_MonadFix_eitherT mF _ _ r v =
  mfix mF (fun f x -> unEitherT (r f x)) v
