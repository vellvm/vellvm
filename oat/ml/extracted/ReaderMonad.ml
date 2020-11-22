open Monad
open MonadExc
open MonadFix
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadWriter
open MonadZero
open Monoid

type __ = Obj.t

type ('s, 't) reader =
  's -> 't
  (* singleton inductive, whose constructor was mkReader *)

(** val runReader : ('a1, 'a2) reader -> 'a1 -> 'a2 **)

let runReader r =
  r

(** val coq_Monad_reader : ('a1, __) reader coq_Monad **)

let coq_Monad_reader =
  { ret = (fun _ v _ -> v); bind = (fun _ _ c1 c2 s ->
    let v = runReader c1 s in runReader (c2 v) s) }

(** val coq_MonadReader_reader : ('a1, ('a1, __) reader) coq_MonadReader **)

let coq_MonadReader_reader =
  { local = (fun _ f cmd x -> runReader cmd (f x)); ask = (fun x ->
    Obj.magic x) }

type ('s, 'm, 't) readerT =
  's -> 'm
  (* singleton inductive, whose constructor was mkReaderT *)

(** val runReaderT : ('a1, 'a2, 'a3) readerT -> 'a1 -> 'a2 **)

let runReaderT r =
  r

(** val coq_Monad_readerT :
    'a2 coq_Monad -> ('a1, 'a2, __) readerT coq_Monad **)

let coq_Monad_readerT m =
  { ret = (fun _ x _ -> ret m x); bind = (fun _ _ c1 c2 s ->
    bind m (runReaderT c1 s) (fun v -> runReaderT (c2 v) s)) }

(** val coq_MonadReader_readerT :
    'a2 coq_Monad -> ('a1, ('a1, 'a2, __) readerT) coq_MonadReader **)

let coq_MonadReader_readerT m =
  { local = (fun _ f cmd x -> runReaderT cmd (f x)); ask = (fun x ->
    ret m x) }

(** val coq_MonadT_readerT : (('a1, 'a2, __) readerT, 'a2) coq_MonadT **)

let coq_MonadT_readerT _ c _ =
  c

(** val coq_MonadZero_readerT :
    'a2 coq_MonadZero -> ('a1, 'a2, __) readerT coq_MonadZero **)

let coq_MonadZero_readerT mZ _ =
  lift coq_MonadT_readerT (mzero mZ)

(** val coq_MonadState_readerT :
    ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __) readerT) coq_MonadState **)

let coq_MonadState_readerT mS =
  { get = (lift coq_MonadT_readerT mS.get); put = (fun x ->
    lift coq_MonadT_readerT (mS.put x)) }

(** val coq_MonadWriter_readerT :
    'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3, ('a1, 'a2, __)
    readerT) coq_MonadWriter **)

let coq_MonadWriter_readerT mon mW =
  { tell = (fun v -> lift coq_MonadT_readerT (mW.tell v)); listen =
    (fun _ c s -> listen mon mW (runReaderT c s)); pass = (fun _ c s ->
    pass mon mW (runReaderT c s)) }

(** val coq_MonadExc_readerT :
    ('a3, 'a2) coq_MonadExc -> ('a3, ('a1, 'a2, __) readerT) coq_MonadExc **)

let coq_MonadExc_readerT mE =
  { raise = (fun _ v -> lift coq_MonadT_readerT (raise mE v)); catch =
    (fun _ c h s -> catch mE (runReaderT c s) (fun x -> runReaderT (h x) s)) }

(** val coq_MonadPlus_readerT :
    'a2 coq_MonadPlus -> ('a1, 'a2, __) readerT coq_MonadPlus **)

let coq_MonadPlus_readerT mP _ _ mA mB r =
  mplus mP (runReaderT mA r) (runReaderT mB r)

(** val coq_MonadFix_readerT :
    'a2 coq_MonadFix -> ('a1, 'a2, __) readerT coq_MonadFix **)

let coq_MonadFix_readerT mF _ _ r x s =
  mfix2 mF (fun f x0 -> runReaderT (r f x0)) x s

(** val coq_MonadReader_lift_readerT :
    ('a1, 'a3) coq_MonadReader -> ('a1, ('a2, 'a3, __) readerT)
    coq_MonadReader **)

let coq_MonadReader_lift_readerT r =
  { local = (fun _ f c s -> local r f (runReaderT c s)); ask = (fun _ ->
    r.ask) }
