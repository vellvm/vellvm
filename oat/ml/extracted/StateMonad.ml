open Datatypes
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

type ('s, 't) state =
  's -> 't * 's
  (* singleton inductive, whose constructor was mkState *)

(** val runState : ('a1, 'a2) state -> 'a1 -> 'a2 * 'a1 **)

let runState s =
  s

(** val evalState : ('a1, 'a2) state -> 'a1 -> 'a2 **)

let evalState c s =
  fst (runState c s)

(** val execState : ('a1, 'a2) state -> 'a1 -> 'a1 **)

let execState c s =
  snd (runState c s)

(** val coq_Monad_state : ('a1, __) state coq_Monad **)

let coq_Monad_state =
  { ret = (fun _ v s -> (v, s)); bind = (fun _ _ c1 c2 s ->
    let (v, s0) = runState c1 s in runState (c2 v) s0) }

(** val coq_MonadState_state : ('a1, ('a1, __) state) coq_MonadState **)

let coq_MonadState_state =
  { get = (fun x -> ((Obj.magic x), x)); put = (fun v _ -> ((Obj.magic ()),
    v)) }

type ('s, 'm, 't) stateT =
  's -> 'm
  (* singleton inductive, whose constructor was mkStateT *)

(** val runStateT : ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2 **)

let runStateT s =
  s

(** val evalStateT : 'a2 coq_Monad -> ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2 **)

let evalStateT m c s =
  bind m (runStateT c s) (fun x -> ret m (fst x))

(** val execStateT : 'a2 coq_Monad -> ('a1, 'a2, 'a3) stateT -> 'a1 -> 'a2 **)

let execStateT m c s =
  bind m (runStateT c s) (fun x -> ret m (snd x))

(** val coq_Monad_stateT :
    'a2 coq_Monad -> ('a1, 'a2, __) stateT coq_Monad **)

let coq_Monad_stateT m =
  { ret = (fun _ x s -> ret m (x, s)); bind = (fun _ _ c1 c2 s ->
    bind m (runStateT c1 s) (fun vs ->
      let (v, s0) = vs in runStateT (c2 v) s0)) }

(** val coq_MonadState_stateT :
    'a2 coq_Monad -> ('a1, ('a1, 'a2, __) stateT) coq_MonadState **)

let coq_MonadState_stateT m =
  { get = (fun x -> ret m (x, x)); put = (fun v _ -> ret m ((), v)) }

(** val coq_MonadT_stateT :
    'a2 coq_Monad -> (('a1, 'a2, __) stateT, 'a2) coq_MonadT **)

let coq_MonadT_stateT m _ c s =
  bind m c (fun t -> ret m (t, s))

(** val coq_State_State_stateT :
    'a2 coq_Monad -> ('a3, 'a2) coq_MonadState -> ('a3, ('a1, 'a2, __)
    stateT) coq_MonadState **)

let coq_State_State_stateT m mS =
  { get = (lift (coq_MonadT_stateT m) mS.get); put = (fun x ->
    lift (coq_MonadT_stateT m) (mS.put x)) }

(** val coq_MonadReader_stateT :
    'a2 coq_Monad -> ('a3, 'a2) coq_MonadReader -> ('a3, ('a1, 'a2, __)
    stateT) coq_MonadReader **)

let coq_MonadReader_stateT m mR =
  { local = (fun _ f c s -> local mR f (runStateT c s)); ask = (fun s ->
    bind m mR.ask (fun t -> ret m (t, s))) }

(** val coq_MonadWriter_stateT :
    'a2 coq_Monad -> 'a3 coq_Monoid -> ('a3, 'a2) coq_MonadWriter -> ('a3,
    ('a1, 'a2, __) stateT) coq_MonadWriter **)

let coq_MonadWriter_stateT m mon mR =
  { tell = (fun x s -> bind m (mR.tell x) (fun v -> ret m (v, s))); listen =
    (fun _ c s ->
    bind m (listen mon mR (runStateT c s)) (fun x ->
      let (y, t) = x in let (a, s0) = y in ret m ((a, t), s0))); pass =
    (fun _ c s ->
    bind m (runStateT c s) (fun x ->
      let (y, s0) = x in let (a, t) = y in pass mon mR (ret m ((a, s0), t)))) }

(** val coq_Exc_stateT :
    'a2 coq_Monad -> ('a3, 'a2) coq_MonadExc -> ('a3, ('a1, 'a2, __) stateT)
    coq_MonadExc **)

let coq_Exc_stateT m mR =
  { raise = (fun _ e -> lift (coq_MonadT_stateT m) (raise mR e)); catch =
    (fun _ body hnd s ->
    catch mR (runStateT body s) (fun e -> runStateT (hnd e) s)) }

(** val coq_MonadZero_stateT :
    'a2 coq_Monad -> 'a2 coq_MonadZero -> ('a1, 'a2, __) stateT coq_MonadZero **)

let coq_MonadZero_stateT m mR _ =
  lift (coq_MonadT_stateT m) (mzero mR)

(** val coq_MonadFix_stateT :
    'a2 coq_MonadFix -> ('a1, 'a2, __) stateT coq_MonadFix **)

let coq_MonadFix_stateT mF _ _ _ v s =
  mfix2 mF (fun r v0 s0 -> runStateT (r v0) s0) v s

(** val coq_MonadPlus_stateT :
    'a2 coq_Monad -> 'a2 coq_MonadPlus -> ('a1, 'a2, __) stateT coq_MonadPlus **)

let coq_MonadPlus_stateT m mP _ _ a b s =
  bind m (mplus mP (runStateT a s) (runStateT b s)) (fun res ->
    match res with
    | Coq_inl y -> let (a0, s0) = y in ret m ((Coq_inl a0), s0)
    | Coq_inr y -> let (b0, s0) = y in ret m ((Coq_inr b0), s0))
