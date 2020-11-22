open Datatypes
open Monad
open MonadExc
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadZero

type __ = Obj.t

(** val coq_Monad_option : __ option coq_Monad **)

let coq_Monad_option =
  { ret = (Obj.magic (fun _ x -> Some x)); bind = (fun _ _ c1 c2 ->
    match c1 with
    | Some v -> c2 v
    | None -> None) }

(** val coq_Zero_option : __ option coq_MonadZero **)

let coq_Zero_option =
  Obj.magic (fun _ -> None)

(** val coq_Plus_option : __ option coq_MonadPlus **)

let coq_Plus_option _ _ aM bM =
  match aM with
  | Some a -> Some (Obj.magic (Coq_inl a))
  | None -> liftM coq_Monad_option (fun x -> Coq_inr x) bM

type ('m, 'a) optionT =
  'm
  (* singleton inductive, whose constructor was mkOptionT *)

(** val optionT_rect : ('a1 -> 'a3) -> ('a1, 'a2) optionT -> 'a3 **)

let optionT_rect f =
  f

(** val optionT_rec : ('a1 -> 'a3) -> ('a1, 'a2) optionT -> 'a3 **)

let optionT_rec f =
  f

(** val unOptionT : ('a1, 'a2) optionT -> 'a1 **)

let unOptionT o =
  o

(** val coq_Monad_optionT : 'a1 coq_Monad -> ('a1, __) optionT coq_Monad **)

let coq_Monad_optionT m =
  { ret = (fun _ x -> ret m (Some x)); bind = (fun _ _ aMM f ->
    bind m (unOptionT aMM) (fun aM ->
      match aM with
      | Some a -> unOptionT (f a)
      | None -> ret m None)) }

(** val coq_Zero_optionT :
    'a1 coq_Monad -> ('a1, __) optionT coq_MonadZero **)

let coq_Zero_optionT m _ =
  ret m None

(** val coq_MonadT_optionT :
    'a1 coq_Monad -> (('a1, __) optionT, 'a1) coq_MonadT **)

let coq_MonadT_optionT m _ aM =
  liftM m (ret coq_Monad_option) aM

(** val coq_State_optionT :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2, ('a1, __) optionT)
    coq_MonadState **)

let coq_State_optionT m sM =
  { get = (lift (coq_MonadT_optionT m) sM.get); put = (fun v ->
    lift (coq_MonadT_optionT m) (sM.put v)) }

(** val coq_Plus_optionT_right :
    'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus **)

let coq_Plus_optionT_right m _ _ a b =
  bind m (unOptionT b) (fun b0 ->
    match b0 with
    | Some b1 -> ret m (Some (Coq_inr b1))
    | None ->
      bind m (unOptionT a) (fun a0 ->
        match a0 with
        | Some a1 -> ret m (Some (Coq_inl a1))
        | None -> ret m None))

(** val coq_Plus_optionT_left :
    'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus **)

let coq_Plus_optionT_left m _ _ a b =
  bind m (unOptionT a) (fun a0 ->
    match a0 with
    | Some a1 -> ret m (Some (Coq_inl a1))
    | None ->
      bind m (unOptionT b) (fun b0 ->
        match b0 with
        | Some b1 -> ret m (Some (Coq_inr b1))
        | None -> ret m None))

(** val coq_Plus_optionT :
    'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus **)

let coq_Plus_optionT =
  coq_Plus_optionT_left

(** val coq_Reader_optionT :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2, ('a1, __) optionT)
    coq_MonadReader **)

let coq_Reader_optionT m sM =
  { local = (fun _ v cmd -> local sM v (unOptionT cmd)); ask =
    (lift (coq_MonadT_optionT m) sM.ask) }

(** val coq_OptionTError :
    'a1 coq_Monad -> (unit, ('a1, __) optionT) coq_MonadExc **)

let coq_OptionTError m =
  { raise = (fun _ _ -> mzero (coq_Zero_optionT m)); catch = (fun _ aMM f ->
    bind m (unOptionT aMM) (fun aM ->
      match aM with
      | Some x -> ret m (Some x)
      | None -> unOptionT (f ()))) }
