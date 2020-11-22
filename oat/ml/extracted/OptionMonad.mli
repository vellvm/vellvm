open Datatypes
open Monad
open MonadExc
open MonadPlus
open MonadReader
open MonadState
open MonadTrans
open MonadZero

type __ = Obj.t

val coq_Monad_option : __ option coq_Monad

val coq_Zero_option : __ option coq_MonadZero

val coq_Plus_option : __ option coq_MonadPlus

type ('m, 'a) optionT =
  'm
  (* singleton inductive, whose constructor was mkOptionT *)

val optionT_rect : ('a1 -> 'a3) -> ('a1, 'a2) optionT -> 'a3

val optionT_rec : ('a1 -> 'a3) -> ('a1, 'a2) optionT -> 'a3

val unOptionT : ('a1, 'a2) optionT -> 'a1

val coq_Monad_optionT : 'a1 coq_Monad -> ('a1, __) optionT coq_Monad

val coq_Zero_optionT : 'a1 coq_Monad -> ('a1, __) optionT coq_MonadZero

val coq_MonadT_optionT : 'a1 coq_Monad -> (('a1, __) optionT, 'a1) coq_MonadT

val coq_State_optionT :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadState -> ('a2, ('a1, __) optionT)
  coq_MonadState

val coq_Plus_optionT_right : 'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus

val coq_Plus_optionT_left : 'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus

val coq_Plus_optionT : 'a1 coq_Monad -> ('a1, __) optionT coq_MonadPlus

val coq_Reader_optionT :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadReader -> ('a2, ('a1, __) optionT)
  coq_MonadReader

val coq_OptionTError : 'a1 coq_Monad -> (unit, ('a1, __) optionT) coq_MonadExc
