From Coq Require Import String.

From ITree Require Import
     ITree
     Events.Exception.

From Vellvm Require Import
     Error.

Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.EitherMonad.


(* Undefined behaviour carries a string. *)
Variant UndefinedBehaviourE : Type -> Type :=
| ThrowUB : string -> UndefinedBehaviourE void.


(** Since the output type of [ThrowUB] is [void], we can make it an action
    with any return type. *)
Definition throwUB {E : Type -> Type} `{UndefinedBehaviourE -< E} {X}
           (e : string)
  : itree E X
  := vis (ThrowUB e) (fun v : void => match v with end).

Definition raiseUB {E} {A} `{UndefinedBehaviourE -< E} (msg : string) : itree E A :=
  throwUB msg.

Inductive UB_or_Err T :=
| UB : string -> UB_or_Err T
| Err : string -> UB_or_Err T
| Norm : T -> UB_or_Err T
.

Arguments UB [T].
Arguments Err [T].
Arguments Norm [T].

Instance Monad_ub_or_err : Monad UB_or_Err :=
  { ret := fun _ v => Norm v
  ; bind := fun _ _ c1 c2 => match c1 with
                          | UB s => UB s
                          | Err s => Err s
                          | Norm v => c2 v
                          end
  }.

Instance MonadExc_ub_or_err : MonadExc string UB_or_Err :=
  { raise := fun _ e => Err e
  ; catch := fun _ c h => match c with
                       | UB s => UB s
                       | Err s => h s
                       | x => x
                       end
  }.
