(* begin hide *)
From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.PropT
     Utils.Error
     Semantics.LLVMEvents.

From ITree Require Import
     ITree
     Eq.Eq
     Basics.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Handler for out of memory
  Definition of the propositional and executable handlers for out of memory (abort).
  - The model interpret the event as an arbitrary computation : in this model, UB can be anything, but cannot travel back in time.
  - The interpreter simply fails.
*)

(* Technically OOM should refine OOM... *)
Definition OOM_handler {E}: OOME ~> PropT E := fun _ _ _ => False.

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).

  Definition E_trigger_prop : E ~> PropT (E +' F) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_prop : F ~> PropT (E +' F) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition model_OOM :
    forall T (RR: T -> T -> Prop), PropT (E +' OOME +' F) T -> PropT (E +' F) T :=
    fun T RR Pt (t : itree (E +' F) T) =>
      exists (t' : itree (E +' OOME +' F) T) , Pt t' /\ (interp_prop (case_ E_trigger_prop (case_ OOM_handler F_trigger_prop)) _ RR t' t).

End PARAMS_MODEL.

Definition OOM_exec {E} `{FailureE -< E}: OOME ~> itree E :=
  fun _ e => match e with | ThrowOOM s => raise ("Abort (OOM): " ++ s) end.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).

  Definition E_trigger :  E ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM `{FailureE -< E +' F}:
    itree (E +' OOME +' F) ~> itree (E +' F) :=
    interp (case_ E_trigger (case_ OOM_exec F_trigger)).

End PARAMS_INTERP.
