(* begin hide *)
From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.PropT
     Semantics.LLVMEvents.

From ITree Require Import
     ITree.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Handler for undefined behaviors 
  Definition of the propositional and executable handlers for undefined behaviors.
  - The model interpret the event as an arbitrary computation : in this model, UB can be anything, but cannot travel back in time.
  - The interpreter simply fails.
*)

Definition UB_handler {E}: UBE ~> PropT E := fun _ _ _ => True.

Section PARAMS_MODEL.
  Variable (E F G: Type -> Type).
  Notation Effin := (E +' F +' UBE +' G).
  Notation Effout := (E +' F +' G).

  Definition E_trigger_prop : E ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_prop : F ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition G_trigger_prop : G ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition model_UB :
    forall T (RR: T -> T -> Prop), PropT Effin T -> PropT Effout T :=
    fun T RR Pt (t : itree Effout T) =>
      exists (t' : itree Effin T) ,
        Pt t' /\
          (interp_prop (case_ E_trigger_prop (case_ F_trigger_prop (case_ UB_handler G_trigger_prop))) _ RR t' t).

End PARAMS_MODEL.

Definition UB_exec {E} `{FailureE -< E}: UBE ~> itree E := fun _ e => match e with | ThrowUB s => raise ("Undefined Behaviour: " ++ s) end.

Section PARAMS_INTERP.
  Variable (E F G: Type -> Type).
  Notation Effin := (E +' F +' UBE +' G).
  Notation Effout := (E +' F +' G).

  Definition E_trigger :  E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition G_trigger : G ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_UB `{FailureE -< Effout}:
    itree Effin ~> itree Effout :=
    interp (case_ E_trigger (case_ F_trigger (case_ UB_exec G_trigger))).

End PARAMS_INTERP.
