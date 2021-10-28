(* begin hide *)
From Coq Require Import
     Relations
     String.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.RefineProp
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
*)

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME_NOMSG +' F).

  Definition E_trigger_model : E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger_model : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition OOM_handler : OOME ~> itree Effout
    := fun T oome =>
         match oome with
         | ThrowOOM x => trigger ThrowOOM_NOMSG
         end.

  Definition model_OOM_h : Effin ~> itree Effout
    := case_ E_trigger_model (case_ OOM_handler F_trigger_model).

  Definition model_OOM : itree Effin ~> itree Effout
    := interp model_OOM_h.

End PARAMS_MODEL.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).
  Context `{FailureE -< F}.
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' F).

  Definition OOM_exec {E} `{FailureE -< E}: OOME ~> itree E :=
    fun _ e => match e with | ThrowOOM s => raise ("Abort (OOM): " ++ s) end.

  Definition E_trigger :  E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM :
    itree Effin ~> itree Effout :=
    interp (case_ E_trigger (case_ OOM_exec F_trigger)).

End PARAMS_INTERP.
