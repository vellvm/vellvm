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

From Vellvm Require Import
     Utils.PropT.

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME_NOMSG +' F).

  Definition E_trigger_model : E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger_model : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition E_trigger_model_prop : E ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_model_prop : F ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition OOM_msg_handler : OOME ~> itree Effout
    := fun T oome =>
         match oome with
         | ThrowOOM x => trigger ThrowOOM_NOMSG
         end.

  Definition remove_OOM_msg_h : Effin ~> itree Effout
    := case_ E_trigger_model (case_ OOM_msg_handler F_trigger_model).

  Definition remove_OOM_msg : itree Effin ~> itree Effout
    := interp remove_OOM_msg_h.

  (* Semantics of OOM *)
  Definition OOM_handler : OOME_NOMSG ~> PropT Effout
    := fun T oome source => True.

  Definition model_OOM_handler : Effout ~> PropT Effout
    := case_ E_trigger_model_prop (case_ OOM_handler F_trigger_model_prop).

  Definition model_OOM_h {T} (source target : itree Effout T) : Prop
    := interp model_OOM_handler target source.

  Definition model_OOM {T} (sources : PropT Effout T) (target : itree Effout T) : Prop
    := exists source, sources source /\ model_OOM_h source target.

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
