(* begin hide *)
From Coq Require Import
     Relations
     String
     RelationClasses
     Morphisms.

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
  Notation Effout := (E +' OOME +' F).

  Definition E_trigger_model_prop : E ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_model_prop : F ~> PropT Effout :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  (* Semantics of OOM *)
  Definition OOM_handler : OOME ~> PropT Effout
    := fun T oome source => True.

  Definition refine_OOM_handler {E} `{OOME -< E} : E ~> PropT E
    := fun T e => fun t => t = trigger e.

  Definition refine_OOM_h {T} (RR : relation T) (source target : itree Effout T) : Prop
    := interp_prop refine_OOM_handler _ (Basics.flip RR) target source.

  Definition refine_OOM {T} (RR : relation T) (sources : PropT Effout T) (target : itree Effout T) : Prop
    := exists source, sources source /\ refine_OOM_h RR source target.

End PARAMS_MODEL.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).
  Context `{FailureE -< F}.
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME +' F).

  Definition OOM_exec_fail {E} `{FailureE -< E}: OOME ~> itree E :=
    fun _ e => match e with | ThrowOOM s => raise ("Abort (OOM): " ++ s) end.

  Definition OOM_exec {E} `{OOME -< E} : OOME ~> itree E :=
    fun R e => trigger e.

  Definition E_trigger :  E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM :
    itree Effin ~> itree Effout :=
    interp ITree.trigger.

End PARAMS_INTERP.

Lemma eutt_refine_oom_h :
  forall {T} {E F} (RR : relation T) `{REF: Reflexive _ RR} `{TRANS : Transitive _ RR}
    (t1 t2 : itree (E +' OOME +' F) T),
    eutt RR t1 t2 ->
    refine_OOM_h RR t1 t2.
Proof.
  intros T E F RR REF TRANS t1 t2 H.
  apply eutt_flip in H.
  unfold refine_OOM_h.

  pose proof interp_prop_Proper_eq.
  unfold Proper, respectful in H0.

  eapply H0; eauto.

  apply interp_prop_refl; eauto.
  unfold refine_OOM_handler.
  reflexivity.
Qed.
