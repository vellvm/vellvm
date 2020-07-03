From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     PropT
     LLVMEvents.

From ITree Require Import
     ITree.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.

Definition UB_handler {E}: UBE ~> PropT E := fun _ _ _ => True.

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).

  Definition E_trigger_prop : E ~> PropT (E +' F) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_prop : F ~> PropT (E +' F) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition model_UB :
    forall T (RR: T -> T -> Prop), PropT (E +' UBE +' F) T -> PropT (E +' F) T :=
    fun T RR Pt (t : itree (E +' F) T) =>
      exists (t' : itree (E +' UBE +' F) T) , Pt t' /\ (interp_prop (case_ E_trigger_prop (case_ UB_handler F_trigger_prop)) _ RR t' t).

End PARAMS_MODEL.

Definition UB_exec {E} `{FailureE -< E}: UBE ~> itree E := fun _ e => match e with | ThrowUB s => raise ("Undefined Behaviour: " ++ s) end.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).

  Definition E_trigger :  E ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_UB `{FailureE -< E +' F}:
    itree (E +' UBE +' F) ~> itree (E +' F) :=
    interp (case_ E_trigger (case_ UB_exec F_trigger)).

End PARAMS_INTERP.

