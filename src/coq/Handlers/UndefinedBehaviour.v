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

Definition UB_handler {E}: UBE ~> PropT (itree E) := fun _ _ _ => True.

Section PARAMS.
  Variable (D E F: Type -> Type).

  Definition D_trigger_prop :  D ~> PropT (itree (D +' E +' F)) :=
    fun R e t => t = r <- trigger e ;; ret r.

  Definition E_trigger_prop :  E ~> PropT (itree (D +' E +' F)) :=
    fun R e t => t = r <- trigger e ;; ret r.

  Definition F_trigger_prop : F ~> PropT (itree (D +' E +' F)) :=
    fun R e t => t = r <- trigger e ;; ret r.

  Definition model_UB :
    PropT (itree (D +' E +' UBE +' F)) ~> PropT (itree (D +' E +' F)) :=
    fun T Pt t =>
      exists t', Pt t' /\ interp_prop (case_ D_trigger_prop (case_ E_trigger_prop (case_ UB_handler F_trigger_prop))) _ t' t.

End PARAMS.

Definition UB_exec {E} `{FailureE -< E}: UBE ~> itree E := fun _ e => match e with | ThrowUB s => raise ("Undefined Behaviour: " ++ s) end.

Section PARAMS.
  Variable (D E F: Type -> Type).

  Definition D_trigger :  D ~> itree (D +' E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition E_trigger :  E ~> itree (D +' E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree (D +' E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition interp_UB `{FailureE -< D +' E +' F}:
    itree (D +' E +' UBE +' F) ~> itree (D +' E +' F) :=
    interp (case_ D_trigger
           (case_ E_trigger (case_ UB_exec F_trigger))).

End PARAMS.

