From Vellvm Require Import
     PropT
     LLVMEvents.

From ITree Require Import
     ITree.

From ExtLib Require Import
     Structures.Monads.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.

Definition UB_handler {E}: UBE ~> PropT (itree E) := fun _ _ _ => True.

Section PARAMS.
  Variable (E F: Type -> Type).

  Definition E_trigger_prop : E ~> PropT (itree (E +' F)) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition F_trigger_prop : F ~> PropT (itree (E +' F)) :=
    fun R e => fun t => t = r <- trigger e ;; ret r.

  Definition model_UB :
    PropT (itree (E +' UBE +' F)) ~> PropT (itree (E +' F)) :=
    fun T Pt t =>
      exists t', Pt t' /\ interp_prop (case_ E_trigger_prop (case_ UB_handler F_trigger_prop)) _ t' t.

End PARAMS.

