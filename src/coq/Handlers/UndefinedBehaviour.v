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

  Definition model_UB {E F} `{UBE +? E -< F} :
    PropT (itree F) ~> PropT (itree E) :=
    fun T Pt t =>
      exists t', Pt t' /\ interp_prop (over UB_handler) _ t' t.

Definition UB_exec {E F} `{FailureE +? F -< E}: UBE ~> itree E := fun _ e => match e with | ThrowUB s => raise ("Undefined Behaviour: " ++ s) end.

  Definition interp_UB {E F C} `{UBE +? C -< F} `{FailureE +? E -< C}:
    itree F ~> itree C :=
    interp (over UB_exec).

