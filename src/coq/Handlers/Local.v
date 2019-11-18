From Coq Require Import
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.State.

From Vellvm Require Import
     LLVMAst
     AstLib
     MemoryAddress
     DynamicValues
     LLVMEvents
     Error.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.

Section Locals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.

  Definition handle_local {E F} `{FailureE +? E -< F} : (LocalE k v) ~> stateT map (itree F) :=
      fun _ e env =>
        match e with
        | LocalWrite k v => ret (Maps.add k v env, tt)
        | LocalRead k =>
            match Maps.lookup k env with
            | Some v => Ret (env, v)
            | None => raise ("Could not look up id " ++ to_string k)
            end
        end.

  Definition interp_local {E1 E2 F} `{LocalE k v +? E1 -< F} `{FailureE +? E2 -< E1}
    : itree F ~> stateT map (itree E1) :=
      interp_state (over handle_local).


End Locals.
