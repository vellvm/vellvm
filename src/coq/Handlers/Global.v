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

Section Globals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.

  Definition handle_global {E F} `{FailureE +? E -< F} : (GlobalE k v) ~> stateT map (itree F) :=
    fun _ e env =>
      match e with
      | GlobalWrite k v => ret (Maps.add k v env, tt)
      | GlobalRead k =>
        match Maps.lookup k env with
        | Some v => Ret (env, v)
        | None => raise ("Could not look up global id " ++ to_string k)
        end
      end.

  Definition interp_global {E1 E2 F} `{GlobalE k v +? E1 -< F} `{FailureE +? E2 -< E1}
    : itree F ~> stateT map (itree E1) :=
      interp_state (over handle_global).

End Globals.
