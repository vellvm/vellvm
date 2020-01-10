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

  Definition handle_global {E} `{FailureE -< E} : (GlobalE k v) ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | GlobalWrite k v => ret (Maps.add k v env, tt)
      | GlobalRead k =>
        match Maps.lookup k env with
        | Some v => Ret (env, v)
        | None => raise ("Could not look up global id " ++ to_string k)
        end
      end.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G : Type -> Type).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_global `{FailureE -< E +' F +' G} : itree (E +' F +' (GlobalE k v) +' G) ~> stateT map (itree (E +' F +' G)) :=
      interp_state (case_ E_trigger (case_ F_trigger (case_ handle_global G_trigger))).
  End PARAMS.

End Globals.
