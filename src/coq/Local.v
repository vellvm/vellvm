From Coq Require Import
     String.

From ExtLib Require Import
     Programming.Show
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
     Failure
     Error.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.

Section Locals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Show k}.
  Definition handle_local {E} `{FailureE -< E} : (LocalE k v) ~> stateT map (itree E) :=
      fun _ e env =>
        match e with
        | LocalWrite k v => ret (Maps.add k v env, tt)
        | LocalRead k =>
            match Maps.lookup k env with
            | Some v => Ret (env, v)
            | None => raise ("Could not look up id " ++ to_string k)
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

    Definition run_local `{FailureE -< E +' F +' G} : itree (E +' F +' (LocalE k v) +' G) ~> stateT map (itree (E +' F +' G)) :=
      interp_state (case_ E_trigger (case_ F_trigger (case_ handle_local G_trigger))).
    End PARAMS.
    
End Locals.

