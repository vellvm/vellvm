From Coq Require Import
     List
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
     Local
     Error.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.
Import MonadNotation.

Import ITree.Basics.Basics.Monads.

Section StackMap.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.

  Definition stack := list map.

  Definition handle_stack {E} `{FailureE -< E} : (StackE k v) ~> stateT (map * stack) (itree E) :=
      fun _ e '(env, stk) =>
        match e with
        | StackPush bs =>
          let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty bs in
          Ret ((init, env::stk), tt)
        | StackPop =>
          match stk with
          (* CB TODO: should this raise an error? Is this UB? *)
          | [] => raise "Tried to pop too many stack frames."
          | (env'::stk') => Ret ((env',stk'), tt)
          end
        end.

    (* Transform a local handler that works on maps to one that works on stacks *)
    Definition handle_local_stack {E} `{FailureE -< E} (h:(LocalE k v) ~> stateT map (itree E)) :
      LocalE k v ~> stateT (map * stack) (itree E)
      :=
      fun _ e '(env, stk) => ITree.map (fun '(env',r) => ((env',stk), r)) (h _ e env).

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G : Type -> Type).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree (E +' F +' G)) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_stack `{FailureE -< E +' F +' G}
               (h:(LocalE k v) ~> stateT map (itree _)) :
      (itree (E +' F +' ((LocalE k v) +' (StackE k v)) +' G)) ~>  stateT (map * stack) (itree (E +' F +' G)) :=
      interp_state (case_ E_trigger
                   (case_ F_trigger
                   (case_ (case_ (handle_local_stack h)
                                 handle_stack)
                          G_trigger))).
    End PARAMS.


    (* SAZ: I wasn't (yet) able to completey disentangle the ocal events from the stack events.
       This version makes the stack a kind of "wrapper" around the locals and provides a way
       of lifting locals into this new state.

       There should be some kind of lemma long the lines of:

        [forall (t:itree (E +' LocalE k v +' F) V) (env:map) (s:stack),
         run_local t env ≅
         Itree.map fst (run_local_stack (translate _into_stack t) (env, s))]

       Here, [_into_stack : (E +' LocalE k v +' F) ~> (E +' ((LocalE k v) +' StackE k v) +' F)]
       is the inclusion into stack events.
    *)

End StackMap.
