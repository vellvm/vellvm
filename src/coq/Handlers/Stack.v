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

  Definition handle_stack {E F} `{FailureE +? E -< F} : (StackE k v) ~> stateT (map * stack) (itree F) :=
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
    Definition handle_local_stack {E F} `{FailureE +? E -< F} (h:(LocalE k v) ~> stateT map (itree F)) :
      LocalE k v ~> stateT (map * stack) (itree F)
      :=
      fun _ e '(env, stk) => ITree.map (fun '(env',r) => ((env',stk), r)) (h _ e env).


    Definition interp_local_stack {E1 E2 F}
               `{(LocalE k v) +' (StackE k v) +? E1 -< F}
               `{FailureE +? E2 -< E1}
               (h:(LocalE k v) ~> stateT map (itree _)) :
      (itree F) ~>  stateT (map * stack) (itree E1) :=
      interp_state (over (case_ (handle_local_stack h)
                                 handle_stack)).

End StackMap.
