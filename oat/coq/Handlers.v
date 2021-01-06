From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     Eq
     Events.State
     Events.StateFacts.

Require Import Ceres.Ceres.
Require Import Oat.OatEvents.
Set Implicit Arguments.
Set Contextual Implicit.
Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.

Section Locals.
  Context {map: Type}.
  Context {M: Map OatEvents.var OatEvents.value map}.
  Context {SK: Serialize var}.

  
  (** Here, we have a handler for local events.
      Observe that this simply interprets local events into the statemonad, returning an itree free of OLocalE events *)
  Definition handle_local {E} `{FailureE -< E} : (OLocalE) ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | OLocalRead id => match Maps.lookup id env with
                         | Some v => Ret (env, v)
                         | None => raise ("Could not lookup id " ++ to_string id)       
                         end
      | OLocalWrite id v => ret (Maps.add id v env, tt)
      end.

  Open Scope monad_scope.


  (** What we would live to have, is a progressive lowering of interpreted events -
      as we proceed, we can replace triggered events with the appropriate interpretation *)

  (** Ideally, we need a handler from Oat0 ~> stateT map (itree Oat1)
      - a handler that invokes locals when we have a local event, and proceeds onwards otherwise *)


  Definition trigger_rest {M} : Oat1 ~> stateT M (itree Oat1) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  Definition interp_local_lower : Oat0 ~> stateT map (itree Oat1)  := case_ handle_local trigger_rest.
  Definition interp_local : itree Oat0 ~> stateT map (itree Oat1) := interp_state interp_local_lower.


  (** TODO, prove structural lemmas *)
End Locals.


Section Stack.
  Context {map: Type}.
  Context {M: Map OatEvents.var OatEvents.value map}.
  Context {SK: Serialize var}.

  Definition stack := list map.

  (** Here, we have a handler for stack events.
      Observe that this simply interprets stack events into the statemonad, returning an itree free of stack events *)
  Definition handle_stack : (OStackE) ~> stateT (map * stack) (itree Oat2) := 
    fun _ e '(scope, stack) =>
      match e with
      | OStackPush args =>
        let env : map := List.fold_left (fun accmap '(id, v) => Maps.add id v accmap) args Maps.empty in
        ret ((env, scope::stack), tt)
      | OStackPop args =>
        match stack with
        | nil => raise "Tried to pop too many stack frames"
        | (prev_env :: stk') => 
          (* TODO: free the arguments here and return them to previous stack frame *)
          ret ((prev_env, stk'), tt)
        (*
        match stack with
          | nil => raise "Tried to pop too many stack frames"
          | (caller_env :: stk') =>
            (** Suppose you had an oat function f that takes a struct and sets it to null.
                This function might not return anything, but it sets its arguments to null.
                We then have to copy the arguments into the previous environment to ensure future computation knows about the silently mutated value 
             *)
            let ids := List.map (fst) args in
            let free_args_env := Maps.filter M (fun k _ => List.existsb (String.eqb k) ids) caller_env in
            (** Rewrite with union *)
            let mutated_env : map := List.fold_left (fun accmap '(id, v) => Maps.add id v accmap)
                                                   args free_args_env in
            ret ((mutated_env, stk'), tt)
         *)
        end
      end.

  (* Literally identical to src/coq/Handlers/Stack.v in vellvm repository *)
  Definition  handle_local_stack {E : Type -> Type} `{FailureE -< E}
              (h : OLocalE ~> stateT map (itree E)) :
    OLocalE ~> stateT (map * stack) (itree E)
    :=
      fun _ e '(env, stk) => ITree.map (fun '(env', r) => ((env', stk), r)) (h _ e env).

  Open Scope monad_scope.
  Definition trigger_rest' : Oat2 ~> stateT (map * stack) (itree Oat2) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  Check Oat2.
  (* Interpret both local and stack events together *)
  Definition interp_local_stack `{FailureE -< Oat0}
             (h : OLocalE ~> stateT map (itree Oat2))
    : itree Oat0 ~> stateT (map * stack) (itree Oat2) :=
   interp_state (case_ (handle_local_stack h)
                (case_ handle_stack trigger_rest')).

  Definition interp_stack_lower : Oat1 ~> stateT (map * stack) (itree Oat2) := case_ handle_stack trigger_rest'.
  Definition interp_stack : itree Oat1 ~> stateT (map * stack) (itree Oat2) := interp_state interp_stack_lower.

End Stack.
