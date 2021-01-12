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

Section Env.
  Context {map: Type}.
  Context {M: Map OatEvents.var OatEvents.value map}.
  Context {SK: Serialize var}.
  
  (** Here, we have a handler for local events.
      Observe that this simply interprets local events into the statemonad, returning an itree free of OLocalE events *)
  Definition handle_env {E} `{FailureE -< E} : (OEnvE) ~> stateT (map * map) (itree E) :=
    fun _ e '(glob, loc) =>
      match e with
      | OEnvRead id => 
        match Maps.lookup id loc with
        | Some v => Ret ((glob,loc), v)
        | None =>
          (** Didn't find the value in the local environment, look in the globals now! *)
          match Maps.lookup id glob with
          | Some v => Ret ((glob,loc), v)
          | None => raise ("err: Could not find id: " ++ id ++ " in environment")
          end
        end
      | OLocalWrite id v => ret ((glob, Maps.add id v loc), tt)
      | OGlobalWrite id v => ret ((Maps.add id v glob, loc), tt)
      end.

  Open Scope monad_scope.


  (** What we would live to have, is a progressive lowering of interpreted events -
      as we proceed, we can replace triggered events with the appropriate interpretation *)

  (** Ideally, we need a handler from Oat0 ~> stateT map (itree Oat1)
      - a handler that invokes locals when we have a local event, and proceeds onwards otherwise *)


  Definition trigger_rest {M} : Oat1 ~> stateT M (itree Oat1) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  Definition interp_env_lower : Oat0 ~> stateT (map * map) (itree Oat1)  := case_ handle_env trigger_rest.
  Definition interp_env : itree Oat0 ~> stateT (map * map) (itree Oat1) := interp_state interp_env_lower.


  (** TODO, prove structural lemmas *)
End Env.


Section Stack.
  Context {map: Type}.
  Context {M: Map OatEvents.var OatEvents.value map}.
  Context {SK: Serialize var}.

  Definition stack := list map.

  (** Here, we have a handler for stack events.
      Observe that this simply interprets stack events into the statemonad, returning an itree free of stack events *)
  Definition handle_stack : (OStackE) ~> stateT (map * map * stack) (itree Oat2) := 
    (* scope is just the current local environment *)
    fun _ e '(globals, scope, stack) =>
      match e with
      | OStackPush args =>
        let env : map := List.fold_left (fun accmap '(id, v) => Maps.add id v accmap) args Maps.empty in
        ret ((globals, env, scope::stack), tt)
      | OStackPop args =>
        match stack with
        | nil => raise "Tried to pop too many stack frames"
        | (prev_env :: stk') => 
          (* TODO: free the arguments here and return them to previous stack frame *)
          ret ((globals, prev_env, stk'), tt)
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
  Definition  handle_env_stack {E : Type -> Type} `{FailureE -< E}
              (h : OEnvE ~> stateT (map * map) (itree E)) :
    OEnvE ~> stateT (map * map * stack) (itree E)
    :=
      fun _ e '(env, stk) => ITree.map (fun '(env', r) =>
                                          let '(glob, loc) := env' in
                                          ((glob, loc, stk), r)) (h _ e env).

  Open Scope monad_scope.
  Definition trigger_rest' : Oat2 ~> stateT (map * map * stack) (itree Oat2) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  (* Interpret both local and stack events together *)
  Definition interp_env_stack `{FailureE -< Oat0}
             (h : OEnvE ~> stateT (map * map) (itree Oat2))
    : itree Oat0 ~> stateT (map * map * stack) (itree Oat2) :=
   interp_state (case_ (handle_env_stack h)
                (case_ handle_stack trigger_rest')).

  Definition interp_stack_lower : Oat1 ~> stateT (map * map * stack) (itree Oat2) := case_ handle_stack trigger_rest'.
  Definition interp_stack : itree Oat1 ~> stateT (map * map * stack) (itree Oat2) := interp_state interp_stack_lower.

End Stack.
