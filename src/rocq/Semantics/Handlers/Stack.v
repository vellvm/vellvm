(* begin hide *)
From ITree Require Import
  ITree
  Events.StateFacts
  Eq.Eqit
  Events.State.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues
  Handlers.Local.

From ExtLib Require Import
  Structures.Maps.

Import ITree.Basics.Basics.Monads.
(* end hide *)

(** * Stack handler
  Definition of the handler interpreting the [StackE] events to push and pop the stack of local frames during function calls.
*)

Section StackMap.
  Context {Pa : Params}.

  Record stack_frame :=
    { stack_vars : local_env;
      stack_exc : option dvalue;
      stack_loc : option string;
    }.
  
  Definition stack := list stack_frame.

  (* See [src/ml/extracted/Extract.v] for the OCaml-side patching: in
     extraction these hooks become a mutable ref-cell that backs the OCaml
     debugger's view of the call stack. Default Rocq implementations are
     pure no-ops. *)
  Record debug_local_stack := mk_debug_local_stack {
      local_stack_set : stack_frame -> unit ;
      local_stack_get : unit -> stack ;
      local_stack_push : stack_frame -> unit ;
      local_stack_pop : unit -> unit;
    }.

  Definition local_stack_object : debug_local_stack :=
    mk_debug_local_stack (fun (_:stack_frame) => tt) (fun (_:unit) => []) (fun (_:stack_frame) => tt) (fun (_:unit) => tt).

  Definition handle_stack {E} `{FailureE -< E} : StackE ~> stateT (stack_frame * stack) (itree E) :=
    fun _ e '(env, stk) =>
      match e with
      | StackPush args =>
          let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args in
          let frame := Build_stack_frame init None (Some (printer_object.(printer_get_loc) tt)) in
          ret (local_stack_object.(local_stack_push) frame);;
          Ret ((frame, env::stk), tt)
      | StackPop =>
          match stk with
          | [] => raise "Tried to pop too many stack frames."
          | (env'::stk') =>
              ret (local_stack_object.(local_stack_pop) tt);;
              Ret ((env',stk'), tt)
          end
      | StackRaise x =>
          let new_frame := Build_stack_frame env.(stack_vars) (Some x) env.(stack_loc) in
          Ret ((new_frame, stk), tt)
      | StackGetExc =>
          (* Consuming read: clear the slot so a landingpad reached without a
             fresh [StackRaise] errors out instead of seeing a stale payload. *)
          let new_frame := Build_stack_frame env.(stack_vars) None env.(stack_loc) in
          Ret ((new_frame, stk), env.(stack_exc))
      end.

  Definition upd_local_sf (env : stack_frame) (l : local_env) : stack_frame :=
    {|
      stack_vars := l ;
      stack_exc := env.(stack_exc) ;
      stack_loc := env.(stack_loc)
    |}.
  
  (* Transform a local handler that works on maps to one that works on stacks.
     Also sync the OCaml-side [local_stack_object] on every local event so the
     debugger sees an up-to-date top frame. The sync is a no-op in pure Rocq
     (see [local_stack_object]) and is replaced by a ref-cell update on
     extraction. *)
  Definition handle_local_stack {E} `{FailureE -< E}
    (h : LocalE ~> stateT local_env (itree E)) :
    LocalE ~> stateT (stack_frame * stack) (itree E) :=
    fun _ e '(env, stk) =>
      ('(lenv, r) <- h _ e env.(stack_vars);;
       let new_frame := upd_local_sf env lenv in
       ret (local_stack_object.(local_stack_set) new_frame);;
       ret ((new_frame, stk), r))%monad.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< E +' F +' G}.
    Notation Effin := (E +' F +' (LocalE +' StackE) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {S} : forall R, E R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {S} : forall R, F R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {S} : forall R , G R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_stack_h
      (h : LocalE ~> stateT local_env (itree Effout)) :=
      (case_ E_trigger
             (case_ F_trigger
                    (case_ (case_ (handle_local_stack h)
                                  handle_stack)
                           G_trigger))).

    Definition interp_local_stack  :
      (itree Effin) ~> stateT (stack_frame * stack) (itree Effout) :=
      interp_state (interp_local_stack_h handle_local_debug).

  End PARAMS.

End StackMap.

