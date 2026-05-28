(* begin hide *)
From ITree Require Import
  ITree
  Events.StateFacts
  Eq.Eqit
  Events.State.

From Vellvm Require Import
  Utilities
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues
  Handlers.Local.

From ExtLib Require Import
  Structures.Maps.

From QuickChick Require Import Show.

Import ITree.Basics.Basics.Monads.
(* end hide *)

(** * Stack handler
  Definition of the handler interpreting the [StackE] events to push and pop the stack of local frames during function calls.
*)

Section StackMap.
  Context {Pa : Params}.

  Record stack_frame :=
    { stack_vars : FMapAList.alist raw_id dvalue;
      stack_handler : option block_id;
      stack_exc : option dvalue;
      stack_loc : option string;
    }.
  
  Definition stack := list stack_frame.

  (* #[global] Instance Map_stack_frame : Map raw_id dvalue stack_frame := *)
  (* { empty := Build_stack_frame Maps.empty None None None; *)
  (*   add := fun k v stack_frame => Build_stack_frame (add k v stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc) stack_frame.(stack_loc); *)
  (*   remove := fun k stack_frame => Build_stack_frame (remove k stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc) stack_frame.(stack_loc); *)
  (*   lookup := fun k stack_frame => lookup k stack_frame.(stack_vars); *)
  (*   union := fun s1 s2 => *)
  (*              let var_union := union s1.(stack_vars) s2.(stack_vars) in *)
  (*              (* Not sure of the order these should merge in... *) *)
  (*              let handler_union := CFG.opt_first s2.(stack_handler) s1.(stack_handler) in *)
  (*              let exc_union := CFG.opt_first s2.(stack_exc) s1.(stack_exc) in *)
  (*              let loc_union := CFG.opt_first s1.(stack_loc) s2.(stack_loc) in *)
  (*              Build_stack_frame var_union handler_union exc_union loc_union *)
  (* }. *)

  (* (* See src/ml/Extract.v for the special handling of these operation. *) *)
  (* Record debug_local_stack := mk_debug_local_stack { *)
  (*     local_stack_set : stack_frame -> unit ; *)
  (*     local_stack_get : unit -> stack ; *)
  (*     local_stack_push : stack_frame -> unit ; *)
  (*     local_stack_pop : unit -> unit; *)
  (*   }. *)

  (* Definition local_stack_object : debug_local_stack := *)
  (*   mk_debug_local_stack (fun (_:stack_frame) => tt) (fun (_:unit) => []) (fun (_:stack_frame) => tt) (fun (_:unit) => tt). *)

  (* Definition update_local_stack_ref {M} `{HM: Monad M} {T} (e : LocalE k v T) : stateT stack_frame M unit := *)
  (*   (sf <- MonadState.get;; *)
  (*   ret (local_stack_object.(local_stack_set) sf))%monad. *)

  Definition handle_stack {E} `{FailureE -< E} : StackE ~> stateT (stack_frame * stack) (itree E) :=
    fun _ e '(env, stk) =>
      match e with
      | StackPush args =>
          let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args in
          let frame := Build_stack_frame init None None (Some (printer_object.(printer_get_loc) tt)) in
          (* Push stack for debugger *)
          (* ret (local_stack_object.(local_stack_push) frame);; *)
          Ret ((frame, env::stk), tt)
      | StackPop =>
          match stk with
          | [] => raise "Tried to pop too many stack frames."
          | (env'::stk') =>
              (* Pop stack for debugger *)
              (* ret (local_stack_object.(local_stack_pop) tt);; *)
              Ret ((env',stk'), tt)
          end
      | StackSetHandler handler =>
          let new_frame := Build_stack_frame env.(stack_vars) handler env.(stack_exc) env.(stack_loc) in
          Ret ((new_frame, stk), tt)
      | StackHandler =>
          match env with
          | Build_stack_frame stack_vars stack_handler stack_exc stack_loc =>
              Ret ((env, stk), stack_handler)
          end
      | StackRaise x =>
          let new_frame := Build_stack_frame env.(stack_vars) env.(stack_handler) (Some x) env.(stack_loc) in
          Ret ((new_frame, stk), tt)
      | StackGetExc =>
          match env with
          | Build_stack_frame stack_vars stack_handler stack_exc stack_loc =>
              Ret ((env, stk), stack_exc)
          end
      end.

  Definition upd_local_sf (env : stack_frame) (l : local_env) : stack_frame :=
    {|
      stack_vars := l ;
      stack_handler := env.(stack_handler) ;
      stack_exc := env.(stack_exc) ;
      stack_loc := env.(stack_loc)
    |}.
  
  (* Transform a local handler that works on maps to one that works on stacks *)
  Definition handle_local_stack {E} `{FailureE -< E}
    (h : LocalE ~> stateT local_env (itree E)) :
    LocalE ~> stateT (stack_frame * stack) (itree E) :=
    fun _ e '(env, stk) =>
      ITree.map
        (fun '(lenv,r) => ((upd_local_sf env lenv,stk), r))
        (h _ e env.(stack_vars)).

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
      interp_state (interp_local_stack_h handle_local).

  End PARAMS.

End StackMap.

