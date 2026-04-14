(* begin hide *)
From Stdlib Require Import
     List
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.StateFacts
     Eq.Eqit
     Events.State.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.AstLib
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.DynamicValues
     Semantics.LLVMParams
     Semantics.LLVMEvents
     Handlers.Local.

From QuickChick Require Import Show.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.
Import MonadNotation.

Import ITree.Basics.Basics.Monads.
(* end hide *)

(** * Stack handler
  Definition of the handler interpreting the [StackE] events to push and pop the stack of local frames during function calls.
*)

Section StackMap.
  Variable (k v exc :Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {S : Show k}.

  Record stack_frame :=
    { stack_vars : map;
      stack_handler : option block_id;
      stack_exc : option exc;
      stack_loc : option string;
    }.

  Definition stack := list stack_frame.

  #[global] Instance Map_stack_frame : Map k v stack_frame :=
  { empty := Build_stack_frame Maps.empty None None None;
    add := fun k v stack_frame => Build_stack_frame (add k v stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc) stack_frame.(stack_loc);
    remove := fun k stack_frame => Build_stack_frame (remove k stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc) stack_frame.(stack_loc);
    lookup := fun k stack_frame => lookup k stack_frame.(stack_vars);
    union := fun s1 s2 =>
               let var_union := union s1.(stack_vars) s2.(stack_vars) in
               (* Not sure of the order these should merge in... *)
               let handler_union := CFG.opt_first s2.(stack_handler) s1.(stack_handler) in
               let exc_union := CFG.opt_first s2.(stack_exc) s1.(stack_exc) in
               let loc_union := CFG.opt_first s1.(stack_loc) s2.(stack_loc) in
               Build_stack_frame var_union handler_union exc_union loc_union
  }.

  (* See src/ml/Extract.v for the special handling of these operation. *)
  Record debug_local_stack := mk_debug_local_stack {
      local_stack_set : stack_frame -> unit ;
      local_stack_get : unit -> stack ;
      local_stack_push : stack_frame -> unit ;
      local_stack_pop : unit -> unit;
    }.

  Definition local_stack_object : debug_local_stack :=
    mk_debug_local_stack (fun (_:stack_frame) => tt) (fun (_:unit) => []) (fun (_:stack_frame) => tt) (fun (_:unit) => tt).

  Definition update_local_stack_ref {M} `{HM: Monad M} {T} (e : LocalE k v T) : stateT stack_frame M unit :=
    (sf <- MonadState.get;;
    ret (local_stack_object.(local_stack_set) sf))%monad.

  Definition handle_stack {E} `{FailureE -< E} : (StackE k v exc) ~> stateT (stack_frame * stack) (itree E) :=
    fun _ e '(env, stk) =>
      match e with
      | StackPush args =>
          let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args in
          let frame := Build_stack_frame init None None (Some (printer_object.(printer_get_loc) tt)) in
          (* Push stack for debugger *)
          ret (local_stack_object.(local_stack_push) frame);;
          Ret ((frame, env::stk), tt)
      | StackPop =>
          match stk with
          | [] => raise "Tried to pop too many stack frames."
          | (env'::stk') =>
              (* Pop stack for debugger *)
              ret (local_stack_object.(local_stack_pop) tt);;
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

    (* Transform a local handler that works on maps to one that works on stacks *)
    Definition handle_local_stack {E} `{FailureE -< E} (h:(LocalE k v) ~> stateT stack_frame (itree E)) :
      LocalE k v ~> stateT (stack_frame * stack) (itree E)
      :=
      fun _ e '(env, stk) => ITree.map (fun '(env',r) => ((env',stk), r)) (h _ e env).

  Definition handle_local_debug_stack {E} `{FailureE -< E} : (LocalE k v) ~> stateT stack_frame (itree E) :=
    fun _ e =>
      (res <- handle_local e;;
      update_local_stack_ref e;;
      ret res)%monad.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< E +' F +' G}.
    Notation Effin := (E +' F +' (LocalE k v +' StackE k v exc) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {S} : forall R, E R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {S} : forall R, F R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {S} : forall R , G R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition  interp_local_stack_h (h:(LocalE k v) ~> stateT stack_frame (itree Effout)) :=
      (case_ E_trigger
             (case_ F_trigger
                    (case_ (case_ (handle_local_stack h)
                                  handle_stack)
                           G_trigger))).

    Definition interp_local_stack `{FailureE -< E +' F +' G}  :
      (itree Effin) ~>  stateT (stack_frame * stack) (itree Effout) :=
      interp_state (interp_local_stack_h handle_local_debug_stack).

    Section Structural_Lemmas.

      Lemma interp_local_stack_bind :
        forall (R S: Type) (t : itree Effin _) (k : R -> itree Effin S) s,
          interp_local_stack (ITree.bind t k) s ≅
                             ITree.bind (interp_local_stack t s)
                             (fun '(s',r) => interp_local_stack (k r) s').
      Proof using.
        intros.
        unfold interp_local_stack.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inversion EQ; reflexivity.
      Qed.

      Lemma interp_local_stack_ret :
        forall (R : Type) l (x: R),
          interp_local_stack (Ret x: itree Effin R) l ≅ Ret (l,x).
      Proof using.
        intros; unfold interp_local_stack.
        apply interp_state_ret.
      Qed.

      Lemma interp_local_stack_vis_eqit:
        forall (ls : stack_frame * stack) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ≅ ITree.bind (interp_local_stack_h handle_local_debug_stack e ls) (fun (sx : stack_frame * stack * X) => Tau (interp_local_stack (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local_stack.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_stack_vis:
        forall (ls : (stack_frame * stack)) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ≈ ITree.bind (interp_local_stack_h handle_local_debug_stack e ls) (fun (sx : stack_frame * stack * X) => interp_local_stack (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_stack_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_local_stack_trigger ls X (e : Effin X):
          interp_local_stack (ITree.trigger e) ls ≈ interp_local_stack_h handle_local_debug_stack e ls.
      Proof using.
        unfold interp_local_stack.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End StackMap.

From ExtLib Require Import
     Data.Map.FMapAList.


(* Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   We are hence exposing the specialization here, but it is slightly awkward.
 *)
Module Make (LP:LLVMParams).
  Definition lstack_frame := @stack_frame LP.DV.uvalue (list (raw_id * LP.DV.uvalue)).
  Definition lstack := @stack LP.DV.uvalue (list (raw_id * LP.DV.uvalue)).
End Make.
