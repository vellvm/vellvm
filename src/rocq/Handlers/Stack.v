(* begin hide *)
Unset Universe Checking.
From Stdlib Require Import
     List
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.AstLib
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.DynamicValues
     Semantics.LLVMEvents
     Handlers.Local.

From CTree Require Import
  CTree
  Fold
  FoldCTree
  FoldStateT
  Eq
  SBisim.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.
Import MonadNotation.

Import ITree.Basics.Basics.Monads.

Import CategoryOps.
(* end hide *)

(** * Stack handler
  Definition of the handler interpreting the [StackE] events to push and pop the stack of local frames during function calls.
*)

Section StackMap.
  Variable (k v exc :Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.

  Record stack_frame :=
    { stack_vars : map;
      stack_handler : option block_id;
      stack_exc : option exc;
    }.

  Definition stack := list stack_frame.

  #[global] Instance Map_stack_frame : Map k v stack_frame :=
  { empty := Build_stack_frame Maps.empty None None;
    add := fun k v stack_frame => Build_stack_frame (add k v stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc);
    remove := fun k stack_frame => Build_stack_frame (remove k stack_frame.(stack_vars)) stack_frame.(stack_handler) stack_frame.(stack_exc);
    lookup := fun k stack_frame => lookup k stack_frame.(stack_vars);
    union := fun s1 s2 =>
               let var_union := union s1.(stack_vars) s2.(stack_vars) in
               (* Not sure of the order these should merge in... *)
               let handler_union := CFG.opt_first s2.(stack_handler) s1.(stack_handler) in
               let exc_union := CFG.opt_first s2.(stack_exc) s1.(stack_exc) in
               Build_stack_frame var_union handler_union exc_union
  }.

  Definition handle_stack {E BR} `{FailureE -< E} : (StackE k v exc) ~> stateT (stack_frame * stack) (ctree E BR) :=
    fun _ e '(env, stk) =>
      match e with
      | StackPush args =>
          let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args in
          Ret ((Build_stack_frame init None None, env::stk), tt)
      | StackPop =>
          match stk with
          | [] => raise "Tried to pop too many stack frames."
          | (env'::stk') => Ret ((env',stk'), tt)
          end
      | StackSetHandler handler =>
          let new_frame := Build_stack_frame env.(stack_vars) handler env.(stack_exc) in
          Ret ((new_frame, stk), tt)
      | StackHandler =>
          match env with
          | Build_stack_frame stack_vars stack_handler stack_exc =>
              Ret ((env, stk), stack_handler)
          end
      | StackRaise x =>
          let new_frame := Build_stack_frame env.(stack_vars) env.(stack_handler) (Some x) in
          Ret ((new_frame, stk), tt)
      | StackGetExc =>
          match env with
          | Build_stack_frame stack_vars stack_handler stack_exc =>
              Ret ((env, stk), stack_exc)
          end
      end.

    (* Transform a local handler that works on maps to one that works on stacks *)
    Definition handle_local_stack {E BR} `{FailureE -< E} (h:(LocalE k v) ~> stateT stack_frame (ctree E BR)) :
      LocalE k v ~> stateT (stack_frame * stack) (ctree E BR)
      :=
      fun _ e '(env, stk) => CTree.map (fun '(env',r) => ((env',stk), r)) (h _ e env).

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G BR : Type -> Type).
    Context `{FailureE -< E +' F +' G}.
    Notation Effin := (E +' F +' (LocalE k v +' StackE k v exc) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {S} : forall R, E R -> (stateT S (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {S} : forall R, F R -> (stateT S (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {S} : forall R , G R -> (stateT S (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition  interp_local_stack_h (h:(LocalE k v) ~> stateT stack_frame (ctree Effout BR)) :=
      (case_ E_trigger
             (case_ F_trigger
                    (case_ (case_ (handle_local_stack h)
                                  handle_stack)
                           G_trigger))).

    Definition interp_local_stack `{FailureE -< E +' F +' G}  :
      (ctree Effin BR) ~>  stateT (stack_frame * stack) (ctree Effout BR) :=
      interp_state (interp_local_stack_h (handle_local (v:=v))).

    Section Structural_Lemmas.

      Lemma interp_local_stack_bind :
        forall (R S: Type) (t : ctree Effin BR _) (k : R -> ctree Effin BR S) s,
          interp_local_stack (CTree.bind t k) s ≅
                             CTree.bind (interp_local_stack t s)
                             (fun '(s',r) => interp_local_stack (k r) s').
      Proof using.
        intros.
        unfold interp_local_stack.
        setoid_rewrite interp_state_bind.
        upto_bind_eq.
        intros ((?&?)&?); cbn; reflexivity.
      Qed.

      Lemma interp_local_stack_ret :
        forall (R : Type) l (x: R),
          interp_local_stack (Ret x: ctree Effin BR R) l ≅ Ret (l,x).
      Proof using.
        intros; unfold interp_local_stack.
        apply interp_state_ret.
      Qed.

      Lemma interp_local_stack_vis_eqit:
        forall (ls : stack_frame * stack) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ≅ CTree.bind (interp_local_stack_h (handle_local (v:=v)) e ls) (fun (sx : stack_frame * stack * X) => Guard (interp_local_stack (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local_stack.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_stack_vis:
        forall (ls : (stack_frame * stack)) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ~ CTree.bind (interp_local_stack_h (handle_local (v:=v)) e ls) (fun (sx : stack_frame * stack * X) => interp_local_stack (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_stack_vis_eqit.
        upto_bind_eq.
        intros ?; rewrite sb_guard; reflexivity.
      Qed.

      Lemma interp_local_stack_trigger ls X (e : Effin X):
          interp_local_stack (CTree.trigger e) ls ~ interp_local_stack_h (handle_local (v:=v)) e ls.
      Proof using.
        unfold interp_local_stack.
        rewrite interp_state_trigger.
        setoid_rewrite sb_guard.
        setoid_rewrite bind_ret_r.
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
Module Make (A : ADDRESS)(IP : INTPTR)(SIZEOF : Sizeof)(LLVMEvents : LLVM_INTERACTIONS(A)(IP)(SIZEOF)).
  Definition lstack_frame := @stack_frame LLVMEvents.DV.uvalue (list (raw_id * LLVMEvents.DV.uvalue)).
  Definition lstack := @stack LLVMEvents.DV.uvalue (list (raw_id * LLVMEvents.DV.uvalue)).
End Make.
