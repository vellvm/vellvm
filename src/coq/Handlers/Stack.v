From Coq Require Import
     List
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.StateFacts
     Eq.Eq
     Events.State.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Syntax.LLVMAst
     Syntax.AstLib
     Semantics.MemoryAddress
     Semantics.DynamicValues
     Semantics.LLVMEvents
     Handlers.Local.

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
    Context `{FailureE -< E +' F +' G}.
    Notation Effin := (E +' F +' (LocalE k v +' StackE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {S} : forall R, E R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {S} : forall R, F R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {S} : forall R , G R -> (stateT S (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_stack `{FailureE -< E +' F +' G}
               (h:(LocalE k v) ~> stateT map (itree Effout)) :
      (itree Effin) ~>  stateT (map * stack) (itree Effout) :=
      interp_state (case_ E_trigger
                   (case_ F_trigger
                   (case_ (case_ (handle_local_stack h)
                                 handle_stack)
                          G_trigger))).

    Lemma interp_local_stack_bind :
      forall (R S: Type) (t : itree Effin _) (k : R -> itree Effin S) s,
        interp_local_stack (handle_local (v:=v)) (ITree.bind t k) s ≅
        ITree.bind (interp_local_stack (handle_local (v:=v)) t s)
        (fun '(s',r) => interp_local_stack (handle_local (v:=v)) (k r) s').
    Proof.
      intros.
      unfold interp_local_stack.
      setoid_rewrite interp_state_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq).
      reflexivity.
      intros [] [] EQ; inv EQ; reflexivity.
    Qed.

    Lemma interp_local_stack_ret :
      forall (R : Type) l (x: R),
        interp_local_stack (handle_local (v:=v)) (Ret x: itree Effin R) l ≅ Ret (l,x).
    Proof.
      intros; apply interp_state_ret.
    Qed.

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

From ExtLib Require Import
     Data.Map.FMapAList.
From Vellvm Require Import
     LLVMAst
     MemoryAddress.

(* YZ TODO : Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   So exposing the specialization here, but it is awkward.
 *)
Module Make (A : ADDRESS) (LLVMEvents : LLVM_INTERACTIONS(A)).
  Definition lstack := @stack (list (raw_id * LLVMEvents.DV.uvalue)).
End Make.

