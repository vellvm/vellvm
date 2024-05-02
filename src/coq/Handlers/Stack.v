(* begin hide *)
From Coq Require Import
     List
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps
     Data.Map.FMapAList.

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
     Semantics.DynamicValues
     Semantics.LLVMEvents
     Handlers.Local.

From Mem Require Import
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

Require Import Ceres.Ceres.

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

    Definition  interp_local_stack_h (h:(LocalE k v) ~> stateT map (itree Effout)) :=
      (case_ E_trigger
             (case_ F_trigger
                    (case_ (case_ (handle_local_stack h)
                                  handle_stack)
                           G_trigger))).

    Definition interp_local_stack `{FailureE -< E +' F +' G}  :
      (itree Effin) ~>  stateT (map * stack) (itree Effout) :=
      interp_state (interp_local_stack_h (handle_local (v:=v))).

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
        forall (ls : map * stack) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ≅ ITree.bind (interp_local_stack_h (handle_local (v:=v)) e ls) (fun (sx : map * stack * X) => Tau (interp_local_stack (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local_stack.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_stack_vis:
        forall (ls : (map * stack)) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local_stack (Vis e kk) ls ≈ ITree.bind (interp_local_stack_h (handle_local (v:=v)) e ls) (fun (sx : map * stack * X) => interp_local_stack (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_stack_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_local_stack_trigger ls X (e : Effin X):
          interp_local_stack (ITree.trigger e) ls ≈ interp_local_stack_h (handle_local (v:=v)) e ls.
      Proof using.
        unfold interp_local_stack.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End StackMap.

(* Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   We are hence exposing the specialization here, but it is slightly awkward.
 *)
Module Make (A : ADDRESS)(IP : INTPTR)(SIZEOF : Sizeof)(LLVMEvents : LLVM_INTERACTIONS(A)(IP)(SIZEOF)).
  Definition lstack := @stack (list (raw_id * LLVMEvents.DV.uvalue)).
End Make.
