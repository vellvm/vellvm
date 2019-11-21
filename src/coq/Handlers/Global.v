From Coq Require Import
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.State
     Eq.Eq
     Events.StateFacts
     InterpFacts.

From Vellvm Require Import
     Util
     LLVMAst
     AstLib
     MemoryAddress
     DynamicValues
     LLVMEvents
     Error.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.

Section Globals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.

  Definition handle_global {E} `{FailureE -< E} : (GlobalE k v) ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | GlobalWrite k v => ret (Maps.add k v env, tt)
      | GlobalRead k =>
        match Maps.lookup k env with
        | Some v => Ret (env, v)
        | None => raise ("Could not look up global id " ++ to_string k)
        end
      end.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< E +' F +' G}.
    Notation Effin := (E +' F +' (GlobalE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_global  : itree Effin ~> stateT map (itree Effout) :=
      interp_state (case_ E_trigger (case_ F_trigger (case_ handle_global G_trigger))).

    Lemma interp_global_bind :
      forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) s,
        runState (interp_global (ITree.bind t k)) s ≅
         ITree.bind (runState (interp_global t) s) (fun '(s',r) => runState (interp_global (k r)) s').
    Proof.
      intros.
      unfold interp_global.
      setoid_rewrite interp_state_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq).
      reflexivity.
      intros [] [] EQ; inv EQ; reflexivity.
    Qed.

    Lemma interp_global_ret :
      forall (R : Type) g (x: R),
        runState (interp_global (Ret x: itree Effin R)) g ≅ Ret (g,x).
    Proof.
      intros; apply interp_state_ret.
    Qed.

  End PARAMS.

End Globals.
