From Coq Require Import
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Eq
     Events.State
     Events.StateFacts.

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

Section Locals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Definition handle_local {E} `{FailureE -< E} : (LocalE k v) ~> stateT map (itree E) :=
      fun _ e env =>
        match e with
        | LocalWrite k v => ret (Maps.add k v env, tt)
        | LocalRead k =>
            match Maps.lookup k env with
            | Some v => Ret (env, v)
            | None => raise ("Could not look up id " ++ to_string k)
            end
        end.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G H: Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' (LocalE k v) +' G).
    Notation Effout := (E +' F +' G).
    Notation Effin' := (E +' F +' H +' (LocalE k v) +' G).
    Notation Effout' := (E +' F +' H +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition E_trigger' {M} : forall R, E R -> (stateT M (itree Effout') R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger' {M} : forall R, F R -> (stateT M (itree Effout') R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition H_trigger' {M} : forall R, H R -> (stateT M (itree Effout') R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger' {M} : forall R , G R -> (stateT M (itree Effout') R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_h := (case_ E_trigger (case_ F_trigger (case_ handle_local G_trigger))).
    Definition interp_local : itree Effin ~> stateT map (itree Effout) :=
      interp_state interp_local_h.

    Definition interp_local' : itree Effin' ~> stateT map (itree Effout') :=
      interp_state (case_ E_trigger' (case_ F_trigger' (case_ H_trigger' (case_ handle_local G_trigger')))).

    Lemma interp_local_ret :
      forall (R : Type) g (x: R),
        runState (interp_local (Ret x: itree Effin R)) g ≅ Ret (g,x).
    Proof.
      intros; apply interp_state_ret.
    Qed.


  End PARAMS.

End Locals.
