(* begin hide *)
From Coq Require Import
     Morphisms
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.State
     Eq.Eqit
     Events.StateFacts
     InterpFacts.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Semantics.LLVMEvents
     LLVMAst.

From Mem Require Import
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.
(* end hide *)

(** * Global handler
  Interpretation of the [GlobalE] events into a state monad.
*)

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
    Variable (E F G H : Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' (GlobalE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_global_h := (case_ E_trigger (case_ F_trigger (case_ handle_global G_trigger))).
    Definition interp_global  : itree Effin ~> stateT map (itree Effout) :=
      interp_state interp_global_h.


    Section Structural_Lemmas.

      Lemma interp_global_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) s,
          interp_global (ITree.bind t k) s ≅
                        ITree.bind (interp_global t s) (fun '(s',r) => interp_global (k r) s').
      Proof using.
        intros.
        unfold interp_global.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inversion EQ; reflexivity.
      Qed.

      Lemma interp_global_ret :
        forall (R : Type) g (x: R),
          interp_global (Ret x: itree Effin R) g ≅ Ret (g,x).
      Proof using.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_global_Tau :
        forall {R} (t: itree Effin R) g,
          interp_global (Tau t) g ≅ Tau (interp_global t g).
      Proof using.
        intros.
        unfold interp_global; rewrite interp_state_tau; reflexivity.
      Qed.

      Lemma interp_global_vis_eqit:
        forall (g : map) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_global (Vis e kk) g ≅ ITree.bind (interp_global_h e g) (fun (sx : map * X) => Tau (interp_global (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_global.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_global_vis:
        forall (g : map) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_global (Vis e kk) g ≈ ITree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_global_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_global_trigger:
        forall (g : map) X (e : Effin X),
          interp_global (ITree.trigger e) g ≈ interp_global_h e g.
      Proof using.
        intros.
        unfold interp_global.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_global_bind_trigger_eqit:
        forall (g : map) S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_global (ITree.bind (trigger e) kk) g ≅ ITree.bind (interp_global_h e g) (fun (sx : map * X) => Tau (interp_global (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_global.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_global_bind_trigger:
        forall (g : map) S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_global (ITree.bind (trigger e) kk) g ≈ ITree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_global_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      #[global] Instance eutt_interp_global {R} :
        Proper (eutt eq ==> eq ==> eutt eq) (@interp_global R).
      Proof using.
        repeat intro.
        unfold interp_global.
        subst; rewrite H1.
        reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Globals.

(* YZ TODO : Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   So exposing the specialization here, but it is awkward.
 *)
Module Make (A : ADDRESS)(IP : INTPTR)(SIZEOF : Sizeof)(LLVMEvents : LLVM_INTERACTIONS(A)(IP)(SIZEOF)).
  Definition global_env := FMapAList.alist raw_id LLVMEvents.DV.dvalue.
End Make.
