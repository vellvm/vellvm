(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Monads
  Structures.Maps.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts.

From Vellvm Require Import
  Utils.Util
  Utils.Error
  Utils.Tactics
  Semantics.LLVMEvents
  Semantics.LLVMParams
  Semantics.Memory.Sizeof.

From QuickChick Require Import Show.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.
(* end hide *)

(** * Local handler
  Interpretation of the [LocalE] events into a state monad.
*)

Section Locals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {S : Show k}.
  Definition handle_local {E} `{FailureE -< E} : (LocalE k v) ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | LocalWrite k v => ret (Maps.add k v env, tt)
      | LocalRead k =>
        match Maps.lookup k env with
        | Some v => Ret (env, v)
        | None => raise ("Could not look up id " ++ show k)
        end
      end.

  (* See src/ml/Extract.v for the special handling of these operation. *)
  Record debug_locals := mk_debug_locals {
      locals_set : map -> unit ;
      locals_get : unit -> map;
    }.

  Definition locals_object : debug_locals :=
    mk_debug_locals (fun (_:map) => tt) (fun (_:unit) => (Maps.empty : map)).

  Definition update_locals_ref {M} `{HM: Monad M} {T} (e : LocalE k v T) : stateT map M unit :=
    (gs <- MonadState.get;;
    ret (locals_object.(locals_set) gs))%monad.
 
  Definition handle_local_debug {E} `{FailureE -< E} : (LocalE k v) ~> stateT map (itree E) :=
    fun _ e =>
      (res <- handle_local e;;
      update_locals_ref e;;
      ret res)%monad.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G H: Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' (LocalE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_h := (case_ E_trigger (case_ F_trigger (case_ handle_local_debug G_trigger))).
    Definition interp_local : itree Effin ~> stateT map (itree Effout) :=
      interp_state interp_local_h.


    Section Structural_Lemmas.

      Lemma interp_local_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) s,
          interp_local (ITree.bind t k) s ≅
                       ITree.bind (interp_local t s) (fun '(s',r) => interp_local (k r) s').
      Proof using.
        intros.
        unfold interp_local.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inversion EQ; reflexivity.
      Qed.

      Lemma interp_local_ret :
        forall (R : Type) l (x: R),
          interp_local (Ret x: itree Effin R) l ≅ Ret (l,x).
      Proof using.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_local_Tau :
        forall {R} (t: itree Effin R) l,
          interp_local (Tau t) l ≅ Tau (interp_local t l).
      Proof using.
        intros.
        unfold interp_local; rewrite interp_state_tau; reflexivity.
      Qed.

      Lemma interp_local_vis_eqit:
        forall (g : map) S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_local (Vis e kk) g ≅ ITree.bind (interp_local_h e g) (fun (sx : map * X) => Tau (interp_local (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_vis:
        forall (g : map) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local (Vis e kk) g ≈ ITree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_local_trigger:
        forall (g : map) X (e : Effin X),
          interp_local (ITree.trigger e) g ≈ interp_local_h e g.
      Proof using.
        intros.
        unfold interp_local.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_local_bind_trigger_eqit:
        forall (g : map) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local (ITree.bind (trigger e) kk) g ≅ ITree.bind (interp_local_h e g) (fun (sx : map * X) => Tau (interp_local (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_trigger_bind:
        forall (g : map) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_local (ITree.bind (trigger e) kk) g ≈ ITree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      #[global] Instance Proper_interp_local {T} {b} :
        Proper (eqit eq b b ==> Monad.eq1) (@interp_local T).
      Proof.
        intros ? ? ?.
        do 3 red.
        intros a.
        do 2 red.
        destruct b; try setoid_rewrite H1; try reflexivity.
      Qed.

      #[global] Instance Proper_interp_local_pointwise {T} {b} :
        Proper (eqit eq b b ==> eq ==> eqit eq b b) (@interp_local T).
      Proof.
        intros ? ? ? ? ? ?; subst.
        unfold interp_local.
        destruct b; rewrite H1;
          reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Locals.


From Vellvm Require Import
     LLVMAst.

(* YZ TODO : Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   So exposing the specialization here, but it is awkward.
 *)
Module Make (LP:LLVMParams). 
  Definition local_env := FMapAList.alist raw_id LP.DV.uvalue.
End Make.
