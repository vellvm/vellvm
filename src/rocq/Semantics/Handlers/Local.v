(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Maps.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.MonadState.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues.

Import ITree.Basics.Basics.Monads.
(* end hide *)

(** * Local handler
  Interpretation of the [LocalE] events into a state monad.
*)

Section Locals.
  Context {Pa : Params}.
  Definition local_env := rmap dvalue.
  #[local] Notation map := (local_env).

  Definition handle_local {E} `{FailureE -< E} : LocalE ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | LocalWrite k v => ret (Maps.add k v env, tt)
      | LocalRead k =>
        match Maps.lookup k env with
        | Some v => Ret (env, v)
        | None => raise ("Could not look up id " ++ show k)
        end
      end.

  (* See [src/ml/extracted/Extract.v] for the OCaml-side patching: in
     extraction [locals_set]/[locals_get] become a mutable ref-cell that
     gives the OCaml debugger live access to the current locals. The
     Rocq-level defaults below are pure no-ops, so non-extracted reasoning
     is unaffected. *)
  Record debug_locals := mk_debug_locals {
      locals_set : map -> unit ;
      locals_get : unit -> map;
    }.

  Definition locals_object : debug_locals :=
    mk_debug_locals (fun (_:map) => tt) (fun (_:unit) => (Maps.empty : map)).

  Definition update_locals_ref {E} `{FailureE -< E} [T] (e : LocalE T) : stateT map (itree E) unit :=
    fun gs => ret (gs,locals_object.(locals_set) gs).

  Definition handle_local_debug {E} `{FailureE -< E} : LocalE ~> stateT map (itree E) :=
    fun _ e =>
      (res <- handle_local e;;
      update_locals_ref e;;
      ret res)%monad.

  Open Scope monad_scope.
  Section PARAMS.
    Variable (E F G: Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' LocalE +' G).
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
        destruct b; try setoid_rewrite H0; try reflexivity.
      Qed.

      #[global] Instance Proper_interp_local_pointwise {T} {b} :
        Proper (eqit eq b b ==> eq ==> eqit eq b b) (@interp_local T).
      Proof.
        intros ? ? ? ? ? ?; subst.
        unfold interp_local.
        destruct b; rewrite H0;
          reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Locals.

