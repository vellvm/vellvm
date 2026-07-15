(* begin hide *)
From Stdlib Require Import
  Morphisms
  String.

From ExtLib Require Import
  Structures.Maps.

From ITree Require Import
  ITree
  Events.State
  Eq.Eqit
  Events.StateFacts
  InterpFacts
  Basics.MonadState.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues.

Import ITree.Basics.Basics.Monads.
(* end hide *)

(** * Global handler
  Interpretation of the [GlobalE] events into a state monad.
*)

Section Globals.
  Context {Pa : Params}.
  Definition global_env := rmap dvalue.
  #[local] Notation map := (global_env).
  
  Definition handle_global {E} `{FailureE -< E} : GlobalE ~> stateT map (itree E) :=
    fun _ e env =>
      match e with
      | GlobalWrite k v => ret (Maps.add k v env, tt)
      | GlobalRead k =>
          match Maps.lookup k env with
          | Some v => Ret (env, v)
          | None => raise ("Could not look up global id " ++ show k)
          end
      end.

  (* See [src/ml/extracted/Extract.v] for the OCaml-side patching: in
     extraction [globals_set]/[globals_get] become a mutable ref-cell that
     gives the OCaml debugger live access to the current globals. The
     Rocq-level defaults below are pure no-ops. *)
  Record debug_globals := mk_debug_globals {
      globals_set : map -> unit ;
      globals_get : unit -> map;
    }.

  Definition globals_object : debug_globals :=
    mk_debug_globals (fun (_:map) => tt) (fun (_:unit) => (Maps.empty : map)).

  Definition update_globals_ref {E} `{FailureE -< E} [T] (e : GlobalE T) : stateT map (itree E) unit :=
    fun gs => ret (gs, globals_object.(globals_set) gs).

  Definition handle_global_debug {E} `{FailureE -< E} : GlobalE ~> stateT map (itree E) :=
    fun _ e =>
      (res <- handle_global e;;
      update_globals_ref e;;
      ret res)%monad.

  Section PARAMS.
    Variable (E F G H : Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' GlobalE +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_global_h := (case_ E_trigger (case_ F_trigger (case_ handle_global_debug G_trigger))).
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

      #[global] Instance eutt_interp_global {R} {b} :
        Proper (eqit eq b b ==> eq ==> eqit eq b b) (@interp_global R).
      Proof using.
        repeat intro.
        unfold interp_global.
        destruct b; subst; rewrite H1;
          reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Globals.

