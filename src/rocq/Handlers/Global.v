(* begin hide *)

Unset Universe Checking.
From Stdlib Require Import
     Morphisms
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From Vellvm Require Import
      Handlers.CTreeHandler
     Utils.Util
     Utils.Error
     Utils.Tactics
     Semantics.LLVMEvents
     Semantics.Memory.Sizeof.

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

Import MonadNotation.
Import CategoryOps.
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

  Definition handle_global {E} {BR} `{FailureE -< E} : (GlobalE k v) ~> Monads.stateT map (ctree E BR) :=
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
    Variable (E F G H BR: Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' (GlobalE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (Monads.stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (Monads.stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (Monads.stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_global_h := (case_ E_trigger (case_ F_trigger (case_ handle_global G_trigger))).
    Definition interp_global  : ctree Effin BR ~> Monads.stateT map (ctree Effout BR) :=
      interp_state interp_global_h.


    Section Structural_Lemmas.

      Lemma interp_global_bind:
        forall (R S : Type) (t : ctree Effin BR R) (k : R -> ctree Effin BR S) s,
          interp_global (CTree.bind t k) s ≅
                        CTree.bind (interp_global t s) (fun '(s',r) => interp_global (k r) s').
      Proof using.
        intros.
        unfold interp_global.
        setoid_rewrite interp_state_bind.
        apply equ_clo_bind with (S := Logic.eq).
        reflexivity.
        intros [] [] EQ; inversion EQ; reflexivity.
      Qed.

      Lemma interp_global_ret :
        forall (R : Type) g (x: R),
          interp_global (Ret x: ctree Effin BR R) g ≅ Ret (g,x).
      Proof using.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_global_Guard :
        forall {R} (t: ctree Effin BR R) g,
          interp_global (Guard t) g ≅ Guard (interp_global t g).
      Proof using.
        intros.
        unfold interp_global; rewrite interp_state_guard; reflexivity.
      Qed.

      Lemma interp_global_vis_eqit:
        forall (g : map) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_global (Vis e kk) g ≅ CTree.bind (interp_global_h e g) (fun (sx : map * X) => Guard (interp_global (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_global.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_global_vis:
        forall (g : map) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_global (Vis e kk) g ~ CTree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_global_vis_eqit.
        apply sbisim_bind_eq.
        intros ?. rewrite sb_guard. reflexivity.
      Qed.

      Lemma interp_global_trigger:
        forall (g : map) X (e : Effin X),
          interp_global (CTree.trigger e) g ~ interp_global_h e g.
      Proof using.
        intros.
        unfold interp_global.
        rewrite interp_state_trigger.
        setoid_rewrite sb_guard.
        cbn.
        rewrite bind_ret_r.
        reflexivity.
      Qed.

      Lemma interp_global_bind_trigger_eqit:
        forall (g : map) S X
          (kk : X -> ctree Effin BR S)
          (e : Effin X),
          interp_global (CTree.bind (trigger e) kk) g ≅ CTree.bind (interp_global_h e g) (fun (sx : map * X) => Guard (interp_global (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_global.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_global_bind_trigger:
        forall (g : map) S X
          (kk : X -> ctree Effin BR S)
          (e : Effin X),
          interp_global (CTree.bind (trigger e) kk) g ~ CTree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_global_bind_trigger_eqit.
        apply sbisim_bind_eq.
        intros ?. rewrite sb_guard. reflexivity.
      Qed.

      #[global] Instance equ_interp_global {R} :
        Proper (equ eq ==> eq ==> equ eq) (@interp_global R).
      Proof using.
        repeat intro.
        unfold interp_global.
        subst; rewrite H1;
          reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Globals.


From Vellvm Require Import
     LLVMAst
     MemoryAddress.

(* YZ TODO : Undecided about the status of this over-generalization of these events over domains of keys and values.
   The interface needs to be specialized anyway in [LLVMEvents].
   We want to have access to the specialized type both in [InterpreterMCFG] and [InterpreterCFG] so we cannot delay
   it until [TopLevel] either.
   So exposing the specialization here, but it is awkward.
 *)
Module Make (A : ADDRESS)(IP : INTPTR)(SIZEOF : Sizeof)(LLVMEvents : LLVM_INTERACTIONS(A)(IP)(SIZEOF)).
  Definition global_env := FMapAList.alist raw_id LLVMEvents.DV.dvalue.
End Make.
