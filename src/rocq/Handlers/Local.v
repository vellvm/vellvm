(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Monads
  Structures.Maps.

From Vellvm Require Import
  Utils.Util
  Utils.Error
  Utils.Tactics
  Semantics.LLVMEvents
  Semantics.Memory.Sizeof.

Unset Universe Checking.
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
Import ITree.Basics.Basics.Monads.
Import CategoryOps.
Open Scope string_scope.
(* end hide *)

(** * Local handler
  Interpretation of the [LocalE] events into a state monad.
*)

Section Locals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Definition handle_local {E BR} `{FailureE -< E} : (LocalE k v) ~> stateT map (ctree E BR) :=
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
    Variable (E F G H BR: Type -> Type).
    Context `{FailureE -< G}.
    Notation Effin := (E +' F +' (LocalE k v) +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (ctree Effout BR) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_local_h := (case_ E_trigger (case_ F_trigger (case_ handle_local G_trigger))).
    Definition interp_local : ctree Effin BR ~> stateT map (ctree Effout BR) :=
      interp_state interp_local_h.


    Section Structural_Lemmas.

      Lemma interp_local_bind :
        forall (R S : Type) (t : ctree Effin BR R) (k : R -> ctree Effin BR S) s,
          interp_local (CTree.bind t k) s ≅
                       CTree.bind (interp_local t s) (fun '(s',r) => interp_local (k r) s').
      Proof using.
        intros.
        unfold interp_local.
        setoid_rewrite interp_state_bind.
        apply equ_clo_bind_eq.
        intros (?&?).
        reflexivity.
      Qed.

      Lemma interp_local_ret :
        forall (R : Type) l (x: R),
          interp_local (Ret x: ctree Effin BR R) l ≅ Ret (l,x).
      Proof using.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_local_guard :
        forall {R} (t: ctree Effin BR R) l,
          interp_local (Guard t) l ≅ Guard (interp_local t l).
      Proof using.
        intros.
        unfold interp_local; rewrite interp_state_guard; reflexivity.
      Qed.

      Lemma interp_local_vis_eqit:
        forall (g : map) S X
          (kk : X -> ctree Effin BR S)
          (e : Effin X),
          interp_local (Vis e kk) g ≅ CTree.bind (interp_local_h e g) (fun (sx : map * X) => Guard (interp_local (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_vis:
        forall (g : map) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_local (Vis e kk) g ~ CTree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_vis_eqit.
        upto_bind_eq.
        intros ?; rewrite sb_guard; reflexivity.
      Qed.

      Lemma interp_local_trigger:
        forall (g : map) X (e : Effin X),
          interp_local (CTree.trigger e) g ~ interp_local_h e g.
      Proof using.
        intros.
        unfold interp_local.
        rewrite interp_state_trigger.
        setoid_rewrite sb_guard.
        setoid_rewrite bind_ret_r.
        reflexivity.
      Qed.

      Lemma interp_local_bind_trigger_eqit:
        forall (g : map) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_local (CTree.bind (trigger e) kk) g ≅ CTree.bind (interp_local_h e g) (fun (sx : map * X) => Guard (interp_local (kk (snd sx)) (fst sx))).
      Proof using.
        intros.
        unfold interp_local.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_local_trigger_bind:
        forall (g : map) S X (kk : X -> ctree Effin BR S) (e : Effin X),
          interp_local (CTree.bind (trigger e) kk) g ~ CTree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
      Proof using.
        intros.
        rewrite interp_local_bind_trigger_eqit.
        upto_bind_eq.
        intros ?; rewrite sb_guard; reflexivity.
      Qed.

      #[global] Instance Proper_interp_local_equ {T} :
        Proper (equ eq  ==> eq ==> equ eq) (@interp_local T).
      Proof.
        intros ? ? ? ? ? ?; subst.
        rewrite H1.
        reflexivity.
      Qed.

      #[global] Instance Proper_interp_local_sbisim {T} :
        Proper (sbisim eq  ==> eq ==> sbisim eq) (@interp_local T).
      Proof.
        intros ? ? ? ? ? ?; subst.
      Abort.

      #[global] Instance Proper_interp_local_pointwise_equ {T} :
        Proper (equ eq  ==> eq ==> equ eq) (@interp_local T).
      Proof.
        intros ? ? ? ? ? ?; subst.
        unfold interp_local.
        rewrite H1; reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End Locals.


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
  Definition local_env := FMapAList.alist raw_id LLVMEvents.DV.uvalue.
End Make.
