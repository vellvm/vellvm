(* begin hide *)
From Coq Require Import
     Relations
     String.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.RefineProp
     Utils.Error
     Semantics.LLVMEvents.

From ITree Require Import
     ITree
     Eq.Eq
     Basics.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Handler for out of memory
  Definition of the propositional and executable handlers for out of memory (abort).
  - The model interpret the event as an arbitrary computation : in this model, UB can be anything, but cannot travel back in time.
  - The interpreter simply fails.
*)

(* Technically OOM should refine OOM... *)
Definition OOMProp (X : Type) : Type := OOM X -> Prop.

Definition OOM_handler {E} : OOME ~> fun T => (OOMProp (itree E T)) :=
  fun _ _ oomt =>
    match oomt with
    | Oom msg => True
    | _ => False
    end.

Definition interp_oom_prop {E F} (h_spec : E ~> fun T => OOMProp (itree F T)) :
  forall R (RR: relation R), itree E R -> OOMProp (itree F R).
Admitted.

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).

  Definition E_trigger_prop : E ~> (fun T => OOMProp (itree (E +' F) T)) :=
    fun R e => fun oomt =>
      match oomt with
      | NoOom t => t = r <- trigger e ;; ret r
      | Oom msg => True
      end.

  Definition F_trigger_prop : F ~> (fun T => OOMProp (itree (E +' F) T)) :=
    fun R e => fun oomt =>
      match oomt with
      | NoOom t => t = r <- trigger e ;; ret r
      | Oom msg => True
      end.

  Import PropT.

  Definition model_OOM :
    forall T (RR: T -> T -> Prop), PropT (E +' OOME +' F) T -> OOMProp (itree (E +' F) T) :=
    fun T RR Pt (t : OOM (itree (E +' F) T)) =>
      exists (t' : itree (E +' OOME +' F) T) , Pt t' /\ (interp_oom_prop (case_ E_trigger_prop (case_ OOM_handler F_trigger_prop)) RR t' t).

End PARAMS_MODEL.

Definition OOM_exec {E} `{FailureE -< E}: OOME ~> itree E :=
  fun _ e => match e with | ThrowOOM s => raise ("Abort (OOM): " ++ s) end.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).

  Definition E_trigger :  E ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree (E +' F) :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM `{FailureE -< E +' F}:
    itree (E +' OOME +' F) ~> itree (E +' F) :=
    interp (case_ E_trigger (case_ OOM_exec F_trigger)).

End PARAMS_INTERP.
