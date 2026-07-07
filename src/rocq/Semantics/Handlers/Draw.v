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

(** * Draw handler
    Interpretation of [DrawE] (draw an arbitrary dvalue of a given type).
    The executable handler returns the canonical default; the propositional
    spec layer (when wired) makes this non-deterministic.
*)

Section PARAMS.
  Context {Pa : Params}.
  
  Definition handle_draw {E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} :
    DrawE ~> itree E :=
    fun T '(Draw τ) => EOU_to_itree (default_dvalue_of_dtyp τ).
  
  Variable (E G: Type -> Type).
  Notation Effin := (E +' DrawE +' G).
  Notation Effout := (E +' G).
  Context `{FailureE -< G} `{OOME -< G} `{UBE -< G}.
  
  Definition E_trigger : forall R, E R -> itree Effout R :=
    fun R e => trigger e.

  Definition G_trigger : forall R, G R -> itree Effout R :=
    fun R e => trigger e.

  Definition interp_draw_h:  Effin ~> itree Effout :=
    case_ E_trigger (case_ handle_draw G_trigger).
  Definition interp_draw : itree Effin ~> itree Effout :=
    interp interp_draw_h.

End PARAMS.
