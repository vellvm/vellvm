From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.MonadState.

From Vellvm Require Import
  Utilities
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues.
Import ITree.Basics.Basics.Monads.

(* TODO: move in the right place *)
Definition EOB_to_itree {E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} : EOB ~> itree E :=
  fun T m => match m with
          | raise_oom s => raiseOOM s
          | raise_ub s => raiseUB s
          | raise_error s => raise s
          | raise_ret x => ret x
          end.

Section PARAMS.
  Context {Pa : Params}.
  (* Definition handle_draw {E M} `{FailureE -< E} `{OOME -< E} `{UBE -< E} : DrawE ~> stateT M (itree E) := *)
  (*   fun T '(draw τ) => *)
  (*     fun s => (fun x => (s,x)) <$> EOB_to_itree (default_dvalue_of_dtyp τ). *)
  Definition handle_draw {E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} :
    DrawE ~> itree E :=
    fun T '(draw τ) => EOB_to_itree (default_dvalue_of_dtyp τ).
  
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
