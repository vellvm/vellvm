(* begin hide *)
From ITree Require Import
     ITree
     Basics.Monad
     Events.State
     Events.StateFacts
     Eq.Eqit.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Params
     Interfaces.Memory
     Implementations.Memory.

From Vellvm Require Import
  Handlers.

Import MonadNotation.
#[local] Notation stateT := Monads.stateT.
#[local] Open Scope monad_scope.
(* end hide *)

Section withParams.
  Context {Pa : Params}.
  Existing Instance MemoryModelPrimitivesV.

  (**
   Interpretation of the trees produced by the denotation of _VIR_ programs.

   The executable interpreter runs in TWO passes rather than one per event
   family:
   - [interp_intrinsics] first: the semantic functions of pure intrinsics
     may themselves emit [MemoryE]/[IntrinsicE] events, which the second
     pass consumes — so this layer cannot be folded into a handler whose
     target signature has no [MemoryE].
   - a single fused [interp_state] pass over the product of the global,
     local/stack and memory states, dispatching every remaining event
     family to the per-family handlers from [Handlers/].

   The fused pass replaces the previous chain
   [interp_global ∘ interp_local_stack ∘ interp_memory ∘ interp_draw]:
   each of those was a full structural rebuild of the tree emitting ~one
   [Tau] per node, so one source event was traversed and re-allocated
   once per layer (see perf/README.md). Per-family interpreters
   ([interp_global], [interp_local_stack], ...) remain available in
   [Handlers/] as the building blocks for layered, spec-side reasoning;
   a future propositional model stack can (and should) stay layered.
   *)

  (* Product of the three threaded states. *)
  Definition FusedS := (state * ((stack_frame * stack) * global_env))%type.

  Definition Res X := (FusedS * X)%type.

  (* Lift a handler acting on one component of [FusedS]. *)
  Definition on_mem {T} (f : stateT state (itree MCFGEbot) T)
    : stateT FusedS (itree MCFGEbot) T :=
    fun '(m, rest) => '(m', r) <- f m;; ret ((m', rest), r).

  Definition on_ls {T} (f : stateT (stack_frame * stack) (itree MCFGEbot) T)
    : stateT FusedS (itree MCFGEbot) T :=
    fun '(m, (ls, g)) => '(ls', r) <- f ls;; ret ((m, (ls', g)), r).

  Definition on_genv {T} (f : stateT global_env (itree MCFGEbot) T)
    : stateT FusedS (itree MCFGEbot) T :=
    fun '(m, (ls, g)) => '(g', r) <- f g;; ret ((m, (ls, g')), r).

  (* Events not interpreted here (external calls, aborts, debug) are
     re-emitted unchanged. *)
  Definition fused_trigger {F} `{F -< MCFGEbot}
    : forall T, F T -> stateT FusedS (itree MCFGEbot) T :=
    fun _ e s => r <- trigger e;; ret (s, r).

  Definition fused_intrinsic : IntrinsicE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e => on_mem (handle_intrinsic memM_interp e).
  Definition fused_global : GlobalE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e => on_genv (handle_global_debug e).
  Definition fused_local : LocalE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e => on_ls (handle_local_stack handle_local_debug e).
  Definition fused_stack : StackE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e => on_ls (handle_stack e).
  Definition fused_memory : MemoryE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e => on_mem (handle_memory memM_interp e).
  Definition fused_draw : DrawE ~> stateT FusedS (itree MCFGEbot) :=
    fun T e s => r <- handle_draw e;; ret (s, r).

  Definition interp_vellvm_h : MCFGEtop ~> stateT FusedS (itree MCFGEbot) :=
    case_ (fused_trigger (F := ExternalCallE))
   (case_ fused_intrinsic
   (case_ fused_global
   (case_ (case_ fused_local fused_stack)
   (case_ fused_memory
   (case_ fused_draw
   (case_ (fused_trigger (F := OOME))
   (case_ (fused_trigger (F := LLVMExcE))
   (case_ (fused_trigger (F := UBE))
   (case_ (fused_trigger (F := DebugE))
          (fused_trigger (F := FailureE))))))))))).

  Definition interp_mcfg {R} (t: MCFGtop R) g l m : MCFGbot (Res R) :=
    interp_state interp_vellvm_h (interp_intrinsics t) (m, (l, g)).

End withParams.
