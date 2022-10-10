(* Structured leaking protocol for passing pointers to and from external calls. *)

From Vellvm Require Import
     Handlers.Handlers
     Numeric.Coqlib
     Syntax.LLVMAst.

From ITree Require Import ITree Eq Events.State Events.StateFacts.
Import ITree.Basics.Basics.Monads.

Variant own := Self | Public | Other.

Inductive logical_block_ext:=
| LBlock (size : N) (bytes : mem_block) (concrete_id : option Z) (o : own) : logical_block_ext.

(* Structured injections, motivated from Compositional CompCert. *)
Record memory_interface := MemoryInterface {
    Memory: concrete_memory * IntMap logical_block_ext;
}.

Definition memory_ext := (memory_interface * frame_stack)%type.
Definition L3_state := (global_env * (local_env * lstack) * memory_ext)%type.

Section call.

  Context (S : Type).

  Definition pure_state {E F} `{E -< F} : E ~> stateT S (itree F)
    := fun _ e s => ITree.bind (trigger e) (fun x => Ret (s, x)).

  Variant stateEff {E : Type -> Type} : Type -> Type :=
    | StateEff {X} : S * E X -> stateEff (S * X).

  Definition handle_stateEff {E F : Type -> Type} `{@stateEff E -< F}:
      E ~> stateT S (itree F) := fun _ e env => trigger (StateEff (env, e)).

  Arguments h_state {_ _}.

  (* Note that this interpretation expects three kinds of events, [stateE S]
     which affect state but are not external calls, [E] corresponding to external
     call events, and [F] corresponding to all other events which are guaranteed to
     not affect state. *)
  Definition interp_call_state {E F} :
      itree (@stateE S +' E +' F) ~> stateT S (itree (@stateEff E +' F)) :=
    interp_state (case_ h_state (case_ handle_stateEff pure_state)).

End call.

Definition handle_external:
  (ExternalCallE +' IntrinsicE +' MemoryE +' PickE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE) ~>
    stateT memory_stack (itree ((@stateEff memory_stack ExternalCallE) +' PickE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE)) :=
    case_ (handle_stateEff memory_stack)
      (case_ handle_intrinsic
          (case_ handle_memory (pure_state memory_stack))).

Definition interp_mcfg3_external {R} (t : itree L0 R) g l :=
  let uvalue_trace   := interp_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack L1_trace l in
  let L3_trace_ext   := interp_state handle_external L2_trace in
  L3_trace_ext.

Definition to_memory_stack (m : memory_ext) : memory_stack.
  red in m.
  do 2 destruct m. destruct Memory0.
  do 2 (split; auto).
  eapply IM.map; [ | exact i].
  clear.
  intro. destruct X; constructor; eauto.
Defined.

Definition to_memory_ext (m : memory_stack) : memory_ext.
  red in m.
  do 2 destruct m.
  do 3 (split; auto).
  eapply IM.map; [ | exact l].
  clear.
  intro. destruct X; constructor; eauto.
  exact Self.
Defined.

Definition handle_memory':
  (ExternalCallE +' IntrinsicE +' MemoryE +' PickE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE) ~>
  stateT memory_ext (itree ((@stateEff memory_ext ExternalCallE) +' PickE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE)).
  refine (case_ (handle_stateEff memory_ext) _).
  refine (case_ _ _).
  - intros ? E σ.
    match goal with | |- itree ?E _ => remember E as ev end.
    unshelve eset (foo := handle_intrinsic (E := ev) E (to_memory_stack σ)); subst; try typeclasses eauto.
    exact (ITree.bind foo (fun '(x, r) => Ret (to_memory_ext x, r))).
  - refine (case_ _ _).
    + intros ? E σ.
      match goal with | |- itree ?E _ => remember E as ev end.
      unshelve eset (foo := handle_memory (E := ev) E (to_memory_stack σ)); subst; try typeclasses eauto.
      exact (ITree.bind foo (fun '(x, r) => Ret (to_memory_ext x, r))).
    + exact (pure_state _).
Defined.
