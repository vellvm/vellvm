(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.MonadState.

Import Basics.Basics.Monads.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues
  Interfaces.Memory
  Implementations.Memory.
(* end hide *)

(** * Memory handler
    Interpretation of [MemoryE] events into a state monad over the
    memory model.
*)

Section withParams.
  Context {Pa : Params}.
  Context  {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E}.
  Existing Instance MemoryModelPrimitivesV.
  
  Definition handle_memory {E} (h : memM ~> stateT state (itree E))
    : MemoryE ~> stateT state (itree E) :=
    fun T e => h _ (handle_memoryM e).

  Definition fresh_provenance : stateT state (itree E) provenance :=
    fun σ => let p' := next_provenance σ.(state_provenance) in
          ret ({| state_memory_stack := σ.(state_memory_stack) ;
                 state_provenance := p' |} ,p').

  Definition pad_amount (align : N) (offset : N) :=
    ((align - (offset mod align)) mod align)%N.

  Definition pad_to (align : N) (sz : N) :=
    (sz + pad_amount align sz)%N.

  Definition next_key_with_alignment {A} (m : IntMap A) (align : N) : Z :=
    match IM_greatest_key m with
    | Some k => Z.of_N (pad_to align (1 + Z.to_N k))
    | None => 0
    end.

  Fixpoint memM_interp
    : memM ~> stateT state (itree E) :=
    fun T m σ => match m with
              | Mret x => ret (σ, x)
              | Moom s => raiseOOM s
              | Mub s => raiseUB s
              | Merr s => raise s
              | Mget   k => memM_interp (k σ) σ
              | Mput σ' k => memM_interp k σ'
              | Mchoose _ (Cnext_key _ align) k =>
                  memM_interp
                    (k (next_key_with_alignment σ.(state_memory_stack).(Memory_stack_memory) align))
                    σ
              | Mchoose _ Cfresh_prov k => '(σ',p) <- fresh_provenance σ ;; memM_interp (k p) σ'
              (* TODO deal with provenance *)                                                                                  | Mchoose _ Cexposed_prov k => memM_interp (k None) σ
              end
  .
 
(* TODO: Same signature for the model,
   but branching based on ctrees instead. *)
  (*   Fixpoint memM_model *)
  (*   : memM ~> stateT state (itree E). *)
  (*   fun T m σ => match m with *)
  (*             | Mret x => ret (σ, x) *)
  (*             | Moom s => raiseOOM s *)
  (*             | Mub s => raiseUB s *)
  (*             | Merr s => raise s *)
  (*             | Mget   k => memM_interp (k σ) σ *)
  (*             | Mput σ' k => memM_interp k σ' *)
  (*             | Mnext_key k =>  *)
  (*             | Mfresh_prov k => *)
  (*             end *)
  (* . *)
  
  Definition handle_intrinsic {E} (h : memM ~> stateT state (itree E))
    : IntrinsicE ~> stateT state (itree E) :=
    fun T e => h _ (handle_intrinsicM e).

End withParams.

Section PARAMS.
  Context {Pa : Params}.
  Existing Instance MemoryModelPrimitivesV.
  
  Variable (E F G: Type -> Type).
  Context  `{FailureE -< G} `{UBE -< G} `{OOME -< G}.
  Notation Effin := (E +' IntrinsicE +' MemoryE +' G).
  Notation Effout := (E +' G).

  Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  Definition G_trigger {M} : forall R, G R -> (stateT M (itree Effout) R) :=
    fun R e m => r <- trigger e ;; ret (m, r).
  
  Definition interp_memory_h : Effin ~> stateT state (itree Effout) :=
    case_ E_trigger
      (case_ (handle_intrinsic memM_interp) (case_ (handle_memory memM_interp) G_trigger)).
  
  Definition interp_memory : itree Effin ~> stateT state (itree Effout) :=
    interp_state interp_memory_h.

End PARAMS.
