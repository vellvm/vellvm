From Vellvm.Semantics Require Import
     MemoryParams
     LLVMParams
     LLVMEvents.

From Vellvm.Handlers Require Import
     MemoryModel.

From ITree Require Import
     ITree
     Basics.Basics
     Events.State.

From ExtLib Require Import
     Structures.Monads.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type MemoryInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MM : MemoryModel LP MP).
  Import MM.
  Import LP.Events.

  Section Interpreters.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger : forall R, E R -> (MemStateT (itree Effout) R) :=
      fun R e => lift (trigger e).

    Definition F_trigger : forall R, F R -> (MemStateT (itree Effout) R) :=
      fun R e => lift (trigger e).

    Definition interp_memory_h := case_ E_trigger (case_ handle_intrinsic  (case_ handle_memory F_trigger)).

    Definition interp_memory :
      itree Effin ~> MemStateT (itree Effout) :=
      interp_state interp_memory_h.
  End Interpreters.
End MemoryInterpreter.

Module Make (LP : LLVMParams) (MP : MemoryParams LP) (MM : MemoryModel LP MP) : MemoryInterpreter LP MP MM.
  Include MemoryInterpreter LP MP MM.
End Make.
