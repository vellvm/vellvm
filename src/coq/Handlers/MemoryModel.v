From Vellvm.Syntax Require Import
     DataLayout.

From Vellvm.Semantics Require Import
     MemoryParams
     LLVMParams
     LLVMEvents.

From Vellvm.Utils Require Import
     Error
     PropT.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

From Coq Require Import
     ZArith.

Import Basics.Basics.Monads.

Require Import Vellvm.Semantics.MemoryAddress.
Require Import Vellvm.Syntax.DynamicTypes.
Require Import Vellvm.Semantics.DynamicValues.
Require Import Vellvm.Semantics.Memory.Sizeof.

Module Type MemoryState (Addr:MemoryAddress.ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PROV : PROVENANCE Addr) (Events : LLVM_INTERACTIONS Addr IP SIZEOF).
  Import PROV.
  Import Addr.
  Import Events.DV.

  Import MonadNotation.
  Open Scope monad.

  Parameter store_id : Type.

  Class MonadProvenance (M : Type -> Type) : Type :=
    { fresh_provenance : M Provenance
    }.

  Class MonadStoreID (M : Type -> Type) : Type :=
    { fresh_sid : M store_id
    }.

  Class MonadMemState (MemState : Type) (M : Type -> Type) : Type :=
    { get_mem_state : M MemState;
      put_mem_state : MemState -> M unit
    }.

  Definition fresh_allocation_id {M} `{Monad M} `{MonadProvenance M} : M AllocationId
    := prov <- fresh_provenance;;
       ret (provenance_to_allocation_id prov).

  (* Datatype for the state of memory *)
  Parameter MemState : Type.
  Parameter initial_memory_state : MemState.

  Parameter allocate :
    forall {M}
      `{Monad M}
      `{MonadMemState MemState}
      `{MonadProvenance M} `{MonadStoreID M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M},
      dtyp -> M addr.

  Parameter allocated :
    forall {M}
      `{Monad M}
      `{MonadMemState MemState}
      (ptr : addr),
      M bool.

  Parameter read :
    forall (mem : MemState) (ptr : addr) (t : dtyp), err uvalue.

  Parameter write :
    forall {M}
      `{MonadState MemState}
      `{MonadStoreID M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M}
      (ptr : addr) (v : uvalue) (t : dtyp),
      M unit.

  Import SIZEOF.

  Record ext_memory (m1 : MemState) (a : addr) (τ : dtyp) (v : uvalue) (m2 : MemState) : Prop :=
    {
      (* TODO: might want to extend this so if the size is 0 I know
               what the value of read is... *)
      new_lu  : sizeof_dtyp τ <> 0%N -> read m2 a τ = inr v;
      old_lu  : forall a' τ', allocated a' m1 ->
                         no_overlap_dtyp a τ a' τ' ->
                         read m2 a' τ' = read m1 a' τ'
    }.

    Definition same_reads (m1 m2 : memory_stack) : Prop := forall a τ, read m1 a τ = read m2 a τ.

    Record allocate_spec (m1 : memory_stack) (τ : dtyp) (m2 : memory_stack) (a : addr) : Prop :=
      {
      was_fresh : ~ allocated a m1;
      is_allocated : ext_memory m1 a τ (UVALUE_Undef τ) m2
      }.

    Record write_spec (m1 : memory_stack) (a : addr) (v : dvalue) (m2 : memory_stack) : Prop :=
      {
      was_allocated : allocated a m1;
      is_written    : forall τ, is_supported τ ->
                           dvalue_has_dtyp v τ ->
                           ext_memory m1 a τ (dvalue_to_uvalue v) m2
      }.

    Record read_spec (m : memory_stack) (a : addr) (τ : dtyp) (v : uvalue) : Prop :=
      {
      is_read : read m a τ = inr v
      }.
End MemoryState.

(* Module types for memory models to allow different memory models to be plugged in. *)
Module Type MemoryModel (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.

  (* TODO: Should DataLayout be here? 

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  Parameter datalayout : DataLayout.

  (* Datatype for the state of memory *)
  Parameter MemState : Type.
  Parameter initial_memory_state : MemState.

  (* TODO: Should we generalize this? *)
  Definition MemStateT := stateT MemState.

  Section Handlers.
    (* TODO: Not 100% sure of the constraints on E. *)

    (* TODO: Should we generalize the return type? *)
    Parameter handle_memory : 
      forall {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E},
        MemoryE ~> MemStateT (itree E).

    Parameter handle_intrinsic :
      forall {E} `{FailureE -< E} `{PickE -< E} `{UBE -< E}, IntrinsicE ~> MemStateT (itree E).
   End Handlers.

  (* For registering a physical address of a given size in memory

     May fail if the block cannot be registered (likely because it
     overlaps with non-free memory).
   *)
  Parameter reserve_block : MemState -> LP.IP.intptr -> N -> option MemState.
End MemoryModel.
