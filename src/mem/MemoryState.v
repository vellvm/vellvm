Require Import Vellvm.Syntax.DynamicTypes.

From Vellvm.Semantics Require Import
     LLVMParams
     LLVMEvents
     DynamicValues
     MemoryParams
     MemoryAddress
     Memory.Sizeof
     Memory.Overlaps.

From Vellvm.Utils Require Import
     Error.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From Coq Require Import
     ZArith.

Module Type MemoryTypeSupport.
  Parameter is_supported : dtyp -> Prop.
End MemoryTypeSupport.

Module Type MemoryState (LP : LLVMParams).
  Import LP.PROV.
  Import LP.ADDR.
  Import LP.Events.DV.

  Import MonadNotation.
  Open Scope monad.

  (* TODO: Clean up / move this stuff *)
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

  (** Datatype for the state of memory *)
  Parameter MemState : Type.
  Parameter initial_memory_state : MemState.

  (** Basic operations on the state of memory. *)
  Parameter allocate :
    forall {M : Type -> Type}
      `{Monad M}
      `{MonadMemState MemState}
      `{MonadProvenance M} `{MonadStoreID M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M},
      dtyp -> M addr.

  Parameter allocated :
    forall {M : Type -> Type}
      `{Monad M}
      `{MonadMemState MemState}
      (ptr : addr),
      M bool.

  Parameter read :
    forall (mem : MemState) (ptr : addr) (t : dtyp), err uvalue.

  Parameter write :
    forall {M : Type -> Type}
      `{MonadState MemState}
      `{MonadStoreID M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M}
      (ptr : addr) (v : uvalue) (t : dtyp),
      M unit.

End MemoryState.

(** Lemmas, helper functions, and specifications relating to the state of memory. *)
Module MemoryStateHelpers (LP : LLVMParams) (OVER : Overlaps LP.ADDR) (MS : MemoryState LP) (MTS : MemoryTypeSupport).
  Import LP.PROV.
  Import LP.ADDR.
  Import LP.Events.DV.
  Import MS.
  Import MTS.

  Module OVER_H := OverlapHelpers LP.ADDR LP.SIZEOF OVER.
  Import OVER_H.
  Import LP.SIZEOF.

  Instance MonadState_MonadMemState {M} `{MonadState MemState M} : MonadMemState MemState M
    := {
      get_mem_state := get;
      put_mem_state := put;
    }.

  (** Check if an address is allocated given the state of memory. *)
  Definition addr_allocated (a : addr) (ms : MemState) : bool
    := evalState (allocated a) ms.

    (** Specification of memory state operations *)
  Record ext_memory (m1 : MemState) (a : addr) (τ : dtyp) (v : uvalue) (m2 : MemState) : Prop :=
    {
      (* TODO: might want to extend this so if the size is 0 I know
               what the value of read is... *)
      new_lu  : sizeof_dtyp τ <> 0%N -> read m2 a τ = inr v;
      old_lu  : forall a' τ', addr_allocated a' m1 = true ->
                         no_overlap_dtyp a τ a' τ' = true ->
                         read m2 a' τ' = read m1 a' τ'
    }.

  Definition same_reads (m1 m2 : MemState) : Prop := forall a τ, read m1 a τ = read m2 a τ.

  Record allocate_spec (m1 : MemState) (τ : dtyp) (m2 : MemState) (a : addr) : Prop :=
    {
      was_fresh : addr_allocated a m1 = false;
      is_allocated : ext_memory m1 a τ (UVALUE_Undef τ) m2
    }.

  Record write_spec (m1 : MemState) (a : addr) (v : dvalue) (m2 : MemState) : Prop :=
    {
      was_allocated : addr_allocated a m1 = true;
      is_written    : forall τ, is_supported τ ->
                           dvalue_has_dtyp v τ ->
                           ext_memory m1 a τ (dvalue_to_uvalue v) m2
    }.

  Record read_spec (m : MemState) (a : addr) (τ : dtyp) (v : uvalue) : Prop :=
    {
      is_read : read m a τ = inr v
    }.

  Record ptoi_spec (m1 : MemState) (a : addr) (τ : dtyp) (m2 : MemState) (phys_addr : Z) : Prop :=
    {
      (* If there's already a concrete address associated with addr... It must be the same. *)
      ptoi_already_exists : forall c, has_concrete a m1 c -> m1 = m2 /\ c = phys_addr;
      ptoi_new : (forall c, ~ has_concrete a m1 c) -> (exists c, has_concrete a m2 c
    }
End MemoryStateHelpers.
