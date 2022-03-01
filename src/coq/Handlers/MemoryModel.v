From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

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

(* Module types for memory models to allow different memory models to be plugged in. *)
Module Type MemoryModel (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.
  Import LP.ADDR.

  (* TODO: Clean up / move this stuff *)
  Import LP.PROV.
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


  Class MemMonad (MemState : Type) (M : Type -> Type)
        `{MonadProvenance M} `{MonadStoreID M} `{MonadMemState MemState M}
        `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} : Type
    :=
    { MemMonad_runs_to {A} (ma : M A) (ms : MemState) : option (MemState * A);
    }.

  (* TODO: Should DataLayout be here? 

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  Parameter datalayout : DataLayout.

  (** Datatype for the state of memory *)
  Parameter MemState : Type.
  Parameter initial_memory_state : MemState.

  (** Basic operations on the state of logical memory. *)
  Parameter allocate :
    forall {M : Type -> Type}
      `{MemMonad MemState M},
      dtyp -> M addr.

  Parameter allocated :
    forall {M : Type -> Type}
      `{MemMonad MemState M}
      (ptr : addr),
      M bool.

  Parameter read :
    forall (mem : MemState) (ptr : addr) (t : dtyp), err uvalue.

  Parameter write :
    forall {M : Type -> Type}
      `{MemMonad MemState M}
      (ptr : addr) (v : uvalue) (t : dtyp),
      M unit.

  (** Operations for interacting with the concrete layout of memory. *)
  Parameter reserve_block : MemState -> LP.IP.intptr -> N -> option MemState.

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

End MemoryModel.
