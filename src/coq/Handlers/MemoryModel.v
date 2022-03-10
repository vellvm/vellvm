From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
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
Import MonadNotation.
Open Scope monad_scope.

(* Move this ? *)
Definition store_id := N.
Class MonadStoreID (M : Type -> Type) : Type :=
  { fresh_sid : M store_id;
    get_sid : M store_id;
    put_sid : store_id -> M unit;
  }.

Class MonadMemState (MemState : Type) (M : Type -> Type) : Type :=
  { get_mem_state : M MemState;
    put_mem_state : MemState -> M unit;
  }.

Definition modify_mem_state {M MemState} `{Monad M} `{MonadMemState MemState M} (f : MemState -> MemState) : M MemState :=
  ms <- get_mem_state;;
  put_mem_state (f ms);;
  ret ms.

(* TODO: Add RAISE_PICK or something... May need to be in a module *)
Class MemMonad (MemState : Type) (Provenance : Type) (M : Type -> Type)
      `{Monad M}
      `{MonadProvenance Provenance M} `{MonadStoreID M} `{MonadMemState MemState M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} : Type
  :=
  { MemMonad_runs_to {A} (ma : M A) (ms : MemState) : option (MemState * A);
    MemMonad_lift_stateT
      {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A}
      (ma : M A) : stateT MemState (itree E) A;
  }.

(* Module types for memory models to allow different memory models to be plugged in. *)
Module Type MemoryModel (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.

  Import LP.PROV.
  (* TODO: Should DataLayout be here? 

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  (* Parameter datalayout : DataLayout. *)

  (** Datatype for the state of memory *)
  Parameter MemState : Type.
  Parameter initial_memory_state : MemState.

  Definition MemStateT := stateT MemState.

  Instance MemStateT_MonadProvenance {M} :
    MonadProvenance Provenance (MemStateT M).
  Proof.
  Admitted.

  Instance MemStateT_MonadStoreID {M} :
    MonadStoreID (MemStateT M).
  Proof.
  Admitted.

  Instance MemStateT_MonadMemState {M} :
    MonadMemState MemState (MemStateT M).
  Proof.
    split.
    eapply (MonadState.get).
    eapply (MonadState.put).
  Admitted.

  Parameter free_concrete_space :
    forall (ms : MemState) (phys_addr : Z) (sz : N), bool.

  Definition concrete_memory_pick_post
             (st : MemState * (addr * dtyp)) (phys_addr : Z) : Prop
    := match st with
       | (ms, (a, dt)) =>
           free_concrete_space ms phys_addr (sizeof_dtyp dt) = true
       end.

  Definition PickConcreteMemoryE :=
    @PickE (MemState * (addr * dtyp)) Z concrete_memory_pick_post.

  (* Not sure if we need this yet *)
  Parameter free_logical_space :
    forall (ms : MemState) (ptr : addr) (sz : N), bool.

  Definition PickLogicalMemoryE :=
    @PickE (MemState * dtyp) addr
           (fun '(ms, dt) ptr =>
              free_logical_space ms ptr (sizeof_dtyp dt) = true).

  Instance MemStateT_itree_MemMonad
           {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{PickConcreteMemoryE -< E}
    : MemMonad MemState Provenance (MemStateT (itree E)).
  Admitted.

  (* (** MemMonad *) *)
  (* Parameter MemMonad : Type -> Type. *)

  (* (** Extra monad classes *) *)
  (* Parameter MemMonad_MonadStoreID : MonadStoreID MemMonad. *)
  (* Parameter MemMonad_MonadProvenance : MonadProvenance Provenance MemMonad. *)
  (* Parameter MemMonad_MonadMemState : MonadMemState MemState MemMonad. *)

  (* Parameter MemMonad_RAISE_ERROR : RAISE_ERROR MemMonad. *)
  (* Parameter MemMonad_RAISE_UB : RAISE_UB MemMonad. *)
  (* Parameter MemMonad_RAISE_OOM : RAISE_OOM MemMonad. *)
  (* Parameter MemMonad_RAISE_PICK : RAISE_PICK MemMonad. *)

  (* (* Hack to make typeclass resolution work... *) *)
  (* Hint Resolve MemMonad_MonadStoreID : typeclass_instances. *)
  (* Hint Resolve MemMonad_MonadProvenance : typeclass_instances. *)
  (* Hint Resolve MemMonad_MonadMemState : typeclass_instances. *)
  (* Hint Resolve MemMonad_RAISE_ERROR : typeclass_instances. *)
  (* Hint Resolve MemMonad_RAISE_UB : typeclass_instances. *)
  (* Hint Resolve MemMonad_RAISE_OOM : typeclass_instances. *)
  (* Hint Resolve MemMonad_RAISE_PICK : typeclass_instances. *)

  (* Parameter MemMonad_runs_to : forall {A} (ma : MemMonad A) (ms : MemState), option (MemState * A). *)
  (* Parameter MemMonad_lift_stateT :  *)
  (*   forall {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{PickE -< E} {A} *)
  (*     (ma : MemMonad A), stateT MemState (itree E) A. *)

  (** Basic operations on the state of logical memory. *)
  Parameter allocate :
    forall {M} `{MemMonad MemState Provenance M} (dt : dtyp),
      M addr.

  Parameter allocated :
    forall {M} `{MemMonad MemState Provenance M} (ptr : addr),
      M bool.

  Parameter read :
    forall {M} `{MemMonad MemState Provenance M} (ptr : addr) (t : dtyp), M uvalue.

  Parameter write :
    forall {M} `{MemMonad MemState Provenance M}
      (ptr : addr) (v : uvalue) (t : dtyp),
      M unit.

  (** Operations for interacting with the concrete layout of memory. *)
  Parameter reserve_block : MemState -> LP.IP.intptr -> N -> option MemState.

  Section Handlers.
    (* TODO: Should we generalize the return type? *)
    Parameter handle_memory :
      forall {M} `{MemMonad MemState Provenance M},
      MemoryE ~> M.

    Parameter handle_intrinsic :
      forall {M} `{MemMonad MemState Provenance M},
      IntrinsicE ~> M.
   End Handlers.
End MemoryModel.
