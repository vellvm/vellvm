From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eqit
     Events.StateFacts
     Events.State.

From Mem Require Import
  Addresses.MemoryAddress
  Addresses.Provenance
  MemPropT
  StoreId
  SByte
  MemoryModules.Within.

From Vellvm.Utils Require Import
     Error
     PropT
     Util
     NMaps
     Tactics
     Raise
     Monads
     MapMonadExtra
     MonadReturnsLaws
     MonadEq1Laws
     MonadExcLaws
     Inhabited.

From Vellvm.Numeric Require Import
     Integers.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Wellfounded
     Structures.Equalities.

Require Import Morphisms.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import Basics.Basics.Monads.
Import MonadNotation.

Import Monad.
Import EitherMonad.

From Coq Require Import FunctionalExtensionality.

Class ND (M : Type -> Type) `{HM : Monad M} : Type :=
  { contains : forall A, A -> M A -> Prop
  }.

(*** The core memory model *)
Module Type CORE_MEMORY_MODEL
  (Import ADDR : CORE_ADDRESS)
  (Import SB : SBYTE).

  Parameter Memory : Type.
  Parameter initial_memory : Memory.

  (** Primitive byte reads *)
  Parameter read_byte : Memory -> addr -> SByte -> Prop.
End CORE_MEMORY_MODEL.

Module Type MEMORY_READ_ACCESS
  (Import ADDR : CORE_ADDRESS)
  (Import SB : SBYTE)
  (Import MEM : CORE_MEMORY_MODEL ADDR SB).

  (**
     Whether a pointer can be used to read a byte at the location in
     memory.
   *)
  Parameter read_byte_allowed : Memory -> addr -> Prop.

  Parameter read_byte_allowed_spec :
    forall (m : Memory) (ptr : addr),
    (exists (b : SByte),
        read_byte m ptr b) ->
    read_byte_allowed m ptr.
End MEMORY_READ_ACCESS.

Module Type READABLE_MEMORY (ADDR : CORE_ADDRESS) (SB : SBYTE) := CORE_MEMORY_MODEL ADDR SB <+ MEMORY_READ_ACCESS ADDR SB.

Module Type MEMORY_WRITE_ACCESS
  (Import ADDR : CORE_ADDRESS)
  (Import SB : SBYTE)
  (Import MEM : CORE_MEMORY_MODEL ADDR SB).

  (**
     Whether a pointer can be used to write a byte at the location in
     memory.
   *)
  Parameter write_byte_allowed : Memory -> addr -> Prop.
End MEMORY_WRITE_ACCESS.

Module Type READ_WRITE_MEMORY (ADDR : CORE_ADDRESS) (SB : SBYTE) := READABLE_MEMORY ADDR SB <+ MEMORY_WRITE_ACCESS ADDR SB.

Module MEMORY_WRITES
  (Import ADDR : ADDRESS)
  (Import SB : SBYTE)
  (Import MEM : READ_WRITE_MEMORY ADDR SB).

  (* TODO: This does not belong here *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  (* TODO: Is the old write_byte_spec the implementation of this?

     In the version from the paper, we describe write_byte in terms of
     its effect on reads, and describe it as preserving other
     properties (like the allocations, stack frames, heap, allocation
     ids, and permissions... write_byte_spec was _derived_ from the
     properties of the memory model, it was not a parameter. Why has
     this changed?

     1. The modular memory model may not have a write operation at all.
   *)
  (** The raw write_byte operation *)
  Parameter write_byte : Memory -> addr -> SByte -> Memory -> Prop.

  (** We can look up a new value after writing it to memory *)
  Parameter write_byte_new_lu :
    forall (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory),
      write_byte m1 ptr byte m2 ->
      read_byte m2 ptr byte.

  (** We can look up old values after writing to a disjoint location in memory *)
  Parameter write_byte

  Record set_byte_memory (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory) : Prop :=
    {
      new_lu : read_byte m2 ptr byte;
      old_lu : forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        (forall byte', read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
    }.

  Record write_byte_operation_invariants (m1 m2 : MemState) : Prop :=
    {
      write_byte_op_preserves_allocations : allocations_preserved m1 m2;
      write_byte_op_preserves_frame_stack : frame_stack_preserved m1 m2;
      write_byte_op_preserves_heap : heap_preserved m1 m2;
      write_byte_op_read_allowed : read_byte_allowed_all_preserved m1 m2;
      write_byte_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      write_byte_op_free_allowed : free_byte_allowed_all_preserved m1 m2;
      write_byte_op_allocation_ids : preserve_allocation_ids m1 m2;
    }.

  Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      byte_write_succeeds : write_byte_allowed m1 ptr;
      byte_written : set_byte_memory m1 ptr byte m2;

      write_byte_invariants : write_byte_operation_invariants m1 m2;
    }.

  Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT MemState unit
    :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         write_byte_spec m1 ptr byte m2)
      (fun m1 => ~ write_byte_allowed m1 ptr).
End MEMORY_WRITES.


Module Type MemoryModelSpecPrimitives (ADDR : ADDRESS) (SB : SBYTE).
  Import ADDR.
  Import SB.

  (*** Internal state of memory *)
  Parameter MemState : Type.
  Parameter memory_stack : Type.
  Parameter initial_memory_state : MemState.
  Parameter MemState_get_memory : MemState -> memory_stack.
  Parameter MemState_get_provenance : MemState -> Provenance.
  Parameter MemState_put_memory : memory_stack -> MemState -> MemState.

  (* Type for frames and frame stacks *)
  Parameter Frame : Type.
  Parameter FrameStack : Type.

  (* Heaps *)
  Parameter Heap : Type.

  (* TODO: Should DataLayout be here?

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  (* Parameter datalayout : DataLayout. *)

  (*** Primitives on memory *)
  (** Allocations *)
  (* Holds if a byte is allocated with a given AllocationId *)
  Parameter addr_allocated_prop_memory : addr -> AllocationId -> memory_stack -> Prop.

  (** Frame stacks *)
  (* Check if an address is allocated in a frame *)
  Parameter ptr_in_frame_prop : Frame -> addr -> Prop.

  (* Check for the current frame *)
  Parameter peek_frame_stack_prop : FrameStack -> Frame -> Prop.
  Parameter pop_frame_stack_prop : FrameStack -> FrameStack -> Prop.

  Parameter memory_stack_frame_stack_prop : memory_stack -> FrameStack -> Prop.

  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame_prop f ptr <-> ptr_in_frame_prop f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      firstorder.
  Qed.

  Parameter frame_stack_eqv : FrameStack -> FrameStack -> Prop.
  #[global] Parameter frame_stack_eqv_Equivalence : Equivalence frame_stack_eqv.

  (** Heaps *)

  Parameter root_in_heap_prop : Heap -> addr -> Prop.

  (* 1) heap
     2) root pointer
     3) pointer

     The root pointer is the reference to a block that will be freed.
   *)
  Parameter ptr_in_heap_prop : Heap -> addr -> addr -> Prop.

  (* Memory stack's heap *)
  Parameter memory_stack_heap_prop : memory_stack -> Heap -> Prop.

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_in_heap_prop h root <-> root_in_heap_prop h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap_prop h root ptr <-> ptr_in_heap_prop h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> iff) root_in_heap_prop.
  Proof.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
  Proof.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance heap_Equivalence : Equivalence heap_eqv.
  Proof.
    split.
    - intros h; split.
      + intros root.
        reflexivity.
      + intros root ptr.
        reflexivity.
    - intros h1 h2 EQV.
      firstorder.
    - intros x y z XY YZ.
      split.
      + intros root.
        rewrite XY, YZ.
        reflexivity.
      + intros root ptr.
        rewrite XY, YZ.
        reflexivity.
  Qed.

  (** Provenances *)
  Parameter used_provenance_prop : MemState -> Provenance -> Prop. (* Has a provenance *ever* been used. *)

  (* Allocate a new fresh provenance *)
  Parameter mem_state_fresh_provenance : MemState -> (Provenance * MemState)%type.
  Parameter mem_state_fresh_provenance_fresh :
    forall (ms ms' : MemState) (pr : Provenance),
      mem_state_fresh_provenance ms = (pr, ms') ->
      MemState_get_memory ms = MemState_get_memory ms' /\
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
      ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr.

  (** Lemmas about MemState *)
  Parameter MemState_get_put_memory :
    forall ms mem,
      MemState_get_memory (MemState_put_memory mem ms) = mem.

  #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
    {| ms_get_memory := MemState_get_memory;
      ms_put_memory := MemState_put_memory;
      ms_get_put_memory := MemState_get_put_memory;
    |}.

  #[global] Instance Inhabited_MemState : Inhabited MemState :=
    { inhabitant := initial_memory_state
    }.

End MemoryModelSpecPrimitives.

(** * Stuff that is built upon the memory model specification primitives *)
Module Type MemoryModelSpecDerived (ADDR : ADDRESS) (SB : SBYTE) (MMSP : MemoryModelSpecPrimitives ADDR SB).
  Import ADDR.
  Import SB.
  Import MMSP.

  Definition read_byte_prop (ms : MemState) (ptr : addr) (byte : SByte) : Prop
    := read_byte_prop_memory ptr (MemState_get_memory ms) byte.

  Definition byte_allocated (ms : MemState) (ptr : addr) (aid : AllocationId) : Prop
    := addr_allocated_prop_memory ptr aid (MemState_get_memory ms).

  Definition byte_not_allocated (ms : MemState) (ptr : addr) : Prop
    := forall (aid : AllocationId), ~ byte_allocated ms ptr aid.

  (** Addresses *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  #[global] Instance disjoint_ptr_byte_Symmetric : Symmetric disjoint_ptr_byte.
  Proof.
    unfold Symmetric.
    intros x y H.
    unfold disjoint_ptr_byte; auto.
  Qed.

  (** Utilities *)
  Definition lift_spec_to_MemPropT {A}
             (succeeds_spec : MemState -> A -> MemState -> Prop) (ub_spec : MemState -> Prop) :
    MemPropT MemState A :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          ub_spec m1
      | inr (inr (inl (ERR_message x))) =>
          False
      | inr (inr (inr (m2, res))) =>
          succeeds_spec m1 res m2
      end.

  (*** Predicates *)

  (** Reads *)
  Definition read_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition read_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      read_byte_allowed m1 ptr <-> read_byte_allowed m2 ptr.

  Definition read_byte_prop_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr byte,
      read_byte_prop m1 ptr byte <-> read_byte_prop m2 ptr byte.

  Definition read_byte_preserved (m1 m2 : MemState) : Prop :=
    read_byte_allowed_all_preserved m1 m2 /\ read_byte_prop_all_preserved m1 m2.

  (** Writes *)
  Definition write_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition write_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      write_byte_allowed m1 ptr <-> write_byte_allowed m2 ptr.

  (** Freeing *)
  Definition free_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition free_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      free_byte_allowed m1 ptr <-> free_byte_allowed m2 ptr.

  (** Allocations *)
  Definition allocations_preserved (m1 m2 : MemState) : Prop :=
    forall ptr aid, byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid.

  (** Provenances / allocation ids *)
  Definition extend_provenance (ms : MemState) (new_pr : Provenance) (ms' : MemState) : Prop
    := (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
         ~ used_provenance_prop ms new_pr /\
         used_provenance_prop ms' new_pr.

  Definition preserve_allocation_ids (ms ms' : MemState) : Prop
    := forall p, used_provenance_prop ms p <-> used_provenance_prop ms' p.

  (** Store ids *)
  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop
    := exists ptr byte, read_byte_prop ms ptr byte /\ sbyte_sid byte = sid.

  Definition fresh_store_id (ms : MemState) (new_sid : store_id) : Prop
    := ~ used_store_id_prop ms new_sid.

  (** Frame stack *)
  Definition frame_stack_preserved_memory (m1 m2 : memory_stack) : Prop
    := forall fs,
      memory_stack_frame_stack_prop m1 fs <-> memory_stack_frame_stack_prop m2 fs.

  Definition frame_stack_preserved (m1 m2 : MemState) : Prop
    := frame_stack_preserved_memory (MemState_get_memory m1) (MemState_get_memory m2).

  (* Definition Heap_in_bounds (ms_fin:FinMem.MMEP.MMSP.MemState) : Prop := *)
  (*   let h := Memory64BitIntptr.MMEP.MMSP.mem_state_heap ms_fin in *)
  (*   forall i, is_true (IntMaps.member i h) -> exists ptr, FinPTOI.ptr_to_int ptr = i. *)

  (** Heap *)
  (* SAZ: Add Heap_in_bounds *)
  Definition heap_preserved_memory (m1 m2 : memory_stack) : Prop
    := forall h,
        memory_stack_heap_prop m1 h <-> memory_stack_heap_prop m2 h.

  Definition heap_preserved (m1 m2 : MemState) : Prop
    := heap_preserved_memory (MemState_get_memory m1) (MemState_get_memory m2).

  Definition addr_allocated_prop_memory_preserved (m1 m2 : memory_stack) : Prop
    := forall addr aid,
      addr_allocated_prop_memory addr aid m1 <-> addr_allocated_prop_memory addr aid m2.

  Definition read_byte_prop_memory_preserved (m1 m2 : memory_stack) : Prop
    := forall ptr byte,
      read_byte_prop_memory ptr m1 byte <-> read_byte_prop_memory ptr m2 byte.

  Record memory_stack_eqv (m1 m2 : memory_stack) : Prop :=
    { memory_stack_eqv_preserves_addr_allocated : addr_allocated_prop_memory_preserved m1 m2;
      memory_stack_eqv_preserves_read_byte_MemPropT : read_byte_prop_memory_preserved m1 m2;
      memory_stack_eqv_frame_stack_preserved_memory : frame_stack_preserved_memory m1 m2;
      memory_stack_eqv_heap_preserved_memory : heap_preserved_memory m1 m2;
    }.

  Definition MemState_eqv' (ms1 ms2 : MemState) : Prop :=
    memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) /\
      preserve_allocation_ids ms1 ms2.

  Definition MemState_eqv (ms1 ms2 : MemState) : Prop :=
    preserve_allocation_ids ms1 ms2 /\
      read_byte_preserved ms1 ms2 /\
      write_byte_allowed_all_preserved ms1 ms2 /\
      free_byte_allowed_all_preserved ms1 ms2 /\
      allocations_preserved ms1 ms2 /\
      frame_stack_preserved ms1 ms2 /\
      heap_preserved ms1 ms2.

  Lemma MemState_eqv'_read_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr.
    split; intros RBA;
      red; red in RBA;
      destruct RBA as (aid&ALLOC&ACCESS).
    - exists aid.
      split; auto.
      red; red in ALLOC.
      apply memory_stack_eqv_preserves_addr_allocated0; auto.
    - exists aid.
      split; auto.
      red; red in ALLOC.
      apply memory_stack_eqv_preserves_addr_allocated0; auto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_read_byte_prop_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_prop_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr byte.
    split; intros RBP;
      red; red in RBP.
    - red in memory_stack_eqv_preserves_read_byte_MemPropT0.
      eapply memory_stack_eqv_preserves_read_byte_MemPropT0; eauto.
    - red in memory_stack_eqv_preserves_read_byte_MemPropT0.
      eapply memory_stack_eqv_preserves_read_byte_MemPropT0; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_prop_all_preserved : MemEqv.

  Lemma MemState_eqv'_read_byte_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    red.
    split; eauto with MemEqv.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_preserved : MemEqv.

  Lemma MemState_eqv'_write_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      write_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    eapply MemState_eqv'_read_byte_allowed_all_preserved; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_write_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_free_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      free_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    eapply MemState_eqv'_read_byte_allowed_all_preserved; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_free_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_allocations_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      allocations_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr aid.
    split; intros ALLOC;
      repeat red in ALLOC;
      repeat red;
      eapply memory_stack_eqv_preserves_addr_allocated0; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_allocations_preserved : MemEqv.

  Lemma MemState_eqv'_frame_stack_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      frame_stack_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_frame_stack_preserved : MemEqv.

  Lemma MemState_eqv'_heap_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      heap_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_heap_preserved : MemEqv.

  Lemma MemState_eqv'_MemState_eqv :
    forall ms1 ms2,
      MemState_eqv' ms1 ms2 ->
      MemState_eqv ms1 ms2.
  Proof.
    intros ms1 ms2 EQV.
    destruct EQV.
    split; [|split; [|split; [|split; [|split; [|split]]]]]; eauto with MemEqv.
  Qed.

  (*** Provenance operations *)
  #[global] Instance MemPropT_MonadProvenance : MonadProvenance Provenance (MemPropT MemState).
  Proof.
    (* Need to be careful with allocation ids / provenances (more so than store ids)

       They can never be reused. E.g., if you have a pointer `p` with
       allocation id `aid`, and that block is freed, you can't reuse
       `aid` without causing problems. If you allocate a new block
       with `aid` again, then `p` may still be around and may be able
       to access the block.

       Therefore the MemState has to have some idea of what allocation
       ids have been used in the past, not just the allocation ids
       that are *currently* in use.
    *)
    split.
    - (* fresh_provenance *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_pr]]]]]]]]].
      + exact True.
      + exact False.
      + exact False.
      + exact
          ( extend_provenance ms new_pr ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              free_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Store id operations *)
  #[global] Instance MemPropT_MonadStoreID : MonadStoreId (MemPropT MemState).
  Proof.
    split.
    - (* fresh_sid *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_sid]]]]]]]]].
      + exact True.
      + exact False.
      + exact False.
      + exact
          ( fresh_store_id ms' new_sid /\
              preserve_allocation_ids ms ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              free_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Reading from memory *)
  Record read_byte_spec (ms : MemState) (ptr : addr) (byte : SByte) : Prop :=
    { read_byte_allowed_spec : read_byte_allowed ms ptr;
      read_byte_value : read_byte_prop ms ptr byte;
    }.

  Definition read_byte_spec_MemPropT (ptr : addr) : MemPropT MemState SByte :=
    lift_spec_to_MemPropT
      (fun m1 byte m2 =>
         m1 = m2 /\ read_byte_spec m1 ptr byte)
      (fun m1 => ~ read_byte_allowed m1 ptr).

  (*** Framestack operations *)
  Definition empty_frame (f : Frame) : Prop :=
    forall ptr, ~ ptr_in_frame_prop f ptr.

  Record add_ptr_to_frame (f1 : Frame) (ptr : addr) (f2 : Frame) : Prop :=
    {
      old_frame_lu : forall ptr', disjoint_ptr_byte ptr ptr' ->
                             ptr_in_frame_prop f1 ptr' <-> ptr_in_frame_prop f2 ptr';
      new_frame_lu : ptr_in_frame_prop f2 ptr;
    }.

  Record empty_frame_stack (fs : FrameStack) : Prop :=
    {
      no_pop : (forall f, ~ pop_frame_stack_prop fs f);
      empty_fs_empty_frame : forall f, peek_frame_stack_prop fs f -> empty_frame f;
    }.

  Record push_frame_stack_spec (fs1 : FrameStack) (f : Frame) (fs2 : FrameStack) : Prop :=
    {
      can_pop : pop_frame_stack_prop fs2 fs1;
      new_frame : peek_frame_stack_prop fs2 f;
    }.

  Definition ptr_in_current_frame (ms : MemState) (ptr : addr) : Prop
    := forall fs, memory_stack_frame_stack_prop (MemState_get_memory ms) fs ->
             forall f, peek_frame_stack_prop fs f ->
                  ptr_in_frame_prop f ptr.

  (** mempush *)
  Record mempush_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempush_op_reads : read_byte_preserved m1 m2;
      mempush_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      mempush_op_free_allowed : free_byte_allowed_all_preserved m1 m2;
      mempush_op_allocations : allocations_preserved m1 m2;
      mempush_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempush_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempush_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      fresh_frame :
      forall fs1 fs2 f,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        empty_frame f ->
        push_frame_stack_spec fs1 f fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      mempush_invariants :
      mempush_operation_invariants m1 m2;
    }.

  Definition mempush_spec_MemPropT : MemPropT MemState unit :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         mempush_spec m1 m2)
      (fun m1 => False).

  (** mempop *)
  Record mempop_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempop_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempop_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempop_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      (* all bytes in popped frame are freed. *)
      bytes_freed :
      forall ptr,
        ptr_in_current_frame m1 ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the popped frame have the same allocation status as before *)
      non_frame_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_current_frame m1 ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the popped frame are the same when read *)
      non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_current_frame m1 ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new framestack *)
      pop_frame :
      forall fs1 fs2,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        pop_frame_stack_prop fs1 fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      (* Invariants *)
      mempop_invariants : mempop_operation_invariants m1 m2;
    }.

  Definition cannot_pop (ms : MemState) :=
    forall fs1 fs2,
      memory_stack_frame_stack_prop (MemState_get_memory ms) fs1 ->
      ~ pop_frame_stack_prop fs1 fs2.

  Definition mempop_spec_MemPropT : MemPropT MemState unit :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          False
      | inr (inr (inl (ERR_message x))) =>
          (* Not being able to pop is an error, shouldn't happen *)
          cannot_pop m1
      | inr (inr (inr (m2, res))) =>
          mempop_spec m1 m2
      end.

  (* Add a pointer onto the current frame in the frame stack *)
  Definition add_ptr_to_frame_stack (fs1 : FrameStack) (ptr : addr) (fs2 : FrameStack) : Prop :=
    forall f,
      peek_frame_stack_prop fs1 f ->
      exists f', add_ptr_to_frame f ptr f' /\
              peek_frame_stack_prop fs2 f' /\
              (forall fs1_pop, pop_frame_stack_prop fs1 fs1_pop <-> pop_frame_stack_prop fs2 fs1_pop).

  Fixpoint add_ptrs_to_frame_stack (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) : Prop :=
    match ptrs with
    | nil => frame_stack_eqv fs1 fs2
    | (ptr :: ptrs) =>
        exists fs',
          add_ptrs_to_frame_stack fs1 ptrs fs' /\
            add_ptr_to_frame_stack fs' ptr fs2
    end.

  Lemma add_ptrs_to_frame_stack_equation (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) :
    add_ptrs_to_frame_stack fs1 ptrs fs2 =
      match ptrs with
      | nil => frame_stack_eqv fs1 fs2
      | (ptr :: ptrs) =>
          exists fs',
          add_ptrs_to_frame_stack fs1 ptrs fs' /\
            add_ptr_to_frame_stack fs' ptr fs2
      end.
  Proof.
    induction ptrs; cbn; auto.
  Qed.

  (*** Heap operations *)
  Record empty_heap (h : Heap) : Prop :=
    {
      empty_heap_no_roots : forall root,
        ~ root_in_heap_prop h root;

      empty_heap_no_ptrs : forall root ptr,
        ~ ptr_in_heap_prop h root ptr;
    }.

  Definition root_in_memstate_heap (ms : MemState) (root : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            root_in_heap_prop h root.

  Definition ptr_in_memstate_heap (ms : MemState) (root : addr) (ptr : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            ptr_in_heap_prop h root ptr.

  Record add_ptr_to_heap (h1 : Heap) (root : addr) (ptr : addr) (h2 : Heap) : Prop :=
    {
      old_heap_lu : forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        ptr_in_heap_prop h1 root ptr' <-> ptr_in_heap_prop h2 root ptr';

      old_heap_lu_different_root : forall root',
        disjoint_ptr_byte root root' ->
        forall ptr', ptr_in_heap_prop h1 root' ptr' <-> ptr_in_heap_prop h2 root' ptr';

      old_heap_roots : forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';

      new_heap_lu :
      ptr_in_heap_prop h2 root ptr;

      new_heap_root :
      root_in_heap_prop h2 root;
    }.

  Fixpoint add_ptrs_to_heap' (h1 : Heap) (root : addr) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: ptrs) =>
        exists h',
        add_ptrs_to_heap' h1 root ptrs h' /\
          add_ptr_to_heap h' root ptr h2
    end.

  Definition add_ptrs_to_heap (h1 : Heap) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: _) =>
        add_ptrs_to_heap' h1 ptr ptrs h2
    end.

  (*** Writing to memory *)
  Record set_byte_memory (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      new_lu : read_byte_spec m2 ptr byte;
      old_lu : forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        (forall byte', read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
    }.

  Record write_byte_operation_invariants (m1 m2 : MemState) : Prop :=
    {
      write_byte_op_preserves_allocations : allocations_preserved m1 m2;
      write_byte_op_preserves_frame_stack : frame_stack_preserved m1 m2;
      write_byte_op_preserves_heap : heap_preserved m1 m2;
      write_byte_op_read_allowed : read_byte_allowed_all_preserved m1 m2;
      write_byte_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      write_byte_op_free_allowed : free_byte_allowed_all_preserved m1 m2;
      write_byte_op_allocation_ids : preserve_allocation_ids m1 m2;
    }.

  Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      byte_write_succeeds : write_byte_allowed m1 ptr;
      byte_written : set_byte_memory m1 ptr byte m2;

      write_byte_invariants : write_byte_operation_invariants m1 m2;
    }.

  Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT MemState unit
    :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         write_byte_spec m1 ptr byte m2)
      (fun m1 => ~ write_byte_allowed m1 ptr).

  (*** Allocation utilities *)
  Record block_is_free (m1 : MemState) (len : nat) (pr : Provenance) (ptr : addr) (ptrs : list addr) : Prop :=
    { block_is_free_consecutive : ret ptrs {{m1}} ∈ {{m1}} get_consecutive_ptrs ptr len;
      block_is_free_ptr_provenance : address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr); (* Need this case if `ptrs` is empty (allocating 0 bytes) *)
      block_is_free_ptrs_provenance : forall ptr, In ptr ptrs -> address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr);

      (* Actual free condition *)
      block_is_free_bytes_are_free : forall ptr, In ptr ptrs -> byte_not_allocated m1 ptr;
    }.

  Definition find_free_block (len : nat) (pr : Provenance) : MemPropT MemState (addr * list addr)%type
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             True
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr, ptrs)))) =>
             m1 = m2 /\ block_is_free m1 len pr ptr ptrs
         end.

  Record extend_read_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_read_byte_allowed_new_reads :
      forall p, In p ptrs ->
           read_byte_allowed m2 p;

      extend_read_byte_allowed_old_reads :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_allowed m1 ptr' <-> read_byte_allowed m2 ptr';
    }.

  Record extend_reads (m1 : MemState) (ptrs : list addr) (bytes : list SByte) (m2 : MemState) : Prop :=
    { extend_reads_new_reads :
      forall p ix byte,
        Util.Nth ptrs ix p ->
        Util.Nth bytes ix byte ->
        read_byte_prop m2 p byte;

      extend_reads_old_reads :
      forall ptr' byte,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_prop m1 ptr' byte <-> read_byte_prop m2 ptr' byte;
    }.

  Record extend_write_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_write_byte_allowed_new_writes :
      forall p, In p ptrs ->
           write_byte_allowed m2 p;

      extend_write_byte_allowed_old_writes :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        write_byte_allowed m1 ptr' <-> write_byte_allowed m2 ptr';
    }.

  Record extend_free_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_free_byte_allowed_new :
      forall p, In p ptrs ->
           free_byte_allowed m2 p;

      extend_free_byte_allowed_old :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        free_byte_allowed m1 ptr' <-> free_byte_allowed m2 ptr';
    }.

  Definition extend_stack_frame (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    forall fs1 fs2,
      memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
      add_ptrs_to_frame_stack fs1 ptrs fs2 ->
      memory_stack_frame_stack_prop (MemState_get_memory m2) fs2.

  (*
    SAZ TODO: add Heap_in_bounds
  *)
  Definition extend_heap (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    forall h1 h2,
      memory_stack_heap_prop (MemState_get_memory m1) h1 ->
      add_ptrs_to_heap h1 ptrs h2 ->
      memory_stack_heap_prop (MemState_get_memory m2) h2.

  Record extend_allocations (m1 : MemState) (ptrs : list addr) (pr : Provenance) (m2 : MemState) : Prop :=
    { extend_allocations_bytes_now_allocated :
      forall ptr, In ptr ptrs -> byte_allocated m2 ptr (provenance_to_allocation_id pr);

      extend_allocations_old_allocations_preserved :
      forall ptr aid,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr) ->
        (byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid);
    }.

  (*** Allocating bytes on the stack *)
  (* Post conditions for actually reserving bytes in memory and allocating them in the current stack frame *)
  Record allocate_bytes_post_conditions
    (m1 : MemState) (init_bytes : list SByte)
    (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr)
    : Prop :=
    { allocate_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      allocate_bytes_extended_allocations : extend_allocations m1 ptrs pr m2;

      (* read permissions *)
      alloc_bytes_extended_reads_allowed : extend_read_byte_allowed m1 ptrs m2;

      (* reads *)
      alloc_bytes_extended_reads : extend_reads m1 ptrs init_bytes m2;

      (* write permissions *)
      alloc_bytes_extended_writes_allowed : extend_write_byte_allowed m1 ptrs m2;

      (* Add allocated bytes onto the stack frame *)
      allocate_bytes_add_to_frame : extend_stack_frame m1 ptrs m2;

      (* Heap preserved *)
      allocate_bytes_heap_preserved :
      heap_preserved m1 m2;
    }.

  Definition allocate_bytes_post_conditions_MemPropT
    (init_bytes : list SByte)
    (prov : Provenance) (ptr : addr) (ptrs : list addr)
    : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             False
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr', ptrs')))) =>
             allocate_bytes_post_conditions m1 init_bytes prov m2 ptr ptrs /\ ptr = ptr' /\ ptrs = ptrs'
         end.

  Definition allocate_bytes_with_pr_spec_MemPropT
    (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState addr
    := '(ptr, ptrs) <- find_free_block (length init_bytes) prov;;
       allocate_bytes_post_conditions_MemPropT init_bytes prov ptr ptrs;;
       ret ptr.

  Definition allocate_bytes_spec_MemPropT
    (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       allocate_bytes_with_pr_spec_MemPropT init_bytes prov.

  (*** Allocating bytes in the heap *)
  Record malloc_bytes_post_conditions (m1 : MemState) (init_bytes : list SByte) (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr) : Prop :=
    { (* Provenance *)
      malloc_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      malloc_bytes_extended_allocations : extend_allocations m1 ptrs pr m2;

      (* read permissions *)
      malloc_bytes_extended_reads_allowed : extend_read_byte_allowed m1 ptrs m2;

      (* reads *)
      malloc_bytes_extended_reads : extend_reads m1 ptrs init_bytes m2;

      (* write permissions *)
      malloc_bytes_extended_writes_allowed : extend_write_byte_allowed m1 ptrs m2;

      (* free permissions *)
      (* TODO: See #312, need to add this condition back later, but this currently complicates things *)
      (* free_root_allowed covers the case where 0 bytes are allocated *)
      (* malloc_bytes_extended_free_root_allowed : extend_free_byte_allowed m1 [ptr] m2; *)
      malloc_bytes_extended_free_allowed : extend_free_byte_allowed m1 ptrs m2;

      (* Framestack preserved *)
      malloc_bytes_frame_stack_preserved : frame_stack_preserved m1 m2;

      (* Heap extended *)
      malloc_bytes_add_to_frame : extend_heap m1 ptrs m2;
    }.

  Definition malloc_bytes_post_conditions_MemPropT (init_bytes : list SByte) (prov : Provenance) (ptr : addr) (ptrs : list addr) : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             False
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr', ptrs')))) =>
             malloc_bytes_post_conditions m1 init_bytes prov m2 ptr ptrs /\ ptr = ptr' /\ ptrs = ptrs'
         end.

  Definition malloc_bytes_with_pr_spec_MemPropT (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState addr
    := '(ptr, ptrs) <- find_free_block (length init_bytes) prov;;
       malloc_bytes_post_conditions_MemPropT init_bytes prov ptr ptrs;;
       ret ptr.

  Definition malloc_bytes_spec_MemPropT (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       malloc_bytes_with_pr_spec_MemPropT init_bytes prov.

  (*** Freeing heap allocations *)
  Record free_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      free_op_allocation_ids : preserve_allocation_ids m1 m2;
      free_frame_stack_preserved : frame_stack_preserved m1 m2;
    }.

  Record free_block_prop (h1 : Heap) (root : addr) (h2 : Heap) : Prop :=
    { free_block_ptrs_freed :
      forall ptr,
        ptr_in_heap_prop h1 root ptr ->
        ~ ptr_in_heap_prop h2 root ptr;

      free_block_root_freed :
      ~ root_in_heap_prop h2 root;

      (* TODO: make sure there's no weirdness about multiple roots *)
      free_block_disjoint_preserved :
      forall ptr root',
        disjoint_ptr_byte root root' ->
        ptr_in_heap_prop h1 root' ptr <-> ptr_in_heap_prop h2 root' ptr;

      free_block_disjoint_roots :
      forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';
    }.

  Record free_preconditions (m1 : MemState) (root : addr) : Prop :=
    { (* ptr being freed was a root *)
      free_was_root :
      root_in_memstate_heap m1 root;

      (* root being freed was allocated *)
      free_was_allocated :
      exists aid, byte_allocated m1 root aid;

      (* ptrs in block were allocated *)
      free_block_allocated :
      forall ptr,
        ptr_in_memstate_heap m1 root ptr ->
        exists aid, byte_allocated m1 ptr aid;

      (* root is allowed to be freed *)
      (* TODO: add this back. #312 / #313 *)
      (* Running into problems with exec_correct_free because of the
         implementation with size 0 allocations / frees *)
      (* free_root_allowed :
         free_byte_allowed m1 root; *)
    }.

  Record free_spec (m1 : MemState) (root : addr) (m2 : MemState) : Prop :=
    { (* all bytes in block are freed. *)
      free_bytes_freed :
      forall ptr,
        ptr_in_memstate_heap m1 root ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the block have the same allocation status as before *)
      free_non_block_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the freed block are the same when read *)
      free_non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new heap *)
      free_block :
      forall h1 h2,
        memory_stack_heap_prop (MemState_get_memory m1) h1 ->
        memory_stack_heap_prop (MemState_get_memory m2) h2 ->
        free_block_prop h1 root h2;

      (* Invariants *)
      free_invariants : free_operation_invariants m1 m2;
    }.

  Definition free_spec_MemPropT (root : addr) : MemPropT MemState unit :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         free_preconditions m1 root /\ free_spec m1 root m2)
      (fun m1 => ~ free_preconditions m1 root).

  (*** Aggregate things *)

  (** Reading uvalues *)
  Definition read_bytes_spec (ptr : addr) (len : nat) : MemPropT MemState (list SByte) :=
    (* TODO: should this OOM, or should this count as walking outside of memory and be UB? *)
    ptrs <- get_consecutive_ptrs ptr len;;

    (* Actually perform reads *)
    map_monad (fun ptr => read_byte_spec_MemPropT ptr) ptrs.

  Definition read_uvalue_spec (dt : dtyp) (ptr : addr) : MemPropT MemState uvalue :=
    bytes <- read_bytes_spec ptr (N.to_nat (sizeof_dtyp dt));;
    lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

  (** Writing uvalues *)
  Definition write_bytes_spec (ptr : addr) (bytes : list SByte) : MemPropT MemState unit :=
    ptrs <- get_consecutive_ptrs ptr (length bytes);;
    let ptr_bytes := zip ptrs bytes in

    (* TODO: double check that this is correct... Should we check if all writes are allowed first? *)
    (* Actually perform writes *)
    map_monad_ (fun '(ptr, byte) => write_byte_spec_MemPropT ptr byte) ptr_bytes.

  Definition write_uvalue_spec (dt : dtyp) (ptr : addr) (uv : uvalue) : MemPropT MemState unit :=
    bytes <- serialize_sbytes uv dt;;
    write_bytes_spec ptr bytes.

  (** Allocating dtyps *)
  (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
  Definition allocate_dtyp_spec (dt : dtyp) (num_elements : N) : MemPropT MemState addr :=
    MemPropT_assert_pre (dt <> DTYPE_Void);;
    sid <- fresh_sid;;
    element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
    let bytes := concat element_bytes in
    allocate_bytes_spec_MemPropT bytes.

  (** memcpy spec *)
  Definition memcpy_spec (src dst : addr) (len : Z) (volatile : bool) : MemPropT MemState unit :=
    if Z.ltb len 0
    then
      raise_ub "memcpy given negative length."
    else
      (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
       *)
      if orb (no_overlap dst len src len)
             (Z.eqb (ptr_to_int src) (ptr_to_int dst))
      then
        src_bytes <- read_bytes_spec src (Z.to_nat len);;

        (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
        write_bytes_spec dst src_bytes
      else
        raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

  (** memset spec *)
  Definition memset_spec (dst : addr) (val : int8) (len : Z) (sid : store_id) (volatile : bool) : MemPropT MemState unit :=
    if Z.ltb len 0
    then
      raise_ub "memset given negative length."
    else
      let byte := uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid in
      write_bytes_spec dst (repeatN (Z.to_N len) byte).

  (*** Handling memory events *)
  Section Handlers.
    Definition handle_memory_prop : MemoryE ~> MemPropT MemState
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush_spec_MemPropT
           | MemPop =>
               mempop_spec_MemPropT
           | Alloca t n align =>
               addr <- allocate_dtyp_spec t n;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue_spec t a
               | _ => raise_ub "Loading from something that isn't an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue_spec t a v
               | _ => raise_ub "Writing something to somewhere that isn't an address."
               end
           end.

    Definition handle_memcpy_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (IP.to_Z len) (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_memset_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I32 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset_spec dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I64 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset_spec dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memset."
      end.

    Definition handle_malloc_prop (args : list dvalue) : MemPropT MemState addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I16 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free_spec_MemPropT ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic_prop : IntrinsicE ~> MemPropT MemState
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy_prop args;;
                 ret DVALUE_None
               else
                 if orb (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
                 then
                   handle_memset_prop args;;
                   ret DVALUE_None
                 else
                   if (Coqlib.proj_sumbool (string_dec name "malloc"))
                   then
                     addr <- handle_malloc_prop args;;
                     ret (DVALUE_Addr addr)
                   else
                     if (Coqlib.proj_sumbool (string_dec name "free"))
                     then
                       handle_free_prop args;;
                       ret DVALUE_None
                     else
                       raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.

  (* TODO: Should these be here, or in another module? *)
  (* Useful helper lemmas and relations... *)
  #[global] Instance preserve_allocation_ids_Reflexive :
    Reflexive preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Reflexive :
    Reflexive read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Reflexive :
    Reflexive read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_preserved_Reflexive :
    Reflexive read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    split; reflexivity.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Reflexive :
    Reflexive write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Reflexive :
    Reflexive free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance allocations_preserved_Reflexive :
    Reflexive allocations_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance frame_stack_preserved_memory_Reflexive :
    Reflexive frame_stack_preserved_memory.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance frame_stack_preserved_Reflexive :
    Reflexive frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance heap_preserved_memory_Reflexive :
    Reflexive heap_preserved_memory.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance heap_preserved_Reflexive :
    Reflexive heap_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance addr_allocated_preserved_Reflexive : Reflexive addr_allocated_prop_memory_preserved.
  Proof.
    repeat red.
    intros x addr0 aid.
    split; intros ALLOC; auto.
  Qed.

  #[global] Instance read_byte_prop_memory_preserved_Reflexive : Reflexive read_byte_prop_memory_preserved.
  Proof.
    repeat red.
    intros x addr0 aid.
    split; intros ALLOC; auto.
  Qed.

  #[global] Instance memory_stack_Reflexive : Reflexive memory_stack_eqv.
  Proof.
    red.
    intros x.
    split; try reflexivity.
  Qed.

  #[global] Instance MemState_eqv'_Reflexive : Reflexive MemState_eqv'.
  Proof.
    red.
    intros ms.
    red.
    split; [|reflexivity].

    repeat (split; [reflexivity|]); reflexivity.
  Qed.

  #[global] Instance MemState_eqv_Reflexive : Reflexive MemState_eqv.
  Proof.
    red.
    intros ms.
    repeat (split; [reflexivity|]); reflexivity.
  Qed.

  Lemma fresh_sid_MemState_eqv :
    forall ms ms' sid,
      fresh_sid ms (ret (ms', sid)) ->
      MemState_eqv ms ms'.
  Proof.
    intros ms ms' sid H.
    destruct H.
    split; [|split; [|split; [|split; [|split; [|split]]]]];
      tauto.
  Qed.

  #[global] Instance preserve_allocation_ids_Transitive :
    Transitive preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 p.
    split; intros USED.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Transitive :
    Transitive read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros READ.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Transitive :
    Transitive read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr byte.
    split; intros READ.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_preserved_Transitive :
    Transitive read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0.
    destruct H, H0.
    split.
    - eapply read_byte_allowed_all_preserved_Transitive; eauto.
    - eapply read_byte_prop_all_preserved_Transitive; eauto.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Transitive :
    Transitive write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros WRITE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Transitive :
    Transitive free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros FREE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance allocations_preserved_Transitive :
    Transitive allocations_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr aid.
    split; intros BYTE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance frame_stack_preserved_Transitive :
    Transitive frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 fs.
    split; intros FSP.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance heap_preserved_Transitive :
    Transitive heap_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 h.
    split; intros HEAP.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance MemState_eqv_Transitive : Transitive MemState_eqv.
  Proof.
    red.
    intros x y z H H0.
    destruct H as (?&?&?&?&?&?&?).
    destruct H0 as (?&?&?&?&?&?&?).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply preserve_allocation_ids_Transitive; eauto.
    - eapply read_byte_preserved_Transitive; eauto.
    - eapply write_byte_allowed_all_preserved_Transitive; eauto.
    - eapply free_byte_allowed_all_preserved_Transitive; eauto.
    - eapply allocations_preserved_Transitive; eauto.
    - eapply frame_stack_preserved_Transitive; eauto.
    - eapply heap_preserved_Transitive; eauto.
  Qed.

  #[global] Instance preserve_allocation_ids_Symmetric :
    Symmetric preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    intros y H p.
    split; intros USED.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Symmetric :
    Symmetric read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros READ.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Symmetric :
    Symmetric read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr byte.
    split; intros READ.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_preserved_Symmetric :
    Symmetric read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H.
    destruct H.
    split.
    - eapply read_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply read_byte_prop_all_preserved_Symmetric; eauto.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Symmetric :
    Symmetric write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros WRITE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Symmetric :
    Symmetric free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros FREE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance allocations_preserved_Symmetric :
    Symmetric allocations_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr aid.
    split; intros BYTE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance frame_stack_preserved_Symmetric :
    Symmetric frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H fs.
    split; intros FSP.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance heap_preserved_Symmetric :
    Symmetric heap_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H h.
    split; intros HEAP.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance MemState_eqv_Symmetric : Symmetric MemState_eqv.
  Proof.
    red.
    intros x y H.
    destruct H as (?&?&?&?&?&?&?).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply preserve_allocation_ids_Symmetric; eauto.
    - eapply read_byte_preserved_Symmetric; eauto.
    - eapply write_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply free_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply allocations_preserved_Symmetric; eauto.
    - eapply frame_stack_preserved_Symmetric; eauto.
    - eapply heap_preserved_Symmetric; eauto.
  Qed.

End MemoryModelSpec.

Module MakeMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) <: MemoryModelSpec LP MP MMSP.
  Include MemoryModelSpec LP MP MMSP.
End MakeMemoryModelSpec.

Module Type MemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  Import LP.
  Import MMS.
  Import PROV.
  Import MMSP.
  Import MemHelpers.

  Definition MemMonad_valid_state (ms : MemState) (st : store_id) : Prop
    := let sid := st in
       (forall sid', used_store_id_prop ms sid' -> (sid' < sid)%N).

  Class MemMonad (M : Type -> Type) (RunM : Type -> Type)
        `{MM : Monad M} `{MRun: Monad RunM}
        `{MPROV : MonadProvenance Provenance M} `{MSID : MonadStoreId M} `{MMS: MonadMemState MemState M}
        `{MERR : RAISE_ERROR M} `{MUB : RAISE_UB M} `{MOOM :RAISE_OOM M}
        `{RunERR : RAISE_ERROR RunM} `{RunUB : RAISE_UB RunM} `{RunOOM :RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
    : Type
    :=
    { #[global] MemMonad_eq1_runm :: Eq1 RunM;
      #[global] MemMonad_runm_monadlaws :: MonadLawsE RunM;
      #[global] MemMonad_eq1_runm_equiv :: Eq1Equivalence RunM;
      #[global] MemMonad_eq1_runm_eq1laws :: Eq1_ret_inv RunM;
      #[global] MemMonad_raisebindm_ub :: RaiseBindM RunM string (@raise_ub RunM RunUB);
      #[global] MemMonad_raisebindm_oom :: RaiseBindM RunM string (@raise_oom RunM RunOOM);
      #[global] MemMonad_raisebindm_err :: RaiseBindM RunM string (@raise_error RunM RunERR);
      #[global] MemMonad_within :: @Within M EQM RunM (store_id * MemState)%type (store_id * MemState)%type;

      #[global] MemMonad_eq1_runm_proper ::
                               (forall A, Proper ((@eq1 _ MemMonad_eq1_runm) A ==> (@eq1 _ MemMonad_eq1_runm) A ==> iff) ((@eq1 _ MemMonad_eq1_runm) A));

      MemMonad_run {A} (ma : M A) (ms : MemState) (st : store_id)
      : RunM (store_id * (MemState * A))%type;

      #[global] MemMonad_run_proper ::
        (forall A, Proper (@eq1 _ EQM A ==> eq ==> eq ==> @eq1 _ MemMonad_eq1_runm (store_id * (MemState * A))) MemMonad_run);

      (** Some lemmas about valid states *)
      (* This may not be true for infinite memory. Valid state is
         mostly used to ensure that we can find a store id that hasn't
         been used in memory yet...

         Unfortunately, if memory is infinite it's possible to
         construct a MemState that has a byte allocated for every
         store id... Even though store ids are unbounded integers,
         they have the same cardinality as the memory :|.
       *)
      (*
      MemMonad_has_valid_state :
      forall (ms : MemState), exists (st : store_id),
        MemMonad_valid_state ms st;
       *)
    (** Run bind / ret laws *)
    MemMonad_run_bind
      {A B} (ma : M A) (k : A -> M B) (ms : MemState) (st : store_id):
    eq1 (MemMonad_run (x <- ma;; k x) ms st)
        ('(st', (ms', x)) <- MemMonad_run ma ms st;; MemMonad_run (k x) ms' st');

    MemMonad_run_ret
      {A} (x : A) (ms : MemState) st:
    eq1 (MemMonad_run (ret x) ms st) (ret (st, (ms, x)));

    (** MonadMemState properties *)
    MemMonad_get_mem_state
      (ms : MemState) st :
    eq1 (MemMonad_run (get_mem_state) ms st) (ret (st, (ms, ms)));

    MemMonad_put_mem_state
      (ms ms' : MemState) st :
    eq1 (MemMonad_run (put_mem_state ms') ms st) (ret (st, (ms', tt)));

    (** Fresh store id property *)
    MemMonad_run_fresh_sid
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists st' sid',
      eq1 (MemMonad_run (fresh_sid) ms st) (ret (st', (ms, sid'))) /\
        MemMonad_valid_state ms st' /\
        sid' <= st /\ st < st' /\
        ~ used_store_id_prop ms sid';

    (** Fresh provenance property *)
    (* TODO: unclear if this should exist, must change ms. *)
    MemMonad_run_fresh_provenance
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists ms' pr',
      eq1 (MemMonad_run (fresh_provenance) ms st) (ret (st, (ms', pr'))) /\
        MemMonad_valid_state ms' st /\
        ms_get_memory ms = ms_get_memory ms' /\
        (* Analogous to extend_provenance *)
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
        ~ used_provenance_prop ms pr' /\
        used_provenance_prop ms' pr';

    (** Exceptions *)
    MemMonad_run_raise_oom :
    forall {A} ms oom_msg st,
      eq1 (MemMonad_run (@raise_oom _ _ A oom_msg) ms st) (raise_oom oom_msg);

    MemMonad_eq1_raise_oom_inv :
    forall {A} x oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_oom oom_msg));

    MemMonad_run_raise_ub :
    forall {A} ms ub_msg st,
      eq1 (MemMonad_run (@raise_ub _ _ A ub_msg) ms st) (raise_ub ub_msg);

    MemMonad_eq1_raise_ub_inv :
    forall {A} x ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_ub ub_msg));

    MemMonad_run_raise_error :
    forall {A} ms error_msg st,
      eq1 (MemMonad_run (@raise_error _ _ A error_msg) ms st) (raise_error error_msg);

    MemMonad_eq1_raise_error_inv :
    forall {A} x error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_error error_msg));

    MemMonad_eq1_raise_oom_raise_error_inv :
    forall {A} oom_msg error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_oom oom_msg) (raise_error error_msg));

    MemMonad_eq1_raise_error_raise_oom_inv :
    forall {A} error_msg oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_error error_msg) (raise_oom oom_msg));

    MemMonad_eq1_raise_ub_raise_error_inv :
    forall {A} ub_msg error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_ub ub_msg) (raise_error error_msg));

    MemMonad_eq1_raise_error_raise_ub_inv :
    forall {A} error_msg ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_error error_msg) (raise_ub ub_msg));

    MemMonad_eq1_raise_oom_raise_ub_inv :
    forall {A} oom_msg ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_oom oom_msg) (raise_ub ub_msg));

    MemMonad_eq1_raise_ub_raise_oom_inv :
    forall {A} ub_msg oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_ub ub_msg) (raise_oom oom_msg));
  }.

  Definition within_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} {A} (memm : MemM A) (pre : (store_id * MemState)%type) (runm : RunM A) (post : (store_id * MemState)%type) : Prop :=
    let '(st1, ms1) := pre in
    let '(st2, ms2) := post in
    let t := MemMonad_run memm ms1 st1 in
    let run := a <- runm;; ret (st2, (ms2, a)) : RunM (store_id * (MemState * A))%type in
    let eqi := (@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) in
    eqi _ t run.

  Lemma within_eq1_Proper_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_RunM_MemMonad (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_RunM_MemMonad in *.
    destruct y0, y2.
    split; intros WITHIN.
    - rewrite H in WITHIN.
      auto.
    - rewrite H.
      auto.
  Qed.

  #[global] Instance Within_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} : @Within MemM _ RunM (store_id * MemState)%type (store_id * MemState)%type.
  Proof.
    esplit.
    Unshelve.
    2: {
      intros A m pre b post.
      eapply @within_RunM_MemMonad.
      3: apply pre.
      4: apply post.
      all: eauto.
    }

    intros A.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    eapply within_eq1_Proper_RunM_MemMonad; eauto.
  Defined.

  Definition within_err_ub_oom_itree
    {Pre Post : Type}
    {Eff}
    `{FAIL : FailureE -< Eff} `{UB : UBE -< Eff} `{OOM : OOME -< Eff}
    {A} (t : itree Eff A) (pre : Pre) (e : err_ub_oom A) (post : Post) : Prop :=
    t ≈ lift_err_ub_oom ret e.

  (* Version that uses RAISE_OOM etc explicitly *)
  Import IdentityMonad.
  Definition within_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    {A} (t : itree Eff A) (pre : Pre) (e : err_ub_oom A) (post : Post) : Prop :=
    match e with
    | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
        match m with
        | inl (OOM_message x) =>
            exists oom_msg, t ≈ raise_oom oom_msg
        | inr (inl (UB_message x)) =>
            (* Should this be more permissive? *)
            exists ub_msg, t ≈ raise_ub ub_msg
        | inr (inr (inl (ERR_message x))) =>
            exists err_msg, t ≈ raise_error err_msg
        | inr (inr (inr x)) =>
            (t ≈ ret x)%monad
        end
    end.

  Lemma within_Proper_err_ub_oom_itree
    {Pre Post : Type}
    {Eff}
    `{FAIL : FailureE -< Eff} `{UB : UBE -< Eff} `{OOM : OOME -< Eff}
    {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_err_ub_oom_itree (Eff:=Eff) (Pre:=Pre) (Post:=Post) (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_err_ub_oom_itree in *.
    split; intros WITHIN.
    - rewrite H in WITHIN.
      auto.
    - rewrite H.
      auto.
  Qed.

  Lemma within_Proper_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_err_ub_oom_itree' (EQI:=EQI) (Pre:=Pre) (Post:=Post) (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_err_ub_oom_itree' in *.
    split; intros WITHIN.
    - destruct y1 as [[[[[[[oom_y1] | [[ub_y1] | [[err_y1] | y1']]]]]]]] eqn:Hy1;
        setoid_rewrite H in WITHIN;
        auto.
    - destruct y1 as [[[[[[[oom_y1] | [[ub_y1] | [[err_y1] | y1']]]]]]]] eqn:Hy1;
        setoid_rewrite H;
        auto.
  Qed.

  #[global] Instance Within_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    : @Within (itree Eff) _ err_ub_oom Pre Post.
  Proof.
    esplit.
    intros A.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    eapply within_Proper_err_ub_oom_itree'; eauto.
  Defined.

  (* Should probably be derivable with typeclasses eauto... *)
  #[global] Instance Within_err_ub_oom_MemM {MemM Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    `{MM: MemMonad MemM (itree Eff)} : @Within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type.
  Proof.
    eapply @Transitive_Within with (M1:=err_ub_oom) (M2:=itree Eff) (M3:=MemM).
    - eapply Within_err_ub_oom_itree'.
    - eapply Within_RunM_MemMonad.
  Defined.

  (*** Correctness *)
  Definition exec_correct_post (X : Type) : Type := MemState -> store_id -> X -> MemState -> store_id -> Prop.
  Definition exec_correct_id_post {X} : exec_correct_post X :=
    fun _ _ _ _ _ => True.
  #[global] Hint Unfold exec_correct_id_post : core.
  Definition exec_correct_pre := MemState -> store_id -> Prop.

  Definition exec_correct_post_ret {X} (x : X) : exec_correct_post X
    := fun ms st x' ms' st' =>
         x = x' /\ ms = ms' /\ st = st'.

  Definition exec_correct_post_bind
    {A B}
    (ma : exec_correct_post A)
    (k : A -> exec_correct_post B)
    : exec_correct_post B
    := fun ms st b ms'' st'' =>
         exists a ms' st',
           ma ms st a ms' st' /\
             (k a) ms' st' b ms'' st''.

  Definition exec_correct_post_eqv {A} (a b : exec_correct_post A) :=
    forall ms st x ms' st',
      a ms st x ms' st' <-> b ms st x ms' st'.

  Lemma exec_correct_post_eqv_refl :
    forall {A} (a : exec_correct_post A),
      exec_correct_post_eqv a a.
  Proof.
    intros A a.
    red.
    reflexivity.
  Qed.

  #[global] Instance MonadStoreId_exec_correct_post : MonadStoreId exec_correct_post.
  split.
  refine (fun ms st sid ms' st' =>
            sid <= st /\ st < st' /\ ms = ms').
  Defined.

  #[global] Instance MonadProvenance_exec_correct_post : MonadProvenance Provenance exec_correct_post.
  split.
  refine (fun ms st pr ms' st' =>
            (forall pr0 : Provenance, used_provenance_prop ms pr0 -> used_provenance_prop ms' pr0) /\
              ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr /\
              st = st').
  Defined.

  #[global] Instance Proper_exec_correct_post_eqv {X} :
    Proper (@exec_correct_post_eqv X ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) (fun post ms st x ms' st' => post ms st x ms' st').
  Proof.
    unfold Proper, respectful.
    intros; subst.
    apply H.
  Qed.

  Lemma exec_correct_post_left_identity :
    forall {A B} (a : A) (k : A -> exec_correct_post B),
      exec_correct_post_eqv (exec_correct_post_bind (exec_correct_post_ret a) k) (k a).
  Proof.
    intros A B a k ms st x ms' st'.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H as (?&?&?); subst.
      auto.
    - exists a, ms, st.
      auto.
  Qed.

  Lemma exec_correct_post_right_identity :
    forall {A} (ma : exec_correct_post A),
      exec_correct_post_eqv (exec_correct_post_bind ma exec_correct_post_ret) ma.
  Proof.
    intros A ma ms st x ms' st'.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H0 as (?&?&?); subst.
      auto.
    - exists x, ms', st'.
      auto.
  Qed.

  Lemma exec_correct_post_associativity :
    forall {A B C}
      (ma : exec_correct_post A)
      (mab : A -> exec_correct_post B)
      (mbc : B -> exec_correct_post C),
      exec_correct_post_eqv
        (exec_correct_post_bind (exec_correct_post_bind ma mab) mbc)
        (exec_correct_post_bind ma (fun a => exec_correct_post_bind (mab a) mbc)).
  Proof.
    intros A B C ma mab mbc.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H as (?&?&?&?&?); subst.
      exists x3, x4, x5.
      split; eauto.
    - destruct H as (?&?&?&?&?); subst.
      destruct H0 as (?&?&?&?&?); subst.
      exists x3, x4, x5.
      split; eauto.
  Qed.

  #[global] Instance Monad_exec_correct_post : Monad exec_correct_post.
  split.
  - intros; apply exec_correct_post_ret; auto.
  - intros; eapply exec_correct_post_bind; eauto.
  Defined.

  #[global] Instance Eq1_exec_correct_post : Eq1 exec_correct_post.
  red. intros. eapply exec_correct_post_eqv.
  apply X.
  apply X0.
  Defined.

  #[global] Instance MonadLawsE_exec_correct_post : MonadLawsE exec_correct_post.
  split.
  - intros. apply exec_correct_post_left_identity.
  - intros. apply exec_correct_post_right_identity.
  - intros. apply exec_correct_post_associativity.
  - intros A B.
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    repeat red in H.
    repeat red.
    intros ms st x1 ms' st'.
    split.
    + intros H1.
      red in H0.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      specialize (H ms st x2 x3 x4).
      destruct H.
      eapply H in H1.
      repeat red.
      exists x2, x3, x4.
      split; eauto.
      apply H0; auto.
    + intros H1.
      red in H0.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      specialize (H ms st x2 x3 x4).
      destruct H.
      eapply H3 in H1.
      repeat red.
      exists x2, x3, x4.
      split; eauto.
      apply H0; auto.
  Defined.

  Lemma exec_correct_post_bind_unfold :
    forall {A B}
      (ma : exec_correct_post A)
      (mab : A -> exec_correct_post B)
      ms st b ms'' st'',
      (exists a ms' st',
          ma ms st a ms' st' /\
            (mab a) ms' st' b ms'' st'') ->
      (a <- ma;;
       mab a) ms st b ms'' st''.
  Proof.
    intros A B ma mab ms st b ms'' st'' H.
    cbn.
    unfold exec_correct_post_bind.
    auto.
  Qed.

  Definition exec_correct {MemM Eff} `{MM: MemMonad MemM (itree Eff)} {X} (pre : exec_correct_pre) (exec : MemM X) (spec : MemPropT MemState X) (post : exec_correct_post X) : Prop :=
    forall ms st,
      (MemMonad_valid_state ms st) ->
      pre ms st ->
      (* UB catchall *)
      (exists ms' msg_spec,
          @raise_ub err_ub_oom _ X msg_spec {{ ms }} ∈ {{ ms' }} spec) \/
        ( (* exists a behaviour in exec that lines up with spec.

               Technically this should be something along the lines of...

               "There is at least one behaviour in exec, and for every
               behaviour in exec it is within the spec"

               For our purposes exec is deterministic, so "exists"
               should be fine here for simplicity.
             *)
           exists (e : err_ub_oom X) (st' : store_id) (ms' : MemState),
             (* Had to manually supply typeclasses, but this within expression is: (e {{(st, ms)}} ∈ {{(st', ms')}} exec))

                 I.e., The executable is correct if forall behaviours
                 in the executable those behaviours are in the spec as
                 well, and if the executable returns successfully it
                 gives a valid store_id / MemState pair.
              *)
             let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM))) in
             (@within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type WEM X exec (st, ms) e (st', ms')) /\
               (e {{ms}} ∈ {{ms'}} spec) /\ ((exists x, e = ret x) -> (MemMonad_valid_state ms' st' /\ (exists x, e = ret x /\ post ms st x ms' st')))).

  (* TODO: Move this *)
  Lemma exec_correct_weaken_pre :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A}
      (pre : exec_correct_pre)
      (post : exec_correct_post A)
      (weak_pre : exec_correct_pre)
      (exec : MemM A)
      (spec : MemPropT MemState A),
      (forall ms st, pre ms st -> weak_pre ms st) ->
      exec_correct weak_pre exec spec post ->
      exec_correct pre exec spec post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A pre post weak_pre exec spec WEAK EXEC.
    unfold exec_correct in *.
    intros ms st VALID PRE.
    apply WEAK in PRE.
    eauto.
  Qed.

  (* TODO: Move this *)
  Lemma exec_correct_strengthen_post :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A}
      (pre : exec_correct_pre)
      (post : exec_correct_post A)
      (strong_post : exec_correct_post A)
      (exec : MemM A)
      (spec : MemPropT MemState A),
      (forall ms st a ms' st', pre ms st -> strong_post ms st a ms' st' -> post ms st a ms' st') ->
      exec_correct pre exec spec strong_post ->
      exec_correct pre exec spec post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A pre post strong_post exec spec STRONG EXEC.
    unfold exec_correct in *.
    intros ms st VALID PRE.
    specialize (EXEC _ _ VALID PRE).
    destruct EXEC as [UB | EXEC]; auto.
    right.
    destruct EXEC as (?&?&?&?&?&?).
    exists x, x0, x1.
    split; auto.
    split; auto.
    intros H2.
    forward H1; auto.
    destruct H1 as (?&(?&?&?)).
    subst.
    split; auto.
    exists x2.
    split; auto.
  Qed.

  (* TODO: move this *)
  Lemma exec_correct_bind :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A B}
      (pre : exec_correct_pre)
      (post_a : exec_correct_post A)
      (post_b : A -> exec_correct_post B)
      (m_exec : MemM A) (k_exec : A -> MemM B)
      (m_spec : MemPropT MemState A) (k_spec : A -> MemPropT MemState B),
      exec_correct pre m_exec m_spec post_a ->
      (* This isn't true:

           (forall a ms ms', m_spec ms (ret (ms', a)) -> exec_correct (k_exec a) (k_spec a)) -> ...

           E.g., if 1 is a valid return value in m_spec, but m_exec can only return 0, then

           k_spec may ≈ ret 2

           But k_exec may ≈ \a => if a == 0 then ret 2 else raise_ub "blah"

           I.e., k_exec may be set up to only be valid when results are returned by m_exec.
       *)
      (* The exec continuation `k_exec a` agrees with `k_spec a`
           whenever `a` is a valid return value from the spec and the
           executable prefix

           Questions:

           - What if m_exec returns an `a` that isn't in the spec...
             + Should be covered by `exec_correct m_exec m_spec` assumption.
       *)
      (forall a ms_init ms_after_m st_init st_after_m,
          MemMonad_valid_state ms_after_m st_after_m ->
          post_a ms_init st_init a ms_after_m st_after_m ->
          ((@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM)) _
                                                                                (MemMonad_run m_exec ms_init st_init)
                                                                                (ret (st_after_m, (ms_after_m, a))))%monad ->
          (* ms_k is a MemState after evaluating m *)
          let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM))) in
          exec_correct (fun ms_k st_k =>
                          pre ms_init st_init /\
                            (@within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type WEM _ m_exec (st_init, ms_init) (ret a) (st_k, ms_k))
                          /\ m_spec ms_init (ret (ms_k, a))) (k_exec a) (k_spec a) (post_b a)) ->
      exec_correct pre (a <- m_exec;; k_exec a) (a <- m_spec;; k_spec a) (a <- post_a;; post_b a).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS MEMM A B pre post_a post_b m_exec k_exec m_spec
      k_spec M_CORRECT K_CORRECT.

    unfold exec_correct in *.
    intros ms st VALID PRE.
    specialize (M_CORRECT ms st VALID PRE).
    destruct M_CORRECT as [[ub_ms' [msg M_UB]] | M_CORRECT].
    { (* UB *)
      left.
      exists ub_ms'. exists msg.
      left; auto.
    }

    destruct M_CORRECT as [e [st' [ms' [M_EXEC_CORRECT [M_SPEC_CORRECT M_POST]]]]].
    destruct e as [[[[[[[oom_e] | [[ub_e] | [[err_e] | e']]]]]]]] eqn:He.

    - (* OOM *)
      right.
      exists (raise_oom oom_e).
      exists st'.
      exists ms'.

      split.
      { (* Exec *)
        cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        cbn. red.
        destruct M_EXEC_CORRECT as [m2 [[oom_msg OOM] EXEC]].
        exists (raise_oom oom_msg).
        split.
        cbn.
        eexists; reflexivity.
        cbn.
        cbn in EXEC.
        rewrite MemMonad_run_bind.
        rewrite EXEC.
        rewrite OOM.
        repeat (rewrite rbm_raise_bind; [| typeclasses eauto]).
        reflexivity.
      }

      split.
      { (* In spec *)
        cbn.
        left.
        apply M_SPEC_CORRECT.
      }

      intros [x CONTRA].
      inv CONTRA.
    - (* UB *)
      left.
      exists ms'. exists ub_e.
      cbn.
      left.
      apply M_SPEC_CORRECT.
    - (* Err *)
      right.
      exists (raise_error err_e).
      exists st'.
      exists ms'.

      split.
      { (* Exec *)
        cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        cbn. red.
        destruct M_EXEC_CORRECT as [m2 [[err_msg ERR] EXEC]].
        exists (raise_error err_msg).
        split.
        cbn.
        eexists; reflexivity.
        cbn.
        cbn in EXEC.
        rewrite MemMonad_run_bind.
        rewrite EXEC.
        rewrite ERR.
        repeat (rewrite rbm_raise_bind; [| typeclasses eauto]).
        reflexivity.
      }

      split.
      { (* In spec *)
        cbn.
        left.
        apply M_SPEC_CORRECT.
      }

      intros [x CONTRA].
      cbn in CONTRA.
      inv CONTRA.
    - (* Success *)
      (* Need to know if there's UB in K... *)
      rename e' into a.
      forward M_POST.
      { eexists; reflexivity. }
      destruct M_POST as (VALID' & POST').
      destruct POST' as (?&?&POST').
      inv H.
      rename x into a.

      specialize (K_CORRECT a ms ms' st st').
      forward K_CORRECT; eauto.
      forward K_CORRECT; eauto.

      forward K_CORRECT.
      { cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        destruct M_EXEC_CORRECT as [m2 [SUCC EXEC]].
        cbn in *.
        rewrite EXEC, SUCC.
        rewrite bind_ret_l.
        reflexivity.
      }

      specialize (K_CORRECT _ _ VALID').
      forward K_CORRECT.
      { split; auto. }

      destruct K_CORRECT as [[ub_ms [ub_msg K_UB]] | K_CORRECT].
      { (* UB in K *)
        left.
        exists ub_ms. exists ub_msg.
        right.
        exists ms'. exists a.
        split; auto.
      }

      (* UB not necessarily in K *)
      right.
      destruct K_CORRECT as [eb [st'' [ms'' [K_EXEC [K_SPEC K_POST]]]]].

      cbn in M_EXEC_CORRECT.
      red in M_EXEC_CORRECT.

      cbn in K_EXEC.
      red in K_EXEC.

      destruct M_EXEC_CORRECT as [tm [M_SUCC M_EXEC]].
      destruct K_EXEC as [tk [K_SUCC K_EXEC]].

      cbn in M_SUCC, M_EXEC.
      rewrite M_SUCC in M_EXEC.
      rewrite bind_ret_l in M_EXEC.

      exists eb. exists st''. exists ms''.
      split; [| split].

      { (* Exec *)
        exists tk.
        split; auto.

        cbn.
        rewrite MemMonad_run_bind.

        rewrite M_EXEC.
        rewrite bind_ret_l.
        rewrite K_EXEC.
        reflexivity.
      }

      { (* Spec *)
        (* TODO: Probably a good bind lemma for this *)
        destruct eb as [[[[[[[oom_eb] | [[ub_eb] | [[err_eb] | eb']]]]]]]] eqn:Heb;
          try right; cbn; exists ms'; exists a; split; auto.
      }

      { (* Post *)
        intros [x RET].
        subst.
        forward K_POST; eauto.
        destruct K_POST.
        split; eauto.
        exists x.
        split; auto.
        destruct H0 as (?&?&?).
        inv H0.

        repeat red.
        exists a, ms', st'.
        split; eauto.
      }
  Qed.

  Lemma exec_correct_ret :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {X}
      (pre : exec_correct_pre)
      (x : X),
      exec_correct pre (ret x) (ret x) (exec_correct_post_ret x).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H X pre x.
    intros ms st VALID PRE.
    right.
    exists (ret x), st, ms.
    split.
    { (* TODO: cleaner lemma *)
      cbn.
      red.
      exists (ret x).
      split.
      - cbn. reflexivity.
      - cbn.
        rewrite MemMonad_run_ret.
        rewrite bind_ret_l.
        reflexivity.
    }

    split; cbn; auto.
    intros H0.
    split; eauto.
    exists x.
    split; eauto.
    red.
    auto.
  Qed.

  Lemma exec_correct_map_monad :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      xs
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
      (post : A -> exec_correct_post B),
      (forall a (pre : _ -> _ -> Prop),
          exec_correct pre (m_exec a) (m_spec a) (post a)) ->
      forall pre, exec_correct pre (map_monad m_exec xs) (map_monad m_spec xs) (map_monad post xs).
  Proof.
    induction xs;
      intros m_exec m_spec HM pre post.

    - unfold map_monad.
      apply exec_correct_ret; auto.
    - rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      eapply exec_correct_bind; eauto.
      intros * VALID POST RUN.

      eapply exec_correct_bind; eauto.
      intros * VALID2 POST2 RUN2.

      apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_map_monad_ :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
      (post : A -> exec_correct_post B),
      (forall a pre, exec_correct pre (m_exec a) (m_spec a) (post a)) ->
      forall pre, exec_correct pre (map_monad_ m_exec xs) (map_monad_ m_spec xs) (map_monad_ post xs).
  Proof.
    intros MemM Eff MM MRun SID_FRESH MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS A B xs m_exec m_spec H0 pre post.
    eapply exec_correct_bind; auto.
    eapply exec_correct_map_monad; auto.
    intros * VALID POST RUN.
    apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_map_monad_In :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B)
      post,
      (forall a pre (IN : In a xs), exec_correct pre (m_exec a IN) (m_spec a IN) (post a IN)) ->
      forall pre, exec_correct pre (map_monad_In xs m_exec) (map_monad_In xs m_spec) (map_monad_In xs post).
  Proof.
    induction xs; intros m_exec m_spec HM pre post.
    - unfold map_monad_In.
      apply exec_correct_ret; auto.
    - rewrite map_monad_In_unfold.
      rewrite map_monad_In_unfold.

      eapply exec_correct_bind; eauto.
      intros * VALID1 POST1 RUN1.

      eapply exec_correct_bind; eauto.
      intros * VALID2 POST2 RUN2.

      apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_raise_oom :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg : string),
    forall pre post, exec_correct pre (raise_oom msg) (raise_oom msg : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg pre post.
    red.
    intros ms st VALID PRE.
    right.
    exists (raise_oom msg).
    exists st. exists ms.
    split.
    { (* TODO: cleaner lemma? *)
      cbn.
      red.
      exists (raise_oom msg).
      split; cbn.
      - eexists; reflexivity.
      - rewrite MemMonad_run_raise_oom.
        rewrite rbm_raise_bind; [| typeclasses eauto].
        reflexivity.
    }

    split; cbn; auto.
    intros [x CONTRA].
    inv CONTRA.
  Qed.

  Lemma exec_correct_raise_error :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre post, exec_correct pre (raise_error msg1) (raise_error msg2 : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg1 msg2 pre post.
    red.
    intros ms st VALID PRE.
    right.
    exists (raise_error msg2).
    exists st. exists ms.
    split.
    { (* TODO: cleaner lemma? *)
      cbn.
      red.
      exists (raise_error msg1).
      split; cbn.
      - eexists; reflexivity.
      - rewrite MemMonad_run_raise_error.
        rewrite rbm_raise_bind; [| typeclasses eauto].
        reflexivity.
    }

    split; cbn; auto.
    intros [x CONTRA].
    inv CONTRA.
  Qed.

  Lemma exec_correct_raise_ub :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre post, exec_correct pre (raise_ub msg1) (raise_ub msg2 : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg1 msg2 pre post.

    red.
    intros ms st VALID PRE.

    left.
    exists ms. exists msg2.
    cbn; auto.
  Qed.

  (* TODO: Move this *)
  #[global] Instance RAISE_OOM_exec_correct_post : RAISE_OOM exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => False).
  Defined.

  (* TODO: Move this *)
  #[global] Instance RAISE_UB_exec_correct_post : RAISE_UB exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => False).
  Defined.

  (* TODO: Move this *)
  #[global] Instance RAISE_ERROR_exec_correct_post : RAISE_ERROR exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => True).
  Defined.

  Lemma exec_correct_lift_OOM :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : OOM A)
      (pre : exec_correct_pre),
      exec_correct pre (lift_OOM m) (lift_OOM m) (lift_OOM m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [NOOM | OOM] pre post.
    - apply exec_correct_ret; auto.
    - apply exec_correct_raise_oom.
  Qed.

  Lemma exec_correct_lift_ERR_RAISE_ERROR :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : ERR A)
      (pre : _ -> _ -> Prop),
      exec_correct pre (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [[ERR] | NOERR] pre.
    - apply exec_correct_raise_error; auto.
    - cbn.
      repeat red.
      intros ms st H0 H1.
      right.
      exists (ret NOERR), st, ms.
      cbn; split; eauto.
      repeat red.
      cbn.
      exists (ret NOERR).
      split.
      reflexivity.
      rewrite MemMonad_run_ret.
      rewrite bind_ret_l.
      reflexivity.
      split; eauto.
      intros (?&?).
      inv H2.
      split; eauto.
      exists x.
      split; eauto.
      red; auto.
  Qed.

  Lemma exec_correct_lift_err_RAISE_ERROR :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : err A)
      (pre : _ -> _ -> Prop),
      exec_correct pre (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [ERR | NOERR] pre.
    - apply exec_correct_raise_error; auto.
    - repeat red.
      intros ms st H0 H1.
      right.
      exists (ret NOERR), st, ms.
      cbn; split; eauto.
      repeat red.
      cbn.
      exists (ret NOERR).
      split.
      reflexivity.
      rewrite MemMonad_run_ret.
      rewrite bind_ret_l.
      reflexivity.
      split; eauto.
      intros (?&?).
      inv H2.
      split; eauto.
      exists x.
      split; eauto.
      red; auto.
  Qed.

  Definition get_consecutive_ptrs_post len : exec_correct_post (list ADDR.addr) :=
    (fun ms st addrs ms' st' =>
           length addrs = len /\ ms = ms' /\ st = st').
  #[global] Hint Unfold get_consecutive_ptrs_post : core.

  Definition intptr_seq_post len : exec_correct_post (list IP.intptr) :=
    (fun ms st ips ms' st' => length ips = len /\ ms = ms' /\ st = st').
  #[global] Hint Unfold intptr_seq_post : core.

  Lemma exec_correct_get_consecutive_pointers :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      len ptr,
    forall pre,
      exec_correct
        pre
        (get_consecutive_ptrs ptr len)
        (get_consecutive_ptrs ptr len)
        (get_consecutive_ptrs ptr len).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H len ptr pre.
    unfold get_consecutive_ptrs.

    eapply exec_correct_bind.
    apply exec_correct_lift_OOM.

    intros a ms_init ms_after_m st_init st_after_m H0 H1 H2 WEM.
    unfold lift_OOM in H1.
    break_match_hyp_inv.
    destruct H4 as (?&?); subst.

    eapply exec_correct_bind.
    apply exec_correct_lift_err_RAISE_ERROR.

    intros * VALID POST RUN.
    apply exec_correct_lift_OOM.
  Qed.

  Lemma exec_correct_fresh_sid :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)} pre,
      exec_correct pre fresh_sid fresh_sid fresh_sid.
  Proof.
    red.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H pre ms st H0 PRE.
    right.
    eapply (@MemMonad_run_fresh_sid MemM) in H0 as [st' [sid [EUTT [VALID [LT [NEW_ST FRESH]]]]]].
    exists (ret sid), st', ms.
    split; [| split]; auto.
    { cbn.
      red.
      exists (ret sid).
      split; cbn.
      - reflexivity.
      - rewrite EUTT, bind_ret_l.
        reflexivity.
    }
    2: {
      intros [x RET].
      inv RET.
      split; eauto.
      exists x.
      split; eauto.
      red; cbn.
      split; eauto.
    }

    cbn.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];
      try solve [red; reflexivity].
    - unfold fresh_store_id. auto.
    - unfold read_byte_preserved.
      split; red; reflexivity.
  Qed.

  Section Correctness.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    Import Monad.

    (* TODO: move this? *)
    Lemma byte_allocated_mem_eq :
      forall ms ms' ptr aid,
        byte_allocated ms ptr aid ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        byte_allocated ms' ptr aid.
    Proof using Type.
      intros ms ms' ptr aid ALLOC EQ.
      unfold byte_allocated.
      cbn in *.
      red in ALLOC.
      rewrite <- EQ.
      auto.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_allowed_mem_eq :
      forall ms ms' ptr,
        read_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr READ EQ.
      unfold read_byte_allowed in *.
      destruct READ as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_mem_eq :
      forall ms ms' ptr,
        write_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr WRITE EQ.
      unfold write_byte_allowed in *.
      destruct WRITE as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma free_byte_allowed_mem_eq :
      forall ms ms' ptr,
        free_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        free_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr FREE EQ.
      unfold free_byte_allowed in *.
      destruct FREE as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_prop_mem_eq :
      forall ms ms' ptr byte,
        read_byte_prop ms ptr byte ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_prop ms' ptr byte.
    Proof using Type.
      intros ms ms' ptr byte READ EQ.
      unfold read_byte_prop.
      rewrite <- EQ.
      auto.
    Qed.

    Lemma read_byte_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_preserved ms ms'.
    Proof using Type.
      unfold read_byte_preserved.
      split; red.
      + intros ptr; split; intros READ_ALLOWED;
          eapply read_byte_allowed_mem_eq; eauto.
      + intros ptr byte; split; intros READ_ALLOWED;
          eapply read_byte_prop_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_all_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed_all_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr.
      split; red;
        intros WRITE_ALLOWED;
        eapply write_byte_allowed_mem_eq; eauto.
    Qed.

    Lemma free_byte_allowed_all_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        free_byte_allowed_all_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold free_byte_allowed_all_preserved.
      intros ptr.
      split; red;
        intros FREE_ALLOWED;
        eapply free_byte_allowed_mem_eq; eauto.
    Qed.

    Lemma allocations_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        allocations_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr aid.
      split; intros ALLOC; eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma frame_stack_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        frame_stack_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold frame_stack_preserved.
      intros fs.
      split; intros FS; [rewrite <- EQ | rewrite EQ]; eauto.
    Qed.

    #[global] Instance Proper_heap_preserved :
      Proper ((fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> (fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> iff) heap_preserved.
    Proof using Type.
      unfold Proper, respectful.
      intros x y H x0 y0 H0.
      unfold heap_preserved.
      rewrite H, H0.
      reflexivity.
    Qed.

    #[global] Instance Reflexive_heap_preserved : Reflexive heap_preserved.
    Proof using Type.
      unfold Reflexive.
      intros x.
      unfold heap_preserved.
      reflexivity.
    Qed.

    Lemma exec_correct_fresh_provenance :
      forall pre, exec_correct pre fresh_provenance fresh_provenance fresh_provenance.
    Proof using Type.
      red.
      intros pre ms st H PRE.
      right.
      eapply (@MemMonad_run_fresh_provenance MemM) in H as [ms' [pr [EUTT [VALID [MEM FRESH]]]]].
      exists (ret pr), st, ms'.
      split; [| split]; auto.
      { cbn.
        red.
        exists (ret pr).
        split; cbn.
        - reflexivity.
        - rewrite EUTT, bind_ret_l.
          reflexivity.
      }
      2: {
        intros [x RET].
        inv RET.
        split; eauto.
        exists x.
        split; eauto.
        cbn.
        split; [|split;[|split]]; eauto; apply FRESH.
      }

      cbn.
      split; [| split; [| split; [| split; [| split; [| split]]]]];
        try solve [red; reflexivity].
      - unfold extend_provenance. tauto.
      - eapply read_byte_preserved_mem_eq; eauto.
      - eapply write_byte_allowed_all_preserved_mem_eq; eauto.
      - eapply free_byte_allowed_all_preserved_mem_eq; eauto.
      - eapply allocations_preserved_mem_eq; eauto.
      - eapply frame_stack_preserved_mem_eq; eauto.
      - unfold ms_get_memory in MEM; cbn in MEM. eapply Proper_heap_preserved; eauto.
        reflexivity.
    Qed.
  End Correctness.

  Hint Resolve exec_correct_ret : EXEC_CORRECT.
  Hint Resolve exec_correct_bind : EXEC_CORRECT.
  Hint Resolve exec_correct_fresh_sid : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_err_RAISE_ERROR : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_ERR_RAISE_ERROR : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_OOM : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_error : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_oom : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_ub : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad_ : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad_In : EXEC_CORRECT.
  Hint Resolve exec_correct_fresh_provenance : EXEC_CORRECT.

End MemoryExecMonad.

Module MakeMemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) <: MemoryExecMonad LP MP MMSP MMS.
  Include MemoryExecMonad LP MP MMSP MMS.
End MakeMemoryExecMonad.

Module Type MemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import MP.

  (** Specification of the memory model *)
  Declare Module MMSP : MemoryModelSpecPrimitives LP MP.
  Import MMSP.
  Import MMSP.MemByte.

  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.
  Import MemSpec.

  Module MemExecM := MakeMemoryExecMonad LP MP MMSP MemSpec.
  Import MemExecM.

  Section MemoryPrimitives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    (*** Data types *)
    Parameter initial_frame : Frame.
    Parameter initial_heap : Heap.

    (*** Primitives on memory *)
    (** Reads *)
    Parameter read_byte :
      forall `{MemMonad MemM (itree Eff)}, addr -> MemM SByte.

    (** Writes *)
    Parameter write_byte :
      forall `{MemMonad MemM (itree Eff)}, addr -> SByte -> MemM unit.

    (** Stack allocations *)
    Parameter allocate_bytes_with_pr :
      forall `{MemMonad MemM (itree Eff)}, list SByte -> Provenance -> MemM addr.

    (** Frame stacks *)
    Parameter mempush : forall `{MemMonad MemM (itree Eff)}, MemM unit.
    Parameter mempop : forall `{MemMonad MemM (itree Eff)}, MemM unit.

    (** Heap operations *)
    Parameter malloc_bytes_with_pr :
      forall `{MemMonad MemM (itree Eff)}, list SByte -> Provenance -> MemM addr.

    Parameter free :
      forall `{MemMonad MemM (itree Eff)}, addr -> MemM unit.

    (*** Correctness *)

    (** Correctness of the main operations on memory *)
    Parameter read_byte_correct :
      forall ptr pre,
        exec_correct pre (read_byte ptr) (read_byte_spec_MemPropT ptr)
          (fun ms st byte ms' st' => (exists s, MemByte.sbyte_sid byte = inr s /\ s < st) /\ ms = ms' /\ st = st').

    Parameter write_byte_correct :
      forall ptr byte,
        exec_correct
          (fun ms st => exists s, sbyte_sid byte = inr s /\ (s < st)%N)
          (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte)
          (fun _ st _ _ st' => st = st').

    Parameter write_byte_preserves_store_id :
      forall st ms a b st' ms' res,
        @within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
          (@Within_err_ub_oom_MemM MemM Eff
             (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                RunOOM EQM EQRI MLAWS MM) MRun
             (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID MMS MERR MUB
             MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) unit
          (write_byte a b) (@pair store_id MemState st ms)
          (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) unit res)
          (@pair store_id MemState st' ms') ->
        st = st'.

    Parameter allocate_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (allocate_bytes_with_pr init_bytes pr)
          (allocate_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.

    (** Correctness of frame stack operations *)
    Parameter mempush_correct :
      forall pre, exec_correct pre mempush mempush_spec_MemPropT exec_correct_id_post.

    Parameter mempop_correct :
      forall pre, exec_correct pre mempop mempop_spec_MemPropT exec_correct_id_post.

    Parameter malloc_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (malloc_bytes_with_pr init_bytes pr) (malloc_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.

    Parameter free_correct :
      forall ptr pre,
        exec_correct pre (free ptr) (free_spec_MemPropT ptr) exec_correct_id_post.

    (*** Initial memory state *)
    Record initial_memory_state_prop : Prop :=
      {
        initial_memory_no_allocations :
        forall ptr aid,
          ~ byte_allocated initial_memory_state ptr aid;

        initial_memory_frame_stack :
        forall fs,
          memory_stack_frame_stack_prop (MemState_get_memory initial_memory_state) fs ->
          empty_frame_stack fs;

        initial_memory_heap :
        forall h,
          memory_stack_heap_prop (MemState_get_memory initial_memory_state) h ->
          empty_heap h;

        initial_memory_read_ub :
        forall ptr byte,
          ~ read_byte_prop initial_memory_state ptr byte
      }.

    Record initial_frame_prop : Prop :=
      {
        initial_frame_is_empty : empty_frame initial_frame;
      }.

    Record initial_heap_prop : Prop :=
      {
        initial_heap_is_empty : empty_heap initial_heap;
      }.

    Parameter initial_memory_state_correct : initial_memory_state_prop.
    Parameter initial_frame_correct : initial_frame_prop.
    Parameter initial_heap_correct : initial_heap_prop.
  End MemoryPrimitives.
End MemoryModelExecPrimitives.

Module Type MemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import LP.Events.
  Import MP.
  Import MMEP.
  Import MemExecM.
  Import MMSP.
  Import MMSP.MemByte.
  Import MMEP.MemSpec.
  Import MemHelpers.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Import OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Import OVER_H.

  (*** Handling memory events *)
  Section Handlers.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    (** Reading uvalues *)
    Definition read_bytes `{MemMonad MemM (itree Eff)} (ptr : addr) (len : nat) : MemM (list SByte) :=
      (* TODO: this should maybe be UB and not OOM??? *)
      ptrs <- get_consecutive_ptrs ptr len;;

      (* Actually perform reads *)
      map_monad (fun ptr => read_byte ptr) ptrs.

    Definition read_uvalue `{MemMonad MemM (itree Eff)} (dt : dtyp) (ptr : addr) : MemM uvalue :=
      bytes <- read_bytes ptr (N.to_nat (sizeof_dtyp dt));;
      lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

    (** Writing uvalues *)
    Definition write_bytes `{MemMonad MemM (itree Eff)} (ptr : addr) (bytes : list SByte) : MemM unit :=
      (* TODO: Should this be UB instead of OOM? *)
      ptrs <- get_consecutive_ptrs ptr (length bytes);;
      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      map_monad_ (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

    Definition write_uvalue `{MemMonad MemM (itree Eff)} (dt : dtyp) (ptr : addr) (uv : uvalue) : MemM unit :=
      bytes <- serialize_sbytes uv dt;;
      write_bytes ptr bytes.

    (** Allocating dtyps *)
    Definition allocate_bytes `{MemMonad MemM (itree Eff)}
      (init_bytes : list SByte)
      : MemM addr
      := pr <- fresh_provenance;;
         allocate_bytes_with_pr init_bytes pr.

    (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
    Definition allocate_dtyp `{MemMonad MemM (itree Eff)}
      (dt : dtyp) (num_elements : N)
      : MemM addr
      :=
      if dtyp_eqb dt DTYPE_Void
      then raise_ub "allocating void type"
      else sid <- fresh_sid;;
           element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
           let bytes := concat element_bytes in
           allocate_bytes bytes.

    (** Malloc *)
    Definition malloc_bytes `{MemMonad MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      malloc_bytes_with_pr init_bytes pr.

    (** Handle memcpy *)
    Definition memcpy `{MemMonad MemM (itree Eff)} (src dst : addr) (len : Z) (volatile : bool) : MemM unit :=
      if Z.ltb len 0
      then
        raise_ub "memcpy given negative length."
      else
        (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
         *)
        if orb (no_overlap dst len src len)
               (Z.eqb (ptr_to_int src) (ptr_to_int dst))
        then
          src_bytes <- read_bytes src (Z.to_nat len);;

          (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
          write_bytes dst src_bytes
        else
          raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

    (** memset spec *)
    Definition memset `{MemMonad MemM (itree Eff)}
      (dst : addr) (val : int8) (len : Z) (sid : store_id) (volatile : bool) : MemM unit :=
      if Z.ltb len 0
      then
        raise_ub "memset given negative length."
      else
        let byte := uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid in
        write_bytes dst (repeatN (Z.to_N len) byte).

    Definition handle_memory `{MemMonad MemM (itree Eff)} : MemoryE ~> MemM
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush
           | MemPop =>
               mempop
           | Alloca t num_elements align =>
               addr <- allocate_dtyp t num_elements;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue t a
               | _ =>
                   raise_ub "Loading from something that is not an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue t a v
               | _ =>
                   raise_ub "Store to somewhere that is not an address."
               end
           end.

    Definition handle_memcpy `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (IP.to_Z len) (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_memset `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I32 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I64 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memset."
      end.

    Definition handle_malloc `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I16 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic `{MemMonad MemM (itree Eff)} : IntrinsicE ~> MemM
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy args;;
                 ret DVALUE_None
               else
                 if orb (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
                 then
                   handle_memset args;;
                   ret DVALUE_None
                 else
                   if (Coqlib.proj_sumbool (string_dec name "malloc"))
                   then
                     addr <- handle_malloc args;;
                     ret (DVALUE_Addr addr)
                   else
                     if (Coqlib.proj_sumbool (string_dec name "free"))
                     then
                       handle_free args;;
                       ret DVALUE_None
                     else
                       raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.
End MemoryModelExec.

Module MakeMemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) <: MemoryModelExec LP MP MMEP.
  Include MemoryModelExec LP MP MMEP.
End MakeMemoryModelExec.

Module MemoryModelTheory (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MME : MemoryModelExec LP MP MMEP).
  Import MMEP.
  Import MME.
  Import MemSpec.
  Import MMSP.
  Import MemExecM.
  Import MemHelpers.
  Import LP.Events.

  (* TODO: move this *)
  Lemma zip_cons :
    forall {A B} (x : A) (y : B) xs ys,
      zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys.
  Proof.
    reflexivity.
  Qed.

  Section Correctness.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    Import Monad.

    Lemma exec_correct_re_sid_ubytes_helper :
      forall bytes pre nm,
        exec_correct pre
                     (re_sid_ubytes_helper bytes nm)
                     (re_sid_ubytes_helper bytes nm)
                     (re_sid_ubytes_helper bytes nm).
    Proof using Type.
      intros bytes.
      induction bytes using length_strong_ind; intros pre nm.
      - apply exec_correct_ret; auto.
      - repeat rewrite re_sid_ubytes_helper_equation.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        eapply exec_correct_bind; auto with EXEC_CORRECT.
        intros a0.
        intros ms_init ms_after_m st_init st_after_m VALID_FRESH POST_FRESH RUN_FRESH_SID.
        apply H.
        subst.

        cbn in H0.
        apply filter_split_out_length in Heqp1.
        lia.
    Qed.

    Hint Resolve exec_correct_re_sid_ubytes_helper : EXEC_CORRECT.

    Lemma exec_correct_trywith_error :
      forall {A} msg1 msg2 (ma : option A) pre,
        exec_correct pre
                     (trywith_error msg1 ma)
                     (trywith_error msg2 ma)
                     (trywith_error msg2 ma).
    Proof using Type.
      intros A msg1 msg2 [a |] pre;
        unfold trywith_error;
        auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_trywith_error : EXEC_CORRECT.

    Lemma exec_correct_re_sid_ubytes :
      forall bytes pre,
        exec_correct pre (re_sid_ubytes bytes) (re_sid_ubytes bytes)
                     (re_sid_ubytes bytes).
    Proof using Type.
      intros bytes pre.
      eapply exec_correct_bind; auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_re_sid_ubytes : EXEC_CORRECT.

    Lemma dtyp_measure_strong_ind:
      forall (P : dtyp -> Prop)
        (BASE: forall dt, dtyp_measure dt = 1%nat -> P dt)
        (IH: forall (n : nat) (dt: dtyp), (forall (dt : dtyp), dtyp_measure dt <= n -> P dt)%nat -> dtyp_measure dt = S n -> P dt),
      forall dt, P dt.
    Proof using Type.
      intros P BASE IH.
      assert (forall n dt, dtyp_measure dt <= n -> P dt)%nat as IHDT.
      { induction n using nat_strong_ind; intros dt SIZE.
        - destruct dt; cbn in SIZE; lia.
        - assert (dtyp_measure dt <= n \/ dtyp_measure dt = S n)%nat as [LEQ | EQ] by lia;
          eauto.
      }

      intros dt.
      eapply IHDT.
      reflexivity.
    Qed.


    Lemma exec_correct_serialize_by_dtyp_undef :
      forall dt CTR pre,
        exec_correct pre (serialize_by_dtyp CTR dt) (serialize_by_dtyp CTR dt) (serialize_by_dtyp CTR dt).
    Proof using Type.
      induction dt; intros;
        try solve [
            eapply exec_correct_bind; auto with EXEC_CORRECT
          ].

      - eapply exec_correct_bind; auto with EXEC_CORRECT.
        do 3 rewrite map_monad_map_monad_In.
        apply exec_correct_map_monad_In.
        intros.
        apply H.
        assumption.

      - eapply exec_correct_bind; auto with EXEC_CORRECT.
        do 3 rewrite map_monad_map_monad_In.
        apply exec_correct_map_monad_In.
        intros.
        apply H.
        assumption.
    Qed.

    Lemma exec_correct_serialize_sbytes_undef :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Undef t) dt) (serialize_sbytes (UVALUE_Undef t) dt) (serialize_sbytes (UVALUE_Undef t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_undef : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes_poison :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Poison t) dt) (serialize_sbytes (UVALUE_Poison t) dt) (serialize_sbytes (UVALUE_Poison t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_poison : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes_oom :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Oom t) dt) (serialize_sbytes (UVALUE_Oom t) dt) (serialize_sbytes (UVALUE_Oom t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_oom : EXEC_CORRECT.


    Lemma exec_correct_pre_map_monad2 :
      forall {A B C}
        (f : forall {M : Type -> Type} {HM: Monad M} {HS:MonadStoreId M} {HR: RAISE_ERROR M} {HO: RAISE_OOM M}, A -> B -> M C)
        (pre : MemState -> store_id -> Prop) (l1 : list A) (l2: list B)
        (H : forall a, In a l1 -> forall b (pre : MemState -> store_id -> Prop), exec_correct pre (f a b) (f a b) (f a b)),
        exec_correct pre (map_monad2 f l1 l2) (map_monad2 f l1 l2) (map_monad2 f l1 l2).
    Proof using Type.
      intros.
      revert pre l2 H.
      induction l1.
      - intros.
        destruct l2.
        + apply exec_correct_ret; eauto.
        + apply exec_correct_raise_error.
      - intros.
        destruct l2.
        + apply exec_correct_raise_error.
        + apply exec_correct_bind.
          * eapply H. left. auto.
          * intros.
            eapply exec_correct_bind.
            -- apply IHl1.
               intros.
               apply H. right.  auto.
            -- intros.
               apply exec_correct_ret; auto.
    Qed.

    Lemma exec_correct_serialize_sbytes :
      forall uv dt pre,
        exec_correct pre (serialize_sbytes uv dt) (serialize_sbytes uv dt) (serialize_sbytes uv dt).
    Proof using Type.
      induction uv; intros dt' pre;
        try solve [
            auto with EXEC_CORRECT
          | eapply exec_correct_bind; eauto with EXEC_CORRECT
          ].
    Qed.

    Lemma read_bytes_correct :
      forall len ptr pre,
        exec_correct pre (read_bytes ptr len) (read_bytes_spec ptr len)
          (@get_consecutive_ptrs exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post RAISE_ERROR_exec_correct_post ptr len;;
           (fun ms st bytes ms' st' =>
              (Forall (fun byte => exists s, MemByte.sbyte_sid byte = inr s /\ s < st) bytes /\ ms = ms' /\ st = st'))).
    Proof using Type.
      unfold read_bytes.
      unfold read_bytes_spec.
      intros len ptr pre.
      eapply exec_correct_bind.
      eapply exec_correct_get_consecutive_pointers.

      intros * VALID POST RUN.
      eapply exec_correct_strengthen_post; cycle 1.
      eapply exec_correct_map_monad.
      intros ptr'.
      apply read_byte_correct.

      clear.
      intros ms st a0 ms' st' _ MAP.
      generalize dependent a0.
      revert ms st ms' st'.
      induction a; intros ms st ms' st' bytes MAP.
      - cbn in *.
        destruct MAP as (?&?&?); subst.
        split; auto.
      - rewrite map_monad_unfold in MAP.
        destruct MAP as (?&?&?&?&?&?&?&?&?).
        cbn in *.
        red in H1.
        destruct H1 as (?&?&?); subst.
        destruct H as (?&?&?); subst.
        eapply IHa in H0.
        destruct H0 as (?&?&?); subst.
        split; auto.
    Qed.

    Lemma read_uvalue_correct :
      forall dt ptr pre,
        exec_correct pre (read_uvalue dt ptr) (read_uvalue_spec dt ptr)
          (a0 <-
             (_ <- get_consecutive_ptrs ptr (N.to_nat (LP.SIZEOF.sizeof_dtyp dt));;
              (fun (ms0 : MemState) (st0 : store_id) (bytes : list MP.BYTE_IMPL.SByte) 
                 (ms'0 : MemState) (st'0 : store_id) =>
                 Forall
                   (fun byte : MP.BYTE_IMPL.SByte =>
                      exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < st0) bytes /\
                   ms0 = ms'0 /\ st0 = st'0));;
           (fun a1 : list MP.BYTE_IMPL.SByte => lift_err_RAISE_ERROR (deserialize_sbytes a1 dt)) a0).
    Proof using Type.
      intros dt ptr pre.
      eapply exec_correct_bind.
      apply read_bytes_correct.
      intros * VALID POST RUN.
      apply exec_correct_lift_err_RAISE_ERROR; auto.
    Qed.

    (* TODO: move this? *)
    Import MP.
    Import LP.
    Import GEP.
    Lemma MemMonad_run_get_consecutive_ptrs:
      forall {M RunM : Type -> Type} {MM : Monad M} {MRun : Monad RunM}
        {MPROV : MonadProvenance LP.PROV.Provenance M} {MSID : MonadStoreId M} {MMS : MonadMemState MemState M}
        {MERR : RAISE_ERROR M} {MUB : RAISE_UB M} {MOOM : RAISE_OOM M} {RunERR : RAISE_ERROR RunM}
        {RunUB : RAISE_UB RunM} {RunOOM : RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
        {MemMonad : MemMonad M RunM}
        `{EQV : @Eq1Equivalence RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)}
        `{LAWS: @MonadLawsE RunM (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) MRun}
        `{RAISEOOM : @RaiseBindM RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_oom RunM RunOOM)}
        `{RAISEERR : @RaiseBindM RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_error RunM RunERR)}
        (ms : MemState) ptr len (st : store_id),
        (@eq1 RunM
              (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)
              (prod store_id (prod MemState (list LP.ADDR.addr)))
              (@MemMonad_run
           M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad (list LP.ADDR.addr)
           (@get_consecutive_ptrs M MM MOOM MERR ptr len) ms st)
              (fmap (fun ptrs => (st, (ms, ptrs))) (@get_consecutive_ptrs RunM MRun RunOOM RunERR ptr len)))%monad.
    Proof using.
      intros M RunM MM1 MRun0 MPROV0 MSID0 MMS0
        MERR0 MUB0 MOOM0 RunERR0 RunUB0 RunOOM0 EQM' EQRI' MLAWS' MemMonad0
        EQV LAWS RAISEOOM RAISEERR ms ptr len st.
      Opaque handle_gep_addr.

      unfold get_consecutive_ptrs.
      destruct (intptr_seq 0 len) as [NOOM_seq | OOM_seq] eqn:HSEQ.
      - cbn.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_run_ret.
        unfold liftM.
        repeat rewrite bind_ret_l.

        destruct
          (map_monad
             (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix])
             NOOM_seq) eqn:HMAPM.
        + cbn.
          rewrite MemMonad_run_bind.
          rewrite rbm_raise_bind; [|typeclasses eauto].

          rewrite MemMonad_run_raise_error.
          rewrite rbm_raise_bind; eauto.
          rewrite rbm_raise_bind; eauto.
          reflexivity.
        + cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_ret.
          rewrite bind_ret_l.
          rewrite bind_ret_l.
          destruct (Monads.sequence l) eqn:HSEQUENCE.
          * cbn; rewrite bind_ret_l.
            rewrite MemMonad_run_ret.
            reflexivity.
          * cbn.
            rewrite rbm_raise_bind; [|typeclasses eauto].
            rewrite MemMonad_run_raise_oom.
            reflexivity.
      - cbn.
        rewrite MemMonad_run_bind.
        unfold liftM.
        rewrite MemMonad_run_raise_oom.
        rewrite bind_bind.
        rewrite rbm_raise_bind; eauto.
        rewrite rbm_raise_bind; eauto.
        reflexivity.
    Qed.

    Lemma exec_correct_step_map_monad_In :
      forall {A B}
        xs
        (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : forall x : A, In x xs -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st IN,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a IN) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a IN ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a (IN : In a xs) res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a IN) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a IN) ms_init st_init res ms st /\
                m_spec a IN ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a (IN : In a xs), exec_correct pre (m_exec a IN) (m_spec a IN) (post_b a IN)) ->
        exec_correct pre (map_monad_In xs m_exec) (map_monad_In xs m_spec) (map_monad_In xs post_b).
    Proof.
      induction xs;
        intros m_exec m_spec pre post_b POST_STEP STEP HM.
      - unfold map_monad.
        apply exec_correct_ret.
      - rewrite map_monad_In_unfold.
        rewrite map_monad_In_unfold.

        eapply exec_correct_bind; auto.
        intros * VALID POST RUN.
        eapply exec_correct_bind.
        { eapply exec_correct_weaken_pre; cycle 1.
          eapply IHxs.
          { intros ms_init0 st_init0 a1 b ms st IN H.
            eapply POST_STEP; eauto.
          }
          { intros ms_init0 st_init0 H ms st a1 IN res H0.
            eapply STEP; cbn in *; eauto.
          }

          intros a1 IN.
          apply HM.

          cbn.
          intros ms st H.
          cbn.
          eapply STEP.
          apply H.
          split.
          apply H.
          split; [| apply H].
          destruct H as (?&?&?).
          cbn in H0.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0 in H2.
          rewrite bind_ret_l in H2.
          eapply POST_STEP; eauto.
        }

        intros * VALID2 POST2 RUN2.
        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_step_map_monad :
      forall {A B}
        xs
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : A -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a) ms_init st_init res ms st /\
                m_spec a ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a, exec_correct pre (m_exec a) (m_spec a) (post_b a)) ->
        exec_correct pre (map_monad m_exec xs) (map_monad m_spec xs) (map_monad post_b xs).
    Proof.
      induction xs;
        intros m_exec m_spec pre post_b POST_STEP STEP HM.
      - unfold map_monad.
        apply exec_correct_ret.
      - rewrite map_monad_unfold.
        rewrite map_monad_unfold.

        eapply exec_correct_bind; auto.
        intros * VALID POST RUN.
        eapply exec_correct_bind.
        { eapply exec_correct_weaken_pre; cycle 1.
          eapply IHxs.
          { intros ms_init0 st_init0 a1 b ms st H.
            eapply POST_STEP; eauto.
          }
          { intros ms_init0 st_init0 H ms st a1 res H0.
            eapply STEP; cbn in *; eauto.
          }

          intros a1 IN.
          apply HM.

          intros ms st H.
          eapply STEP.
          apply H.
          split.
          apply H.
          split; [| apply H].
          destruct H as (?&?&?).
          cbn in H0.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0 in H2.
          rewrite bind_ret_l in H2.
          eapply POST_STEP; eauto.
        }

        intros * VALID2 POST2 RUN2.
        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_step_map_monad_ :
      forall {A B}
        xs
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : A -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a) ms_init st_init res ms st /\
                m_spec a ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a, exec_correct pre (m_exec a) (m_spec a) (post_b a)) ->
        exec_correct pre (map_monad_ m_exec xs) (map_monad_ m_spec xs) (map_monad_ post_b xs).
    Proof.
      intros A B xs m_exec m_spec pre post_b POST_STEP STEP HM.
      unfold map_monad_.
      apply exec_correct_bind.
      apply exec_correct_step_map_monad; auto.

      intros * VALID POST RUN.
      apply exec_correct_ret.
    Qed.

    Lemma get_consecutive_ptrs_preserves_state :
      forall st ms st' ms' ptr bytes a,
        @within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
          (@Within_err_ub_oom_MemM MemM Eff
             (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                RunOOM EQM EQRI MLAWS MM) MRun
             (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID MMS MERR MUB
             MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) (list ADDR.addr)
          (@get_consecutive_ptrs MemM MM0 MOOM MERR ptr (@Datatypes.length BYTE_IMPL.SByte bytes))
          (@pair store_id MemState st ms)
          (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
             (list ADDR.addr) a) (@pair store_id MemState st' ms') ->
        (ms, st) = (ms', st').
    Proof.
      intros st ms st' ms' ptr bytes a H.
      cbn in H.
      repeat red in H.
      destruct H as (?&?&?).
      cbn in H, H0.
      rewrite H in H0.
      rewrite bind_ret_l in H0.
      rewrite MemMonad_run_get_consecutive_ptrs in H0.
      unfold fmap in H0.
      cbn in H0.
      unfold liftM in H0.
      pose proof get_consecutive_ptrs_inv ptr (Datatypes.length bytes).
      destruct H1 as [[msg OOM] | [ptrs GCP]].
      { rewrite OOM in H0.
        rewrite rbm_raise_bind in H0; try typeclasses eauto.
        symmetry in H0.
        apply MemMonad_eq1_raise_oom_inv in H0; contradiction.
      }

      rewrite GCP in H0.
      repeat rewrite bind_ret_l in H0.
      eapply eq1_ret_ret in H0; try typeclasses eauto.
      inv H0.
      auto.
    Qed.

    Lemma write_bytes_correct :
      forall ptr bytes,
        exec_correct
          (fun ms st => Forall (fun byte => exists s, MemByte.sbyte_sid byte = inr s /\ (s < st)%N) bytes)
          (write_bytes ptr bytes) (write_bytes_spec ptr bytes)
          (@exec_correct_post_bind (list ADDR.addr) unit
             (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                   (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte bytes)))
                (fun ixs : list IP.intptr =>
                   @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                     (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                        RAISE_ERROR_exec_correct_post
                        (@map_monad (sum string) (EitherMonad.Monad_either string) IP.intptr
                           (OOM ADDR.addr)
                           (fun ix : IP.intptr =>
                              handle_gep_addr (DTYPE_I 8) ptr (@cons dvalue (DVALUE_IPTR ix) (@nil dvalue)))
                           ixs))
                     (fun addrs : list (OOM ADDR.addr) =>
                        @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                          (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
             (fun a : list ADDR.addr =>
                @exec_correct_post_bind (list unit) unit
                  (@map_monad_In exec_correct_post Monad_exec_correct_post (prod ADDR.addr BYTE_IMPL.SByte)
                     unit (@zip ADDR.addr BYTE_IMPL.SByte a bytes)
                     (fun (H : prod ADDR.addr BYTE_IMPL.SByte)
                        (_ : @In (prod ADDR.addr BYTE_IMPL.SByte) H (@zip ADDR.addr BYTE_IMPL.SByte a bytes))
                        (_ : MemState) (st : store_id) (_ : unit) (_ : MemState)
                        (st' : store_id) => @eq store_id st st'))
                  (fun _ : list unit => @exec_correct_post_ret unit tt))).
    Proof using Type.
      intros ptr bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind.
        apply exec_correct_get_consecutive_pointers.
        intros * VALID POST RUN.
        cbn in POST.
        destruct POST as (?&?&?&?&?&?&?&?&?).
        unfold lift_OOM in H.
        break_match_hyp_inv.
        destruct H3; subst.

        unfold map_monad_.
        eapply exec_correct_bind.
        { repeat rewrite map_monad_map_monad_In.
          eapply exec_correct_weaken_pre
            with
            (weak_pre:=(fun (ms_k : MemState) (st_k : store_id) =>
                          Forall
                            (fun byte : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < x1)
                            bytes /\ x1 <= st_k)).
          { intros ms st (?&?&?).
            eapply get_consecutive_ptrs_preserves_state in H2; inv H2.
            split; eauto.
            lia.
          }

          eapply exec_correct_step_map_monad_In
            with (post_b := fun _ _ _ st _ _ st' => st = st').
          3: {
            intros [a' b] IN.
            eapply exec_correct_weaken_pre
              with (weak_pre:=(fun ms st => exists s, MemByte.sbyte_sid b = inr s /\ (s < st)%N)).
            { intros ms st (H&LT).
              apply zip_In_both in IN as (_&IN).
              eapply Forall_forall in H; eauto.
              destruct H as (?&?&?).
              exists x5; split; eauto.
              lia.
            }

            eapply write_byte_correct.
          }
          {
            intros ms_init st_init [a' b] [] ms st IN H.
            unfold lift_OOM in *; break_match_hyp_inv.
            destruct H3; subst.
            eapply write_byte_preserves_store_id.
            cbn.
            repeat red.
            eexists.
            split; cbn.
            reflexivity.
            rewrite bind_ret_l.
            apply H.
          }

          (* STEP for map_monad_In *)
          intros ms_init st_init (?&?) ms st [a' b] IN [] (?&?).
          split; eauto.
          destruct H4; subst.
          auto.
        }

        intros * VALID' POST' RUN'.
        apply exec_correct_ret.
      }

      intros.
      cbn in H.
      auto.
    Qed.

    Lemma to_ubytes_sids_bounded :
      forall uv dt sid st,
        sid < st ->
        Forall (fun byte : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < st)
          (MemByte.to_ubytes uv dt sid).
    Proof.
      intros uv dt sid st H.
      apply Forall_map.
      remember (N.to_nat (SIZEOF.sizeof_dtyp dt)) as n.
      clear Heqn.
      remember 0 as start.
      clear Heqstart.
      revert start.
      induction n; intros start.
      - cbn.
        constructor.
      - cbn.
        constructor.
        + unfold MemByte.sbyte_sid.
          rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
          exists sid; auto.
        + apply IHn.
    Qed.

    Lemma write_uvalue_correct :
      forall dt ptr uv pre,
        exec_correct pre (write_uvalue dt ptr uv) (write_uvalue_spec dt ptr uv)
          (@bind exec_correct_post Monad_exec_correct_post (list BYTE_IMPL.SByte) unit
             (@serialize_sbytes exec_correct_post Monad_exec_correct_post MonadStoreId_exec_correct_post uv
                dt)
             (fun a : list BYTE_IMPL.SByte =>
                (fun a0 : list BYTE_IMPL.SByte =>
                   @exec_correct_post_bind (list ADDR.addr) unit
                     (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                        (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                           (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte a0)))
                        (fun ixs : list IP.intptr =>
                           @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                             (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post
                                Monad_exec_correct_post RAISE_ERROR_exec_correct_post
                                (@map_monad (sum string) (EitherMonad.Monad_either string) IP.intptr
                                   (OOM ADDR.addr)
                                   (fun ix : IP.intptr =>
                                      handle_gep_addr (DTYPE_I 8) ptr (@cons dvalue (DVALUE_IPTR ix) (@nil dvalue)))
                                   ixs))
                             (fun addrs : list (OOM ADDR.addr) =>
                                @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                                  (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
                     (fun a1 : list ADDR.addr =>
                        @exec_correct_post_bind (list unit) unit
                          (@map_monad_In exec_correct_post Monad_exec_correct_post
                             (prod ADDR.addr BYTE_IMPL.SByte) unit (@zip ADDR.addr BYTE_IMPL.SByte a1 a0)
                             (fun (H : prod ADDR.addr BYTE_IMPL.SByte)
                                (_ : @In (prod ADDR.addr BYTE_IMPL.SByte) H
                                       (@zip ADDR.addr BYTE_IMPL.SByte a1 a0)) (_ : MemState)
                                (st : store_id) (_ : unit) (_ : MemState) (st' : store_id) =>
                                @eq store_id st st')) (fun _ : list unit => @exec_correct_post_ret unit tt))) a)).
    Proof using Type.
      intros dt ptr uv pre.
      { apply exec_correct_bind.
        apply exec_correct_serialize_sbytes.
        intros * VALID POST RUN.
        eapply exec_correct_weaken_pre.
        2: apply write_bytes_correct.

        intros ms st (?&?&?).
        rename a into bytes.

        repeat red in POST.
        destruct POST as (?&?&?&?&?&?&?); subst.
        cbn in H2.
        destruct H2 as (?&?&?); subst.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in *.

        destruct H1 as (?&?&?&?&?).
        subst.

        rewrite H0 in H4.
        rewrite bind_ret_l in H4.
        rewrite RUN in H4.
        eapply eq1_ret_ret in H4; try typeclasses eauto.
        inv H4.

        eapply to_ubytes_sids_bounded; lia.
      }
    Qed.

    Lemma allocate_bytes_correct :
      forall bytes ,
        exec_correct
          (fun _ st =>
             Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes)
          (allocate_bytes bytes)
          (allocate_bytes_spec_MemPropT bytes)
          exec_correct_id_post.
    Proof using Type.
      intros bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { eapply exec_correct_bind.
        apply exec_correct_fresh_provenance.

        intros * VALID POST RUN.
        cbn in POST.
        eapply exec_correct_weaken_pre; cycle 1.
        apply allocate_bytes_with_pr_correct.

        intros ms st (?&?&?).
        cbn in *.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in *.
        rewrite H0 in H2.
        rewrite bind_ret_l in H2.
        rewrite RUN in H2.
        eapply eq1_ret_ret in H2; try typeclasses eauto.
        inv H2.
        destruct POST as (?&?&?&?); subst.
        apply H.
      }
      auto.
    Qed.

    Hint Resolve allocate_bytes_correct : EXEC_CORRECT.

    Lemma exec_correct_repeatMN :
      forall {A} (n : N) (m_exec : MemM A) (m_spec : MemPropT MemState A)
        (pre : exec_correct_pre)
        (post : exec_correct_post A)
        (POST_STEP :
          forall ms_init st_init res ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState A))
              (MemMonad_run m_exec ms_init st_init) (ret (st, (ms, res))))%monad ->
            post ms_init st_init res ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) res,
              m_spec ms_init (ret (ms, res)) ->
              post ms_init st_init res ms st ->
              pre ms st),
        (exec_correct pre m_exec m_spec post) ->
        exec_correct pre
          (repeatMN n m_exec)
          (repeatMN n m_spec)
          (repeatMN n post).
    Proof using Type.
      intros A n.
      induction n using N.peano_rect; intros pre m_exec m_spec post POST_STEP STEP HM.
      - eapply exec_correct_strengthen_post; cycle 1.
        eapply exec_correct_ret.
        eauto.
      - do 2 rewrite repeatMN_succ.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind; auto.
          apply HM.

          intros * VALID POST RUN.
          eapply exec_correct_weaken_pre; cycle 1.
          apply exec_correct_bind.
          { eapply IHn.
            3: {
              apply HM.
            }

            { intros ms_init0 st_init0 res ms st H.
              apply POST_STEP; eauto.
            }

            intros ms_init0 st_init0 H ms st res H0.
            eapply STEP; eauto.
          }

          intros * VALID' POST' RUN'.
          apply exec_correct_ret.
          intros ms st (?&?&?).
          eapply STEP; eauto.
          apply POST_STEP.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0, bind_ret_l in H2.
          auto.
        }

        intros ms st a ms' st' H0 H.
        cbn in H.
        repeat red in H.
        destruct H as (?&?&?&?&?&?&?&?&?).
        rewrite repeatMN_succ.
        cbn.
        repeat red.
        exists x, x0, x1.
        split; eauto.
        repeat red.
        exists x2, x3, x4.
        split; eauto.
    Qed.

    Lemma exec_correct_repeatMN_Forall_simple :
      forall {A} (n : N) (m_exec : MemM A) (m_spec : MemPropT MemState A)
        (pre : exec_correct_pre)
        (post : exec_correct_post A),
        (exec_correct pre m_exec m_spec (fun ms st a ms' st' => post ms st a ms' st' /\ ms = ms' /\ st = st')) ->
        exec_correct pre
          (repeatMN n m_exec)
          (repeatMN n m_spec)
          (fun ms st res ms' st' => Forall (fun r => post ms st r ms' st') res /\ ms = ms' /\ st = st').
    Proof using Type.
      intros A n.
      induction n using N.peano_rect; intros pre m_exec m_spec post HM.
      - eapply exec_correct_strengthen_post; cycle 1.
        eapply exec_correct_ret.
        intros ms st a ms' st' ? (?&?&?); subst.
        eauto.
      - do 2 rewrite repeatMN_succ.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind; auto.
          apply HM.

          intros * VALID POST RUN.
          eapply exec_correct_weaken_pre; cycle 1.
          apply exec_correct_bind.
          { eapply IHn.
            apply HM.
          }

          intros * VALID' POST' RUN'.
          apply exec_correct_ret.
          cbn in POST.
          destruct POST as (?&?&?); subst.
          intros ms st (?&?&?).
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in H3.
          cbn in H1.
          rewrite H1, bind_ret_l in H3.
          rewrite RUN in H3.
          eapply eq1_ret_ret in H3; try typeclasses eauto.
          inv H3.
          auto.
        }

        intros ms st a ms' st' SPEC H.
        cbn in H.
        repeat red in H.
        destruct H as (?&?&?&?&?&?&?&?&?).
        destruct H0 as (?&?&?); subst.
        destruct H as (?&?&?); subst.
        destruct H1 as (?&?&?); subst.
        auto.
    Qed.

    Lemma exec_correct_clear_assertion :
      forall {A} (pre : MemState -> store_id -> Prop) (m_exec : MemM A) (m_spec : MemPropT MemState A) (assertion : Prop) post,
        exec_correct pre m_exec m_spec post ->
        assertion ->
        exec_correct pre m_exec (MemPropT_assert_pre assertion;; m_spec) post.
    Proof using Type.
      intros A pre m_exec m_spec assertion post EXEC ASSERTION.
      repeat red.
      intros ms st H H0.
      repeat red in EXEC.
      specialize (EXEC _ _ H H0).
      destruct EXEC as [UB | EXEC].
      - left.
        destruct UB as (?&?&?).
        exists x, x0.
        cbn.
        right.
        exists ms, tt.
        split; eauto.
      - destruct EXEC as (?&?&?&?&?&?).
        right.
        exists x, x0, x1.
        split; eauto.
        split; eauto.
        destruct_err_ub_oom x; subst; cbn in *.
        + right.
          exists ms, tt.
          split; eauto.
        + right.
          exists ms, tt.
          split; eauto.
        + right.
          exists ms, tt.
          split; eauto.
        + exists ms, tt.
          split; eauto.
    Qed.

    Hint Resolve exec_correct_clear_assertion : EXEC_CORRECT.

    Lemma MemMonad_repeatMN_repeatN :
      forall ms st num_elements l,
        @eq1 (itree Eff)
          (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
             RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState (list (list BYTE_IMPL.SByte))))
          (@MemMonad_run MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM
             EQRI MLAWS MM (list (list BYTE_IMPL.SByte))
             (@repeatMN (list BYTE_IMPL.SByte) MemM MM0 num_elements
                (@ret MemM MM0 (list BYTE_IMPL.SByte) l)) ms st)
          (@ret (itree Eff) MRun (prod store_id (prod MemState (list (list BYTE_IMPL.SByte))))
             (@pair store_id (prod MemState (list (list BYTE_IMPL.SByte))) st
                (@pair MemState (list (list BYTE_IMPL.SByte)) ms (repeatN num_elements l)))).
    Proof.
      intros ms st.
      induction num_elements using N.peano_ind;
        intros l.
      - cbn in *.
        rewrite MemMonad_run_ret.
        reflexivity.
      - rewrite repeatMN_succ.
        repeat setoid_rewrite MemMonad_run_bind.
        rewrite MemMonad_run_ret, bind_ret_l, MemMonad_run_bind.
        rewrite IHnum_elements.
        rewrite bind_ret_l.
        rewrite MemMonad_run_ret.
        rewrite repeatN_succ.
        reflexivity.
    Qed.

    Lemma generate_num_undef_bytes_bounded :
      forall sid st dt bytes n,
        sid < st ->
        generate_num_undef_bytes n dt sid = NoOom bytes ->
        Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes.
    Proof.
      intros sid st dt bytes n LT GEN.
      unfold generate_num_undef_bytes in GEN.
      remember 0 as start_idx.
      clear Heqstart_idx.
      revert start_idx bytes GEN.
      induction n using N.peano_ind;
        intros start_idx bytes GEN.
      - cbn in *.
        inv GEN.
        constructor.
      - unfold generate_num_undef_bytes_h in GEN.
        pose proof @N.recursion_succ (N -> OOM (list BYTE_IMPL.SByte)) eq (fun _ : N => ret [])
          (fun (_ : N) (mf : N -> OOM (list BYTE_IMPL.SByte)) (x : N) =>
             rest_bytes <- mf (N.succ x);;
             ret (BYTE_IMPL.uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes))
          eq_refl.
        forward H.
        { unfold Proper, respectful.
          intros x y H0 x0 y0 H1; subst.
          reflexivity.
        }
        specialize (H n).
        rewrite H in GEN.
        clear H.

        destruct
          (N.recursion (fun _ : N => ret [])
             (fun (_ : N) (mf : N -> OOM (list BYTE_IMPL.SByte)) (x : N) =>
                rest_bytes <- mf (N.succ x);;
                ret (BYTE_IMPL.uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes)) n
             (N.succ start_idx)) eqn:HREC.
        + (* No OOM *)
          cbn in GEN.
          inv GEN.
          constructor.
          { exists sid.
            unfold MemByte.sbyte_sid.
            rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
            auto.
          }
          eapply IHn.
          unfold generate_num_undef_bytes_h.
          apply HREC.
        + (* OOM *)
          cbn in GEN.
          inv GEN.
    Qed.

    Lemma generate_undef_bytes_bounded :
      forall sid st dt bytes,
        sid < st ->
        generate_undef_bytes dt sid = NoOom bytes ->
        Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes.
    Proof.
      intros sid st dt bytes LT GEN.
      unfold generate_undef_bytes in GEN.
      eapply generate_num_undef_bytes_bounded; eauto.
    Qed.

    Lemma allocate_dtyp_correct :
      forall dt num_elements pre,
        exec_correct pre (allocate_dtyp dt num_elements) (allocate_dtyp_spec dt num_elements)
          (@bind exec_correct_post Monad_exec_correct_post store_id ADDR.addr
             (@fresh_sid exec_correct_post MonadStoreId_exec_correct_post)
             (fun a : store_id =>
                (fun a0 : store_id =>
                   @bind exec_correct_post Monad_exec_correct_post (list (list BYTE_IMPL.SByte)) ADDR.addr
                     (fun (ms : MemState) (st : store_id) (res : list (list BYTE_IMPL.SByte))
                        (ms' : MemState) (st' : store_id) =>
                        Logic.and
                          (@Forall (list BYTE_IMPL.SByte)
                             (fun r : list BYTE_IMPL.SByte => Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) r) res)
                          (Logic.and (@eq MemState ms ms') (@eq store_id st st')))
                     (fun a1 : list (list BYTE_IMPL.SByte) =>
                        (fun _ : list (list BYTE_IMPL.SByte) => @exec_correct_id_post ADDR.addr) a1)) a)).
    Proof using Type.
      intros dt num_elements pre.
      destruct (dtyp_eqb dt DTYPE_Void) eqn:DT.
      { (* UB because of attempting to allocate a void type... *)
        unfold allocate_dtyp.
        rewrite DT.
        apply dtyp_eqb_eq in DT; subst.
        unfold allocate_dtyp_spec.
        repeat red.
        intros ms st H H0.
        left.
        exists ms.
        exists ""%string.
        left.
        cbn.
        eauto.
      }

      assert (dt <> DTYPE_Void) as NVOID.
      { intros CONTRA.
        subst.
        rewrite dtyp_eqb_refl in DT.
        discriminate.
      }

      apply exec_correct_clear_assertion; auto.
      unfold allocate_dtyp.
      rewrite DT.

      { apply exec_correct_bind.
        apply exec_correct_fresh_sid.
        intros * VALID1 POST1 RUN1.
        apply exec_correct_bind.
        { eapply exec_correct_repeatMN_Forall_simple.
          eapply exec_correct_strengthen_post; cycle 1.
          apply exec_correct_lift_OOM.
          intros ms st a0 ms' st' PRE POST.
          destruct PRE as (?&?&?).
          cbn in H0, H1.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in H0, H2.
          rewrite H0, bind_ret_l in H2.
          rewrite RUN1 in H2.
          eapply eq1_ret_ret in H2; try typeclasses eauto.
          inv H2.
          unfold lift_OOM in POST.
          break_match_hyp_inv.
          destruct H3; subst.
          split; eauto.

          eapply generate_undef_bytes_bounded; eauto.
          destruct POST1 as (?&?&?); subst.
          lia.
        }

        intros * VALID2 POST2 RUN2.
        eapply exec_correct_weaken_pre; cycle 1.
        apply allocate_bytes_correct.
        { intros ms st (?&?&?).
          destruct H as (?&?&?).
          destruct POST2 as (?&?&?).
          apply Forall_concat.
          subst.
          destruct H0 as (?&?&?).
          cbn in *.
          repeat red in H2.
          destruct H2 as (?&?&?).
          cbn in *.
          rewrite H2, bind_ret_l in H6.
          destruct POST1 as (?&?&?); subst.
          rewrite RUN1 in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          rewrite H0, bind_ret_l in H5.

          unfold lift_OOM in *.
          break_match_hyp.
          2: {
            induction num_elements using N.peano_ind.
            - cbn in *.
              rewrite MemMonad_run_ret in RUN2.
              eapply eq1_ret_ret in RUN2; try typeclasses eauto.
              inv RUN2.
              constructor.
            - clear - RUN2.
              rewrite repeatMN_succ in RUN2.
              rewrite MemMonad_run_bind in RUN2.
              rewrite MemMonad_run_raise_oom in RUN2.
              rewrite rbm_raise_bind in RUN2; try typeclasses eauto.
              symmetry in RUN2.
              eapply MemMonad_eq1_raise_oom_inv in RUN2; contradiction.
          }

          assert (st_after_m0 = st).
          { clear - H5.
            rewrite MemMonad_repeatMN_repeatN in H5.
            eapply eq1_ret_ret in H5; try typeclasses eauto.
            inv H5; auto.
          }
          subst.
          auto.
        }
      }
    Qed.

    Lemma memcpy_correct :
      forall src dst len volatile pre,
        exec_correct pre (memcpy src dst len volatile) (memcpy_spec src dst len volatile)
          (a0 <-
             (_ <-
                @get_consecutive_ptrs exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                  RAISE_ERROR_exec_correct_post src (Z.to_nat len);;
              (fun (ms0 : MemState) (st0 : store_id) (bytes : list BYTE_IMPL.SByte) 
                 (ms'0 : MemState) (st'0 : store_id) =>
                 @Forall BYTE_IMPL.SByte
                   (fun byte : BYTE_IMPL.SByte =>
                      exists s : store_id, MemByte.sbyte_sid byte = @inr string store_id s /\ s < st0) bytes /\
                   ms0 = ms'0 /\ st0 = st'0));;
           (fun a1 : list BYTE_IMPL.SByte =>
              @exec_correct_post_bind (list ADDR.addr) unit
                (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                   (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                      (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte a1)))
                   (fun ixs : list IP.intptr =>
                      @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                        (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                           RAISE_ERROR_exec_correct_post
                           (@map_monad err (EitherMonad.Monad_either string) IP.intptr 
                              (OOM ADDR.addr)
                              (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) dst [DVALUE_IPTR ix]) ixs))
                        (fun addrs : list (OOM ADDR.addr) =>
                           @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                             (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
                (fun a2 : list ADDR.addr =>
                   @exec_correct_post_bind (list unit) unit
                     (@map_monad_In exec_correct_post Monad_exec_correct_post (ADDR.addr * BYTE_IMPL.SByte) unit
                        (@zip ADDR.addr BYTE_IMPL.SByte a2 a1)
                        (fun (H : ADDR.addr * BYTE_IMPL.SByte)
                           (_ : @In (ADDR.addr * BYTE_IMPL.SByte) H (@zip ADDR.addr BYTE_IMPL.SByte a2 a1))
                           (_ : MemState) (st0 : store_id) (_ : unit) (_ : MemState) (st'0 : store_id) =>
                           st0 = st'0)) (fun _ : list unit => @exec_correct_post_ret unit tt))) a0).
    Proof using Type.
      intros src dst len volatile pre.
      unfold memcpy, memcpy_spec.
      break_match; [apply exec_correct_raise_ub|].
      unfold MME.OVER_H.no_overlap, MME.OVER.overlaps.
      unfold OVER_H.no_overlap, OVER.overlaps.
      break_match; [|apply exec_correct_raise_ub].

      { apply exec_correct_bind.
        apply read_bytes_correct.
        intros * VALID POST RUN.
        eapply exec_correct_weaken_pre; cycle 1.
        apply write_bytes_correct.

        intros ms st H.
        cbn.
        destruct H as (?&?&?).
        repeat red in H1.
        destruct H1 as (?&?&?&?).
        assert (x = ms_init).
        { red in H1.
          cbn in H1.
          destruct H1 as (?&?&?&?&?&?&?).
          unfold lift_OOM in *.
          unfold lift_err_RAISE_ERROR in *.
          repeat break_match_hyp_inv.
          auto.
        }

        destruct POST as (?&?&?&?&?&?&?); subst.
        destruct H4 as (?&?&?&?&?&?&?&?&?).
        unfold lift_OOM in *.
        repeat break_match_hyp_inv.
        destruct H8, H7; subst.
        unfold lift_err_RAISE_ERROR in H4.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in H0, H3.
        rewrite H0, bind_ret_l in H3.
        rewrite RUN in H3.
        eapply eq1_ret_ret in H3; try typeclasses eauto.
        inv H3.
        auto.
      }
    Qed.

    Lemma memset_correct :
      forall dst val len sid volatile,
        exec_correct
          (fun ms st => sid < st)
          (memset dst val len sid volatile) (memset_spec dst val len sid volatile)
          (@exec_correct_post_bind (list ADDR.addr) unit
             (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                   (list IP.intptr)
                   (intptr_seq 0
                      (@Datatypes.length BYTE_IMPL.SByte
                         (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                            (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))))
                (fun ixs : list IP.intptr =>
                   @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                     (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                        RAISE_ERROR_exec_correct_post
                        (@map_monad err (EitherMonad.Monad_either string) IP.intptr (OOM ADDR.addr)
                           (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) dst [DVALUE_IPTR ix]) ixs))
                     (fun addrs : list (OOM ADDR.addr) =>
                        @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                          (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
             (fun a0 : list ADDR.addr =>
                @exec_correct_post_bind (list unit) unit
                  (@map_monad_In exec_correct_post Monad_exec_correct_post (ADDR.addr * BYTE_IMPL.SByte) unit
                     (@zip ADDR.addr BYTE_IMPL.SByte a0
                        (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                           (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))
                     (fun (H : ADDR.addr * BYTE_IMPL.SByte)
                        (_ : @In (ADDR.addr * BYTE_IMPL.SByte) H
                               (@zip ADDR.addr BYTE_IMPL.SByte a0
                                  (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                                     (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))) 
                        (_ : MemState) (st0 : store_id) (_ : unit) (_ : MemState) (st'0 : store_id) => 
                        st0 = st'0)) (fun _ : list unit => @exec_correct_post_ret unit tt))).
    Proof using Type.
      intros dst val len sid volatile.
      unfold memset, memset_spec.
      break_match; [apply exec_correct_raise_ub|].
      eapply exec_correct_weaken_pre; cycle 1.
      eapply write_bytes_correct.
      { intros ms st H.
        cbn.
        apply Forall_repeatN.
        exists sid.
        unfold MemByte.sbyte_sid.
        rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
        auto.
      }
    Qed.

    Lemma handle_memory_correct :
      forall T (m : MemoryE T) pre,
        exec_correct pre (handle_memory T m) (handle_memory_prop T m) exec_correct_id_post.
    Proof using Type.
      intros T m pre.
      destruct m.
      - (* MemPush *)
        cbn.
        apply mempush_correct.
      - (* MemPop *)
        cbn.
        apply mempop_correct.
      - (* Alloca *)
        unfold handle_memory.
        unfold handle_memory_prop.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply allocate_dtyp_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }

        intros ms st a ms' st' H H0.
        auto.
      - (* Load *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        eapply exec_correct_strengthen_post; cycle 1.
        apply read_uvalue_correct.
        intros ms st a0 ms' st' H H0.
        auto.
      - (* Store *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        eapply exec_correct_strengthen_post; cycle 1.
        apply write_uvalue_correct.
        intros ms st a0 ms' st' H H0.
        auto.
    Qed.

    Lemma handle_memcpy_correct:
      forall args pre,
        exec_correct pre (handle_memcpy args) (handle_memcpy_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_memcpy, handle_memcpy_prop.
      repeat (break_match; try eapply exec_correct_strengthen_post; try apply exec_correct_raise_error; eauto).
      all: eapply exec_correct_strengthen_post; cycle 1; [apply memcpy_correct|auto].
    Qed.

    Lemma handle_memset_correct:
      forall args pre,
        exec_correct pre (handle_memset args) (handle_memset_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_memset, handle_memset_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).
      { eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply exec_correct_fresh_sid; eauto.
          intros a0 ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
          eapply exec_correct_weaken_pre; cycle 1.
          apply memset_correct.
          intros ms st (?&?&?).
          cbn in *.
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in *.
          rewrite H3, bind_ret_l, H1 in H5.
          eapply eq1_ret_ret in H5; try typeclasses eauto.
          inv H5.
          lia.
        }
        auto.
      }
      { eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply exec_correct_fresh_sid; eauto.
          intros a0 ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
          eapply exec_correct_weaken_pre; cycle 1.
          apply memset_correct.
          intros ms st (?&?&?).
          cbn in *.
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in *.
          rewrite H3, bind_ret_l, H1 in H5.
          eapply eq1_ret_ret in H5; try typeclasses eauto.
          inv H5.
          lia.
        }
        auto.
      }
    Qed.

    Lemma malloc_bytes_correct :
      forall bytes,
        exec_correct
          (fun ms st => Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes)
          (malloc_bytes bytes) (malloc_bytes_spec_MemPropT bytes) exec_correct_id_post.
    Proof using Type.
      intros bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind.
        apply exec_correct_fresh_provenance.
        intros a ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
        eapply exec_correct_weaken_pre; cycle 1.
        apply malloc_bytes_with_pr_correct.

        intros ms st (?&?&?).
        cbn in H3.
        repeat red in H3.
        destruct H3 as (?&?&?).
        cbn in H3.
        cbn in H5.
        rewrite H3, bind_ret_l, H1 in H5.
        eapply eq1_ret_ret in H5; try typeclasses eauto.
        inv H5.
        auto.
        destruct H0 as (?&?&?&?).
        subst.
        auto.
      }
      auto.
    Qed.

    Hint Resolve malloc_bytes_correct : EXEC_CORRECT.

    Lemma handle_malloc_correct:
      forall args pre,
        exec_correct pre (handle_malloc args) (handle_malloc_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_malloc, handle_malloc_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).

      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
    Qed.

    Lemma handle_free_correct:
      forall args pre,
        exec_correct pre (handle_free args) (handle_free_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_free, handle_free_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).
      subst.
      all: apply free_correct.
    Qed.

    Lemma handle_intrinsic_correct:
      forall T (e : IntrinsicE T) pre,
        exec_correct pre (handle_intrinsic T e) (handle_intrinsic_prop T e) exec_correct_id_post.
    Proof using Type.
      intros T e pre.
      unfold handle_intrinsic, handle_intrinsic_prop.
      break_match.
      break_match.
      { (* Memcpy *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_memcpy_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Memset *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_memset_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Malloc *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_malloc_correct.
          intros * VALID POST RUN.
          eapply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Free *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_free_correct.
          intros * VALID POST RUN.
          eapply exec_correct_ret.
        }
        auto.
      }

      apply exec_correct_raise_error.
    Qed.
  End Correctness.

  Import LP.PROV.
  Import LP.SIZEOF.
  Import LP.ADDR.

  Lemma find_free_block_inv :
    forall len pr ms_init
      (res : err_ub_oom (MemState * (addr * list addr)))
      (FIND : find_free_block len pr ms_init res),
      (* Success *)
      (exists ptr ptrs,
          res = ret (ms_init, (ptr, ptrs))) \/
        (* OOM *)
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros len pr ms_init res FIND.
    unfold find_free_block in FIND.
    cbn in *.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.

    - (* OOM *)
      right.
      exists oom_res.
      reflexivity.
    - (* Success *)
      destruct res' as [ms' [ptr ptrs]].
      destruct FIND as [MEQ BLOCKFREE].
      subst.
      left.
      do 2 eexists.
      reflexivity.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_no_ub :
    forall (ms_init : MemState)
      bytes
      (ub_msg : string),
      ~ allocate_bytes_spec_MemPropT bytes ms_init (raise_ub ub_msg).
  Proof.
    intros ms_init bytes ub_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [CONTRA | CONTRA]; try contradiction.
    destruct CONTRA as [ms''' [[ptr' ptrs'] [POST CONTRA]]]; contradiction.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_no_err :
    forall (ms_init : MemState)
      bytes
      (err_msg : string),
      ~ allocate_bytes_spec_MemPropT bytes ms_init (raise_error err_msg).
  Proof.
    intros ms_init bytes err_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [[] | [ms''' [[ptr' ptrs'] [POST []]]]].
  Qed.

  Lemma allocate_bytes_spec_MemPropT_inv :
    forall (ms_init : MemState)
      bytes
      (res : err_ub_oom (MemState * LP.ADDR.addr))
      (ALLOC : allocate_bytes_spec_MemPropT bytes ms_init res),
      (exists ms_final ptr,
          res = ret (ms_final, ptr)) \/
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros ms_init bytes res ALLOC.
    unfold allocate_bytes_spec_MemPropT in ALLOC.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.
    - (* OOM *)
      right. eexists; reflexivity.
    - (* UB *)
      destruct ALLOC as [[] | [ms' [pr' [FRESH [[] | ALLOC]]]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] [UB | ALLOC]]]];
        try contradiction; subst.

      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      tauto.
    - (* Error *)
      destruct ALLOC as [[] | [ms' [pr' [FRESH [[] | ALLOC]]]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] [[] | ALLOC]]]].
      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      tauto.
    - (* Success *)
      destruct res' as [ms a].
      subst.
      left.

      destruct ALLOC as [ms' [pr' [FRESH ALLOC]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] ALLOC]]]; subst.
      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      destruct ALLOC as [[POST [PTREQ PTRSEQ]] [MEQ PTREQ']].
      subst.
      repeat eexists.
  Qed.

  Lemma repeatMN_MemPropT_length :
    forall {A} n (ma : MemPropT MemState A) ms ms' a,
      repeatMN n ma ms (ret (ms', a)) -> length a = N.to_nat n.
  Proof.
    intros A n.
    induction n using N.peano_rect; intros ma ms ms' a REP.
    - cbn in *.
      destruct REP as [MEQ AEQ]; subst.
      reflexivity.
    - rewrite repeatMN_succ in REP.
      cbn in REP.
      destruct REP as [ms1 [a0 [M [ms2 [a1 [REP [MEQ AEQ]]]]]]]; subst.
      cbn.
      apply IHn in REP.
      lia.
  Qed.

  Lemma allocate_dtyp_spec_inv :
    forall (ms_init : MemState) dt num_elements
      (NON_VOID : dt <> DTYPE_Void)
      (res : err_ub_oom (MemState * LP.ADDR.addr))
      (ALLOC : allocate_dtyp_spec dt num_elements ms_init res),
      (exists ms_final ptr,
          res = ret (ms_final, ptr)) \/
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros ms_init dt num_elements NON_VOID res ALLOC.
    unfold allocate_dtyp_spec in *.
    Opaque allocate_bytes_spec_MemPropT.
    cbn in ALLOC.

    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.
    - (* OOM *)
      right. eexists; reflexivity.
    - (* UB *)
      destruct ALLOC as [UB | ALLOC]; try contradiction.
      destruct ALLOC as [ms' [[] [[MS NVOID] [UB | ALLOC]]]]; try contradiction.
      symmetry in MS; subst.
      destruct ALLOC as [ms' [sid [FRESH [GEN | ALLOC]]]].
      { induction num_elements using N.peano_rect; [cbn in *; contradiction|].
        rewrite repeatMN_succ in GEN.
        destruct (generate_undef_bytes dt sid); cbn in *.
        + destruct GEN as [[] | [ms'' [l' [[MEQ LEQ] GEN]]]]; subst.
          destruct GEN as [GEN | [ms'' [l' [GEN []]]]]; eauto.
        + destruct GEN as [[] | [ms'' [l' [[] GEN]]]].
      }

      destruct ALLOC as [ms'' [bytes [GEN ALLOC]]].
      destruct (generate_undef_bytes dt sid) eqn:HGEN; cbn in *.
      { assert (length bytes = N.to_nat num_elements) as LBYTES.
        { eapply repeatMN_MemPropT_length.
          eapply GEN.
        }

        assert (forall bs, In bs bytes -> length bs = N.to_nat (sizeof_dtyp dt)) as LBS.
        { apply generate_undef_bytes_length in HGEN.
          intros bs IN.
          clear - HGEN GEN IN.
          revert bytes GEN bs IN.
          induction num_elements using N.peano_rect; intros bytes GEN bs IN.
          - cbn in GEN.
            destruct GEN as [MEQ BYTES]; subst.
            inversion IN.
          - rewrite repeatMN_succ in GEN.
            cbn in GEN.
            destruct GEN as [ms''' [l' [[MEQ LEQ] GEN]]]; subst.
            destruct GEN as [ms''' [l' [GEN [MEQ LEQ]]]]; subst.
            destruct IN as [IN | IN]; subst; eauto; lia.
        }

        assert (length (concat bytes) = N.to_nat (sizeof_dtyp dt * num_elements)%N) as LCONCAT.
        { erewrite concat_length; eauto.
          lia.
        }

        clear - ALLOC NON_VOID GEN LCONCAT.
        Transparent allocate_bytes_spec_MemPropT.
        unfold allocate_bytes_spec_MemPropT in *.
        cbn in *.
        destruct ALLOC as [[] | [ms''' [pr [FRESH_PR [[] | ALLOC]]]]].
        destruct ALLOC as [ms'''' [[ptr ptrs] ALLOC]].
        destruct ALLOC as [[MEQ BLOCK_FREE] [UB | [_ [_ [_ []]]]]]; contradiction.
      }

      { induction num_elements using N.peano_rect.
        + cbn in GEN.
          destruct GEN as [MEQ BYTES]; subst.
          cbn in ALLOC.
          Transparent allocate_bytes_spec_MemPropT.
          unfold allocate_bytes_spec_MemPropT in *.
          cbn in *.
          destruct ALLOC as [[] | [ms'' [pr [FRESH_PR [[] | ALLOC]]]]].
          destruct ALLOC as [ms''' [[ptr ptrs] ALLOC]].
          destruct ALLOC as [[MEQ BLOCK_FREE] [UB | [_ [_ [_ []]]]]]; contradiction.
          Opaque allocate_bytes_spec_MemPropT.
        + rewrite repeatMN_succ in GEN.
          cbn in GEN.
          destruct GEN as [ms''' [a [[] _]]].
      }
    - (* Error *)
      destruct ALLOC as [UB | ALLOC]; try contradiction.
      destruct ALLOC as [ms' [[] [[MS NVOID] [UB | ALLOC]]]]; try contradiction.
      symmetry in MS; subst.
      destruct ALLOC as [ms' [sid [FRESH [GEN | ALLOC]]]].
      { induction num_elements using N.peano_rect; [cbn in *; contradiction|].
        rewrite repeatMN_succ in GEN.
        destruct (generate_undef_bytes dt sid); cbn in *.
        + destruct GEN as [[] | [ms'' [l' [[MEQ LEQ] GEN]]]]; subst.
          destruct GEN as [GEN | [ms'' [l' [GEN []]]]]; eauto.
        + destruct GEN as [[] | [ms'' [l' [[] GEN]]]].
      }

      destruct ALLOC as [ms'' [bytes [GEN ALLOC]]].
      destruct (generate_undef_bytes dt sid) eqn:HGEN; cbn in *.
      { cbn in ALLOC.
        Transparent allocate_bytes_spec_MemPropT.
        unfold allocate_bytes_spec_MemPropT in *.
        cbn in *.
        destruct ALLOC as [[] | [ms''' [pr [FRESH_PR [[] | ALLOC]]]]].
        destruct ALLOC as [ms'''' [[ptr ptrs] ALLOC]].
        destruct ALLOC as [[MEQ BLOCK_FREE] [[] | [_ [_ [_ []]]]]].
        Opaque allocate_bytes_spec_MemPropT.
      }

      { induction num_elements using N.peano_rect.
        + cbn in GEN.
          destruct GEN as [MEQ BYTES]; subst.
          cbn in ALLOC.
          Transparent allocate_bytes_spec_MemPropT.
          unfold allocate_bytes_spec_MemPropT in *.
          cbn in *.
          destruct ALLOC as [[] | [ms'' [pr [FRESH_PR [[] | ALLOC]]]]].
          destruct ALLOC as [ms''' [[ptr ptrs] ALLOC]].
          destruct ALLOC as [[MEQ BLOCK_FREE] [[] | [_ [_ [_ []]]]]].
          Opaque allocate_bytes_spec_MemPropT.
        + rewrite repeatMN_succ in GEN.
          cbn in GEN.
          destruct GEN as [ms''' [a [[] _]]].
      }
    - (* Success *)
      destruct res' as [ms a].
      subst.
      left.
      repeat eexists.
      Transparent allocate_bytes_spec_MemPropT.
  Qed.

End MemoryModelTheory.

Module MemStateInfiniteHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import Util.

  (*
    Things that must succeed:

    - get_consecutive_ptrs: May need something in GepM for this.
    - byte_allocated: for all of the consecutive pointers

   *)

  (* TODO: Move to something like IP_BIG? *)
  Lemma big_intptr_seq_succeeds :
    forall start len,
    exists ips, intptr_seq start len = NoOom ips.
  Proof.
    intros start len.
    unfold intptr_seq.
    induction (Zseq start len).
    - cbn. exists []. reflexivity.
    - rewrite map_monad_unfold.
      cbn.
      break_match.
      2: {
        pose proof (from_Z_safe a) as CONTRA.
        rewrite Heqo in CONTRA.
        contradiction.
      }

      destruct IHl as (ips & IHl).
      exists (i :: ips).
      setoid_rewrite functional_extensionality.
      rewrite IHl.
      reflexivity.
      reflexivity.
  Qed.

  #[global] Instance lift_err_RAISE_ERROR_Proper {A M} `{HM: Monad M} `{RAISE: RAISE_ERROR M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} :
    Proper (eq ==> eq1) (@lift_err_RAISE_ERROR A M HM RAISE).
  Proof.
    unfold Proper, respectful.
    intros x y H; subst.
    reflexivity.
  Defined.

  Lemma get_consecutive_ptrs_succeeds :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len,
    exists ptrs, (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad.
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len.

    Opaque handle_gep_addr.

    unfold get_consecutive_ptrs.
    pose proof big_intptr_seq_succeeds 0 len as (ips & SEQ).
    rewrite SEQ.
    cbn.

    pose proof map_monad_err_succeeds
         (fun ix : intptr =>
            handle_gep_addr (DTYPE_I 8) ptr [LP.Events.DV.DVALUE_IPTR ix])
         ips as HMAPM.

    forward HMAPM.
    { intros a IN.
      destruct (int_to_ptr (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * LP.IP.to_Z a)%Z (address_provenance ptr)) eqn:IX.
      - exists (ret a0).
        apply handle_gep_addr_ix'; cbn; auto.
      - eapply handle_gep_addr_ix'_OOM in IX; auto.
        destruct IX as [msg' IX].
        exists (Oom msg').
        cbn; auto.
    }

    destruct HMAPM as (res & HMAPM).
    destruct (Monads.sequence res) eqn:HSEQUENCE.
    { rename l into ptrs.
      exists ptrs.
      rewrite bind_ret_l.
      rewrite HMAPM.
      cbn.
      rewrite bind_ret_l.
      rewrite HSEQUENCE.
      cbn.
      reflexivity.
    }
    { apply map_monad_OOM_fail in HSEQUENCE as [a [IN EQA]].
      unfold id in EQA. subst.

      pose proof map_monad_err_In _ _ _ _ HMAPM IN as [ix [GEP INix]].
      apply handle_gep_addr_ix_OOM in GEP; auto.
      destruct GEP as [msg' GEP].
      pose proof
        (LP.I2P_BIG.int_to_ptr_safe (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix)
           (address_provenance ptr)) as SAFE.
      rewrite GEP in SAFE.
      contradiction.
    }
  Qed.

End MemStateInfiniteHelpers.

Module Type MemoryModelInfiniteSpec (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Parameter find_free_block_can_always_succeed :
    forall ms (len : nat) (pr : Provenance),
    exists ptr ptrs,
      ret (ptr, ptrs) {{ms}} ∈ {{ms}} find_free_block len pr.

  Parameter allocate_bytes_post_conditions_can_always_be_satisfied :
    forall (ms_init : MemState) bytes pr,
    exists ms_final ptr ptrs,
      (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_init}} find_free_block (length bytes) pr) /\
      allocate_bytes_post_conditions ms_init bytes pr ms_final ptr ptrs.

End MemoryModelInfiniteSpec.

Module MemoryModelInfiniteSpecHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) (MMIS : MemoryModelInfiniteSpec LP MP MMSP MMS).
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import MMIS.

  Lemma allocate_bytes_with_pr_spec_MemPropT_can_always_succeed :
    forall (ms_init : MemState)
      bytes pr,
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_with_pr_spec_MemPropT bytes pr.
  Proof.
    intros ms_init bytes pr.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_post_conditions_can_always_be_satisfied ms_init bytes pr as (ms_final & ptr & ptrs & (_ & BLOCK_FREE) & ALLOC).

    exists ms_final. exists ptr.
    cbn.

    (* Find free block *)
    exists ms_init. exists (ptr, ptrs).
    split; eauto.

    (* Post conditions *)
    exists ms_final. exists (ptr, ptrs).
    split; split; auto.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_can_always_succeed :
    forall (ms_init ms_fresh_pr : MemState)
      bytes
      (pr : Provenance)
      (FRESH_PR : (fresh_provenance ms_init (ret (ms_fresh_pr, pr)))),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_spec_MemPropT bytes.
  Proof.
    intros ms_init ms_fresh_pr bytes pr FRESH_PR.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_with_pr_spec_MemPropT_can_always_succeed ms_fresh_pr bytes pr as (ms_final & ptr & ALLOC).

    exists ms_final. exists ptr.
    exists ms_fresh_pr. exists pr.
    split; auto.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_h_cons :
    forall dt len sid start bytes,
      generate_num_undef_bytes_h (N.succ start) len dt sid = NoOom bytes ->
      generate_num_undef_bytes_h start (N.succ len) dt sid =
        b <- generate_num_undef_bytes_h start 1 dt sid;;
        rest <- generate_num_undef_bytes_h (N.succ start) len dt sid;;
        NoOom (b ++ rest).
  Proof.
    intros dt len sid start bytes NOOM.
    cbn.
    unfold generate_num_undef_bytes_h in *.
    match goal with
    | H: _ |- N.recursion ?a ?f _ _ = _ =>
        pose proof
          (@N.recursion_succ (N -> OOM (list SByte)) eq
             a
             f
          ) as S
    end.
    forward S.
    reflexivity.
    forward S.
    { unfold Proper, respectful.
      intros x y H0 x0 y0 H1; subst.
      reflexivity.
    }

    specialize (S len).
    cbn in *.
    rewrite S.

    break_match; auto.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_h_succeeds :
    forall dt sid start,
    exists bytes : list SByte, generate_num_undef_bytes_h start (sizeof_dtyp dt) dt sid = ret bytes.
  Proof.
    intros dt.
    induction (sizeof_dtyp dt) using N.peano_ind;
      intros sid start.

    - cbn; eexists; auto.
    - specialize (IHn sid (N.succ start)).
      destruct IHn as [bytes IHn].
      pose proof (from_Z_safe (Z.of_N start)).
      break_match_hyp; [|contradiction].

      eexists.
      erewrite generate_num_undef_bytes_h_cons; eauto.
      rewrite IHn.
      cbn.
      reflexivity.
  Qed.


  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_succeeds :
    forall dt sid,
    exists bytes : list SByte, generate_num_undef_bytes (sizeof_dtyp dt) dt sid = ret bytes.
  Proof.
    intros dt sid.
    eapply generate_num_undef_bytes_h_succeeds.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_undef_bytes_succeeds :
    forall dt sid,
    exists bytes, generate_undef_bytes dt sid = ret bytes.
  Proof.
    intros dt sid.
    unfold generate_undef_bytes.
    apply generate_num_undef_bytes_succeeds.
  Qed.

  Lemma repeatMN_MemPropT_length :
    forall {A} n (ma : MemPropT MemState A) ms ms' a,
      repeatMN n ma ms (ret (ms', a)) -> length a = N.to_nat n.
  Proof.
    intros A n.
    induction n using N.peano_rect; intros ma ms ms' a REP.
    - cbn in *.
      destruct REP as [MEQ AEQ]; subst.
      reflexivity.
    - rewrite repeatMN_succ in REP.
      cbn in REP.
      destruct REP as [ms1 [a0 [M [ms2 [a1 [REP [MEQ AEQ]]]]]]]; subst.
      cbn.
      apply IHn in REP.
      lia.
  Qed.

  Lemma allocate_dtyp_spec_can_always_succeed :
    forall (ms_init ms_fresh_sid ms_fresh_pr : MemState) dt num_elements pr sid
      (FRESH_SID : (ret sid {{ms_init}} ∈ {{ms_fresh_sid}} fresh_sid))
      (FRESH_PR : (ret pr {{ms_fresh_sid}} ∈ {{ms_fresh_pr}} fresh_provenance))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_dtyp_spec dt num_elements.
  Proof.
    intros ms_init ms_fresh_sid ms_fresh_pr dt num_elements pr sid FRESH_SID FRESH_PR NON_VOID.

    unfold allocate_dtyp_spec.

    pose proof generate_undef_bytes_succeeds dt sid as (bytes_dt & UNDEF_BYTES).
    pose proof generate_undef_bytes_length dt sid bytes_dt UNDEF_BYTES as BYTES_SIZE.
    assert (exists bytes, repeatMN num_elements (@ret (MemPropT MemState) _ _ bytes_dt) ms_fresh_sid (ret (ms_fresh_sid, bytes))) as (bytes & BYTES).
    { exists (repeatN num_elements bytes_dt).
      induction num_elements using N.peano_rect.
      - cbn; split; auto.
      - rewrite repeatMN_succ.
        cbn.
        repeat eexists.
        + cbn in *; eauto.
        + rewrite repeatN_succ.
          auto.
    }

    assert (length bytes = N.to_nat num_elements) as LBYTES.
    { eapply repeatMN_MemPropT_length with (ma:=ret bytes_dt); eauto.
    }

    assert (forall bs, In bs bytes -> length bs = length bytes_dt) as LBS.
    {
      clear - BYTES_SIZE BYTES.
      revert bytes BYTES.
      induction num_elements using N.peano_rect; intros bytes BYTES bs IN.
      - cbn in *.
        destruct BYTES as [MEQ BYTES]; subst.
        inversion IN.
      - rewrite repeatMN_succ in BYTES.
        cbn in BYTES.
        destruct BYTES as [ms''' [l' [[MEQ LEQ] GEN]]]; subst.
        destruct GEN as [ms''' [l' [GEN [MEQ LEQ]]]]; subst.
        destruct IN as [IN | IN]; subst; eauto.
        eapply IHnum_elements; cbn; eauto.
    }

    assert (length (concat bytes) = N.to_nat (sizeof_dtyp dt * num_elements)%N) as LCONCAT.
    { erewrite concat_length with (len:=length bytes_dt); eauto.
      lia.
    }

    assert ((sizeof_dtyp dt * num_elements)%N = N.of_nat (Datatypes.length (concat bytes))) as SIZE by lia.

    pose proof allocate_bytes_spec_MemPropT_can_always_succeed
         ms_fresh_sid ms_fresh_pr (concat bytes) pr FRESH_PR
      as (ms_final & ptr & ALLOC_SUCCESS).

    exists ms_final, ptr.
    repeat red.
    exists ms_init, tt.
    split.
    { cbn.
      split; eauto.
    }
    exists ms_fresh_sid, sid; split; auto.

    rewrite UNDEF_BYTES.
    Opaque allocate_bytes_spec_MemPropT.
    cbn.
    Transparent allocate_bytes_spec_MemPropT.

    exists ms_fresh_sid, bytes.
    tauto.
  Qed.
End MemoryModelInfiniteSpecHelpers.
