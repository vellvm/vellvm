From Coq Require Import
  ZArith
  String
  Structures.Equalities.

From Mem Require Import
  MemoryModel
  Addresses.MemoryAddress
  Addresses.Provenance
  SByte
  StoreId
  FiniteMaps
  Tactics
  Heaps
  StackFrames
  Utils.

From Coq Require Import
  List.

From ExtLib Require Import
  Structures.Monad.

Import MonadNotation.
Open Scope monad.

Notation err := (sum string).

Module Type ALLOCATABLE_MEMORY_FRESH (ADDR : BASIC_ADDRESS) (SB : SBYTE) (AID : ALLOCATION_ID) :=
  ALLOCATABLE_MEMORY ADDR SB AID <+ CORE_MEMORY_FRESH_STORE_ID ADDR SB <+ CORE_MEMORY_FRESH_AID ADDR SB AID.

Module Type EXEC_ALLOCATABLE_FREE_MEMORY_FRESH (ADDR : BASIC_ADDRESS) (SB : SBYTE) (AID : ALLOCATION_ID) :=
  MEMORY_MODEL_BASE ADDR SB <+ EXEC_MEMORY_FREE_BYTE ADDR SB <+ EXEC_ALLOCATABLE_MEMORY ADDR SB AID <+ CORE_MEMORY_FRESH_STORE_ID ADDR SB <+ CORE_MEMORY_FRESH_AID ADDR SB AID.

Module Type CORRECT_ALLOCATABLE_FREE_MEMORY_FRESH (ADDR : BASIC_ADDRESS) (SB : SBYTE) (AID : ALLOCATION_ID) :=
  MEMORY_MODEL_BASE ADDR SB <+ EXEC_MEMORY_FREE_BYTE ADDR SB <+ CORRECT_ALLOCATABLE_MEMORY ADDR SB AID <+ CORE_MEMORY_FRESH_STORE_ID ADDR SB <+ CORE_MEMORY_FRESH_AID ADDR SB AID <+
       CORRECT_MEMORY_FREE_BYTE_CORE ADDR SB AID <+
       CORRECT_MEMORY_FREE_BYTE_EXTRAS ADDR SB AID.

Module Type FRAME_HEAP_MEMORY_BASE
  (Import ADDR : BASIC_ADDRESS)
  (Import SB : SBYTE)
  (Import H : HEAP ADDR)
  (Import F : FRAME ADDR)
  (Import FS : FRAME_STACK ADDR F)
  (MEM : MEMORY_MODEL_BASE ADDR SB) <: MEMORY_MODEL_BASE ADDR SB.
  Record Memory' :=
    MkMemory {
        memory_byte_map : MEM.Memory;
        memory_frame_stack : FrameStack;
        memory_heap : Heap;
      }.

  Definition Memory := Memory'.

  Definition initial_memory
    := MkMemory MEM.initial_memory initial_frame_stack empty_heap.

  Definition sub_memory (m : Memory) : MEM.Memory :=
    memory_byte_map m.

  (** STACK *)
  Definition Memory_frame_stack := memory_frame_stack.
  Definition Memory_frame_stack_modify (m : Memory) (f : FrameStack -> FrameStack) : Memory :=
    match m with
    | MkMemory bm fs h =>
        MkMemory bm (f fs) h
    end.

  Lemma Memory_frame_stack_modify_spec :
    forall (m1 : Memory) (f : FrameStack -> FrameStack),
      Memory_frame_stack (Memory_frame_stack_modify m1 f) = f (Memory_frame_stack m1).
  Proof.
    intros m1 f.
    destruct m1; cbn; reflexivity.
  Qed.

  Include (MEMORY_FRAME_STACK_EXTRAS ADDR SB F FS).

  (** HEAP *)
  Definition Memory_heap := memory_heap.
  Definition Memory_heap_modify (m : Memory) (f : Heap -> Heap) : Memory :=
    match m with
    | MkMemory bm fs h =>
        MkMemory bm fs (f h)
    end.

  Lemma Memory_heap_modify_spec :
    forall (m1 m2 : Memory) (f : Heap -> Heap),
      m2 = Memory_heap_modify m1 f ->
      Memory_heap m2 = f (Memory_heap m1).
  Proof.
    intros m1 m2 f H.
    subst.
    destruct m1; cbn; reflexivity.
  Qed.

  Lemma Memory_heap_modify_id :
    forall m,
      Memory_heap_modify m id = m.
  Proof.
    intros m.
    destruct m; cbn; auto.
  Qed.

  Definition ptr_in_memory_heap (m : Memory) (root ptr : addr) : bool :=
    ptr_in_heap (Memory_heap m) root ptr.

  Definition root_ptr_in_memory_heap (m : Memory) (root : addr) : bool :=
    root_ptr_in_heap (Memory_heap m) root.
End FRAME_HEAP_MEMORY_BASE.

(** Add a heap and stack to allocatable memory *)
Module ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL'
  (Import ADDR : BASIC_ADDRESS)
  (Import SB : SBYTE)
  (Import AID: ALLOCATION_ID)
  (Import H : HEAP ADDR)
  (Import F : FRAME ADDR)
  (Import FS : FRAME_STACK ADDR F)
  (MEM : ALLOCATABLE_MEMORY_FRESH ADDR SB AID)
  (Import FH_MEM : FRAME_HEAP_MEMORY_BASE ADDR SB H F FS MEM) <: FULL_MEMORY_MODEL' ADDR SB AID H F FS FH_MEM FH_MEM FH_MEM.

  (*** MEMORY_ALLOCATED_CORE *)
  (** Whether an address is allocated with a given AllocationId *)
  Definition addr_allocated (m : Memory) (ptr : addr) (aid : AllocationId) : Prop :=
    MEM.addr_allocated (memory_byte_map m) ptr aid.

  Definition addr_not_allocated (m : Memory) (ptr : addr) :=
    forall aid, ~ addr_allocated m ptr aid.

  (*** READABLE_MEMORY *)
  Definition read_byte_allowed (m : Memory) (ptr : addr) : Prop :=
    MEM.read_byte_allowed (memory_byte_map m) ptr.

  Definition read_byte (m : Memory) (ptr : addr) (b : SByte) : Prop :=
    MEM.read_byte (memory_byte_map m) ptr b.

  Lemma read_byte_allowed_spec :
    forall (m : Memory) (ptr : addr),
      ~ read_byte_allowed m ptr ->
      forall b, ~ read_byte m ptr b.
  Proof.
    intros m ptr NRBA b RB.
    unfold read_byte, read_byte_allowed in *.
    eapply MEM.read_byte_allowed_spec; eauto.
  Qed.

  (*** WRITEABLE_MEMORY *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  Definition write_byte_allowed (m : Memory) (ptr : addr) : Prop :=
    MEM.write_byte_allowed (memory_byte_map m) ptr.

  Definition write_byte (m1 : Memory) (ptr : addr) (b : SByte) (m2 : Memory) : Prop :=
    match m1 with
    | (MkMemory bm1 fs h) =>
        exists bm2,
        m2 = MkMemory bm2 fs h /\ MEM.write_byte bm1 ptr b bm2
    end.

  (** We can look up a new value after writing it to memory *)
  Lemma write_byte_new_lu :
    forall (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory),
      write_byte m1 ptr byte m2 ->
      read_byte m2 ptr byte.
  Proof.
    intros m1 ptr byte m2 WB.
    red in WB; red.
    break_match_hyp; subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_new_lu; eauto.
  Qed.

  (** We can look up old values after writing to a disjoint location in memory *)
  Lemma write_byte_old_lu :
    forall (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory),
      write_byte m1 ptr byte m2 ->
      forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        (forall byte', read_byte m1 ptr' byte' <-> read_byte m2 ptr' byte').
  Proof.
    intros m1 ptr byte m2 WB ptr' DISJOINT byte'.
    unfold read_byte, write_byte in *.
    repeat (break_match_hyp; try contradiction); subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_old_lu; eauto.
  Qed.

  Lemma write_byte_allowed_spec :
    forall (m : Memory) (ptr : addr),
      ~ write_byte_allowed m ptr ->
      forall b m2, ~ write_byte m ptr b m2.
  Proof.
    intros m ptr NWBA b m2 WB.
    unfold write_byte, write_byte_allowed in *.
    repeat (break_match_hyp; try contradiction); subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_allowed_spec; eauto.
  Qed.

  Definition read_byte_allowed_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr,
      read_byte_allowed m1 ptr <-> read_byte_allowed m2 ptr.

  Lemma write_byte_preserves_read_byte_allowed :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      read_byte_allowed_preserved m1 m2.
  Proof.
    intros m1 ptr b m2 WB.
    unfold write_byte, read_byte_allowed_preserved, read_byte_allowed in *.
    repeat (break_match_hyp; try contradiction); subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_preserves_read_byte_allowed; eauto.
  Qed.

  Definition write_byte_allowed_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr,
      write_byte_allowed m1 ptr <-> write_byte_allowed m2 ptr.

  Lemma write_byte_preserves_write_byte_allowed :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      write_byte_allowed_preserved m1 m2.
  Proof.
    intros m1 ptr b m2 WB.
    unfold write_byte, read_byte_allowed_preserved, read_byte_allowed in *.
    repeat (break_match_hyp; try contradiction); subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_preserves_write_byte_allowed; eauto.
  Qed.

  Lemma read_byte_allocated_spec :
    forall (m : Memory) (ptr : addr),
      addr_not_allocated m ptr ->
      forall b, ~ read_byte m ptr b.
  Proof.
    intros m ptr NALLOC b READ.
    red in NALLOC, READ.
    eapply MEM.read_byte_allocated_spec; eauto.
  Qed.

  Definition all_allocated_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr aid,
      addr_allocated m1 ptr aid <-> addr_allocated m2 ptr aid.

  Definition all_not_allocated_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr,
      addr_not_allocated m1 ptr <-> addr_not_allocated m2 ptr.

  Lemma write_byte_preserves_allocated :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      all_allocated_preserved m1 m2.
  Proof.
    intros m1 ptr b m2 WB.
    unfold write_byte, read_byte_allowed_preserved, read_byte_allowed in *.
    repeat (break_match_hyp; try contradiction); subst.
    destruct WB as (?&?&?); subst.
    eapply MEM.write_byte_preserves_allocated; eauto.
  Qed.

  (** FIND_FREE *)
  Record find_free_block' (m : Memory) (len : nat) (ptrs : (addr * list addr)) : Prop :=
    { (* Minimal *)
      find_free_block_is_free : Forall (addr_not_allocated m) (snd ptrs)
    ; find_free_block_length : length (snd ptrs) = len
    ; find_free_block_consecutive : consecutive_ptrs (snd ptrs) = true
    ; find_free_block_head : forall ptr' ptrs', snd ptrs = (ptr' :: ptrs') -> fst ptrs = ptr'
    ; find_free_non_null : Forall (fun ptr => is_null ptr = false) (snd ptrs)
    ; find_free_non_null' : is_null (fst ptrs) = false
    }.

  (* Make module types happy :| *)
  Definition find_free_block := find_free_block'.

  (** MEMORY_ALLOCATE *)
  (* Include (MEMORY_ALLOCATE_SPEC_IMPL ADDR SB AID). *) (* Need some extras :) *)
  Record allocate_block' (m1 : Memory) (bytes : list SByte) (aid : AllocationId) (m2 : Memory) (ptrs : (addr * list addr)) : Prop :=
    {
      allocate_block_free :
      find_free_block m1 (length bytes) ptrs

    ; allocate_block_new_reads :
      Forall2 (fun b ptr => read_byte m2 ptr b) bytes (snd ptrs)

    ; allocate_block_old_reads :
      forall b ptr, read_byte m1 ptr b -> read_byte m2 ptr b

    ; allocate_block_allocated :
      Forall (fun ptr => addr_allocated m2 ptr aid) (snd ptrs)

    ; allocate_block_old_allocated :
      forall ptr, addr_allocated m1 ptr aid -> addr_allocated m2 ptr aid

    ; allocate_block_non_null :
      Forall (fun ptr => is_null ptr = false) (snd ptrs)

    (* Extras *)
    ; allocate_block_preserves_heap : Memory_heap m1 = Memory_heap m2
    ; allocate_block_preserves_stack : Memory_frame_stack m1 = Memory_frame_stack m2
    }.

  Definition allocate_block := allocate_block'.

  (** Stack allocations *)
  (* It's a little unclear if OOM or err should take precedence... Currently OOM takes precedence. *)
  Definition stack_allocate_block
    (m : Memory) (bytes : list SByte) (aid : AllocationId) (res : err (Memory * (addr * list addr))) : Prop :=
    exists m' ptrs,
      allocate_block m bytes aid m' ptrs /\
        match add_all_to_current_frame (Memory_frame_stack m') (map ptr_to_int (snd ptrs)) with
        | None => res = inl "stack_allocate_block: No stack frame"%string
        | Some fs =>
            res = inr (Memory_frame_stack_modify m' (fun _ => fs), ptrs)
        end.

  Lemma stack_allocate_block_free :
    forall m1 bytes aid m2 ptrs,
      stack_allocate_block m1 bytes aid (inr (m2, ptrs)) ->
      find_free_block m1 (length bytes) ptrs.
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    break_match_hyp_inv.
    eapply allocate_block_free; eauto.
  Qed.

  Lemma stack_allocate_block_non_null :
    forall m1 bytes aid m2 ptrs,
      stack_allocate_block m1 bytes aid (inr (m2, ptrs)) ->
      Forall (fun ptr => is_null ptr = false) (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs ALLOC.
    red in ALLOC.
    destruct ALLOC as (?&?&ALLOC&?).
    break_match_hyp_inv.
    eapply allocate_block_non_null; eauto.
  Qed.

  (* TODO: Make lemma in framestack module? *)
  Lemma read_byte_frame_ambivalent :
    forall m ptr b fs,
      read_byte m ptr b <-> read_byte (Memory_frame_stack_modify m fs) ptr b.
  Proof.
    intros m ptr b fs.
    unfold read_byte.
    unfold Memory_frame_stack_modify.
    destruct m; cbn.
    reflexivity.
  Qed.

  (* TODO: Make lemma in framestack module? *)
  Lemma addr_allocated_frame_ambivalent :
    forall m ptr aid fs,
      addr_allocated m ptr aid <-> addr_allocated (Memory_frame_stack_modify m fs) ptr aid.
  Proof.
    intros m ptr b fs.
    unfold read_byte.
    unfold Memory_frame_stack_modify.
    destruct m; cbn.
    reflexivity.
  Qed.

  Lemma stack_allocate_block_new_reads :
    forall m1 bytes aid m2 ptrs,
      stack_allocate_block m1 bytes aid (inr (m2, ptrs)) ->
      Forall2 (fun b ptr => read_byte m2 ptr b) bytes (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    break_match_hyp_inv.
    eapply Forall2_impl with (R1:= fun b ptr => read_byte m' ptr b).
    intros a b H.
    apply read_byte_frame_ambivalent; auto.
    eapply allocate_block_new_reads; eauto.
  Qed.

  Lemma stack_allocate_block_old_reads :
    forall m1 bytes aid m2 ptrs,
      stack_allocate_block m1 bytes aid (inr (m2, ptrs)) ->
      forall b ptr, read_byte m1 ptr b -> read_byte m2 ptr b.
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    break_match_hyp_inv.
    intros b ptr READ.
    apply read_byte_frame_ambivalent; auto.
    eapply allocate_block_old_reads; eauto.
  Qed.

  Lemma stack_allocate_block_allocated :
    forall m1 bytes aid m2 ptrs,
      stack_allocate_block m1 bytes aid (inr (m2, ptrs)) ->
      Forall (fun ptr => addr_allocated m2 ptr aid) (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    break_match_hyp_inv.
    eapply Forall_impl with (P:=fun ptr => addr_allocated m' ptr aid).
    - intros a H.
      apply addr_allocated_frame_ambivalent; auto.
    - eapply allocate_block_allocated; eauto.
  Qed.

  Record stack_pop' (m1 m2 : Memory) : Prop :=
    { (* Minimal *)
      stack_pop_pop_frame :
      exists f',
        peek (Memory_frame_stack m1) = Some f' /\
          pop (Memory_frame_stack m1) = Some (f', Memory_frame_stack m2)
    ; stack_pop_bytes_freed :
      forall ptr,
        ptr_in_current_frame m1 ptr = true ->
        addr_not_allocated m2 ptr
    ; stack_pop_non_frame_allocations :
      forall ptr aid,
        ptr_in_current_frame m1 ptr = false ->
        addr_allocated m1 ptr aid <-> addr_allocated m2 ptr aid
    ; stack_pop_non_frame_bytes_read :
      forall ptr byte,
        ptr_in_current_frame m1 ptr = false ->
        read_byte m1 ptr byte <-> read_byte m2 ptr byte
    }.

  Definition stack_pop := stack_pop'.

  (** Heap allocations *)
  Definition heap_allocate_block
    (m : Memory) (bytes : list SByte) (aid : AllocationId) (res : Memory * (addr * list addr)) : Prop :=
    exists m' ptrs,
      allocate_block m bytes aid m' ptrs /\
        res = (Memory_heap_modify m' (fun h => add_ptrs_to_heap h (snd ptrs)), ptrs).

  Lemma heap_allocate_block_free :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      find_free_block m1 (length bytes) ptrs.
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    inv ADD.
    eapply allocate_block_free; eauto.
  Qed.

  Lemma heap_allocate_block_non_null :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      Forall (fun p => is_null p = false) (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & ADD).
    inv ADD.
    eapply allocate_block_non_null; eauto.
  Qed.

  Include (ALL_READS_PRESERVED ADDR SB FH_MEM).

  Lemma Memory_heap_modify_reads_preserved :
    forall m f,
      read_bytes_preserved m (Memory_heap_modify m f).
  Proof.
    intros m f.
    split; intros READ.
    - destruct m; cbn in *.
      unfold read_byte in *.
      cbn in *; auto.
    - destruct m; cbn in *.
      unfold read_byte in *.
      cbn in *; auto.
  Qed.

  Lemma Memory_heap_modify_all_allocated_preserved :
    forall m f,
      all_allocated_preserved m (Memory_heap_modify m f).
  Proof.
    intros m f.
    split; intros ALLOC.
    - destruct m; cbn in *.
      unfold addr_allocated in *.
      cbn in *; auto.
    - destruct m; cbn in *.
      unfold addr_allocated in *.
      cbn in *; auto.
  Qed.

  Lemma heap_allocate_block_new_reads :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      Forall2 (fun b ptr => read_byte m2 ptr b) bytes (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & HEAP).
    inv HEAP.
    apply allocate_block_new_reads in ALLOC.
    apply Forall2_forall; apply Forall2_forall in ALLOC as (LEN & ALLOC).
    split; auto.
    intros i a b NA NB.
    apply Memory_heap_modify_reads_preserved; eauto.
  Qed.

  Lemma heap_allocate_block_old_reads :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      forall b ptr, read_byte m1 ptr b -> read_byte m2 ptr b.
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & HEAP).
    inv HEAP.
    intros b ptr READ.
    apply Memory_heap_modify_reads_preserved; eauto.
    eapply allocate_block_old_reads; eauto.
  Qed.

  Lemma heap_allocate_block_allocated :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      Forall (fun ptr => addr_allocated m2 ptr aid) (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & HEAP).
    inv HEAP.
    apply Forall_forall.
    intros x IN.
    apply Memory_heap_modify_all_allocated_preserved.
    eapply allocate_block_allocated in ALLOC.
    eapply Forall_forall in ALLOC; eauto.
  Qed.

  Lemma heap_allocate_block_new_heap :
    forall m1 bytes aid m2 ptrs,
      heap_allocate_block m1 bytes aid (m2, ptrs) ->
      Memory_heap m2 = add_ptrs_to_heap (Memory_heap m1) (snd ptrs).
  Proof.
    intros m1 bytes aid m2 ptrs (m' & ptrs' & ALLOC & HEAP).
    inv HEAP.
    apply allocate_block_preserves_heap in ALLOC.
    rewrite ALLOC.
    erewrite Memory_heap_modify_spec; eauto; cbn; eauto.
  Qed.

  (** Heap free *)
  Record free_preconditions (m1 : Memory) (root : addr) : Prop :=
    { (* ptr being freed was a root *)
      free_was_root :
      root_ptr_in_memory_heap m1 root = true;

      (* root being freed was allocated *)
      free_was_allocated :
      exists aid, addr_allocated m1 root aid;

      (* ptrs in block were allocated *)
      free_block_allocated :
      forall ptr,
        ptr_in_memory_heap m1 root ptr = true ->
        exists aid, addr_allocated m1 ptr aid;

      (* root is allowed to be freed *)
      (* TODO: add this back. #312 / #313 *)
      (* Running into problems with exec_correct_free because of the
         implementation with size 0 allocations / frees *)
      (* free_root_allowed :
         free_byte_allowed m1 root; *)
    }.

  Record free_block_prop (h1 : Heap) (root : addr) (h2 : Heap) : Prop :=
    { free_block_ptrs_freed :
      forall ptr,
        ptr_in_heap h1 root ptr = true ->
        ptr_in_heap h2 root ptr = false;

      free_block_root_freed :
      root_ptr_in_heap h2 root = false;

      (* TODO: make sure there's no weirdness about multiple roots *)
      free_block_disjoint_preserved :
      forall ptr root',
        disjoint_ptr_byte root root' ->
        ptr_in_heap h1 root' ptr = ptr_in_heap h2 root' ptr;

      free_block_disjoint_roots :
      forall root',
        disjoint_ptr_byte root root' ->
        root_ptr_in_heap h1 root' = root_ptr_in_heap h2 root';
    }.

  Record free_spec (m1 : Memory) (root : addr) (m2 : Memory) : Prop :=
    { (* all bytes in block are freed. *)
      free_spec_bytes_freed :
      forall ptr,
        ptr_in_memory_heap m1 root ptr = true ->
        addr_not_allocated m2 ptr;

      (* Bytes not allocated in the block have the same allocation status as before *)
      free_spec_non_block_bytes_preserved :
      forall ptr aid,
        ptr_in_memory_heap m1 root ptr = false ->
        addr_allocated m1 ptr aid <-> addr_allocated m2 ptr aid;

      (* Bytes not allocated in the freed block are the same when read *)
      free_spec_non_frame_bytes_read :
      forall ptr byte,
        ptr_in_memory_heap m1 root ptr = false ->
        read_byte m1 ptr byte <-> read_byte m2 ptr byte;

      (* Set new heap *)
      free_spec_block :
        free_block_prop (Memory_heap m1) root (Memory_heap m2);
    }.

  Definition heap_free (m1 : Memory) (root : addr) (m2 : Memory) : Prop
    := free_preconditions m1 root /\ free_spec m1 root m2.

  (** If the free proconditions aren't met then heap_free can't proceed *)
  Lemma heap_free_no_preconditions_ub :
    forall (m1 : Memory) (root : addr) (m2 : Memory),
      ~ free_preconditions m1 root ->
      ~ heap_free m1 root m2.
  Proof.
    intros m1 root m2 PRE FREE.
    apply PRE.
    apply FREE.
  Qed.

  (** all bytes in block are freed. *)
  Lemma free_bytes_freed :
    forall (m1 : Memory) (root : addr) (m2 : Memory),
      heap_free m1 root m2 ->
      forall ptr,
        ptr_in_memory_heap m1 root ptr = true ->
        addr_not_allocated m2 ptr.
  Proof.
    intros m1 root m2 FREE ptr IN_HEAP.
    eapply free_spec_bytes_freed.
    apply FREE.
    apply IN_HEAP.
  Qed.

  (** Bytes not allocated in the block have the same allocation status as before *)
  Lemma free_non_block_bytes_preserved :
    forall (m1 : Memory) (root : addr) (m2 : Memory),
      heap_free m1 root m2 ->
      forall ptr aid,
        ptr_in_memory_heap m1 root ptr = false ->
        addr_allocated m1 ptr aid <-> addr_allocated m2 ptr aid.
  Proof.
    intros m1 root m2 FREE ptr aid IN_HEAP.
    eapply free_spec_non_block_bytes_preserved.
    apply FREE; auto.
    auto.
  Qed.

  (** Bytes not allocated in the freed block are the same when read *)
  Lemma free_non_frame_bytes_read :
    forall (m1 : Memory) (root : addr) (m2 : Memory),
      heap_free m1 root m2 ->
      forall ptr byte,
        ptr_in_memory_heap m1 root ptr = false ->
        read_byte m1 ptr byte <-> read_byte m2 ptr byte.
  Proof.
    intros m1 root m2 FREE ptr byte IN_HEAP.
    eapply free_spec_non_frame_bytes_read.
    apply FREE; auto.
    auto.
  Qed.

  (** Set new heap *)
  Lemma free_block :
    forall (m1 : Memory) (root : addr) (m2 : Memory),
      heap_free m1 root m2 ->
      free_block_prop (Memory_heap m1) root (Memory_heap m2).
  Proof.
    intros m1 root m2 FREE.
    eapply free_spec_block.
    apply FREE.
  Qed.


  Definition Memory_aid_counter : Memory -> AllocationId := MEM.Memory_aid_counter ∘ sub_memory.
  Definition Memory_aid_modify (m : Memory) (f : AllocationId -> AllocationId) : Memory :=
    match m with
    | (MkMemory bm fs h) =>
        MkMemory (MEM.Memory_aid_modify bm f) fs h
    end.

  Lemma Memory_aid_modify_spec :
    forall (m1 m2 : Memory) (f : AllocationId -> AllocationId) (aid1 aid2 : AllocationId),
      aid1 = Memory_aid_counter m1 ->
      m2 = Memory_aid_modify m1 f ->
      aid2 = Memory_aid_counter m2 ->
      aid2 = f aid1.
  Proof.
    intros m1 m2 f aid1 aid2 H H0 H1.
    subst.
    unfold Memory_aid_counter, Memory_aid_modify.
    destruct m1; cbn.
    unfold Basics.compose.
    cbn.
    eapply MEM.Memory_aid_modify_spec; eauto.
  Qed.

  Definition Memory_fresh_aid (m : Memory) : (AllocationId * Memory)%type
    := let aid := Memory_aid_counter m in
       let aid' := next_aid aid in
       (aid', Memory_aid_modify m (fun _ => aid')).

  Definition Memory_sid_counter : Memory -> store_id := MEM.Memory_sid_counter ∘ sub_memory.
  Definition Memory_sid_modify (m : Memory) (f : store_id -> store_id) : Memory :=
    match m with
    | (MkMemory bm fs h) =>
        MkMemory (MEM.Memory_sid_modify bm f) fs h
    end.

  Lemma Memory_sid_modify_spec :
    forall (m1 m2 : Memory) (f : store_id -> store_id) (sid1 sid2 : store_id),
      sid1 = Memory_sid_counter m1 ->
      m2 = Memory_sid_modify m1 f ->
      sid2 = Memory_sid_counter m2 ->
      sid2 = f sid1.
  Proof.
    intros m1 m2 f sid1 sid2 H H0 H1.
    subst.
    unfold Memory_sid_counter, Memory_sid_modify.
    destruct m1; cbn.
    unfold Basics.compose.
    cbn.
    eapply MEM.Memory_sid_modify_spec; eauto.
  Qed.

  Definition Memory_fresh_sid (m : Memory) : (store_id * Memory)%type
    := let sid := Memory_sid_counter m in
       let sid' := N.succ sid in
       (sid', Memory_sid_modify m (fun _ => sid')).

End ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL'.

Module ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL
   (ADDR : BASIC_ADDRESS)
   (SB : SBYTE)
   (AID : ALLOCATION_ID)
   (H : HEAP ADDR)
   (F : FRAME ADDR)
   (FS : FRAME_STACK ADDR F)
   (MEM : ALLOCATABLE_MEMORY_FRESH ADDR SB AID)  <: FULL_MEMORY_MODEL ADDR SB AID H F FS
  :=
  FRAME_HEAP_MEMORY_BASE ADDR SB H F FS MEM <+
    ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL' ADDR SB AID H F FS MEM.

(** Add a heap and stack to allocatable memory *)
Module EXEC_ALLOCATABLE_MEMORY_FRESH_TO_FULL_EXEC_MEMORY_MODEL'
  (Import ADDR : BASIC_ADDRESS)
  (Import SB : SBYTE)
  (Import AID: ALLOCATION_ID)
  (Import H : HEAP ADDR)
  (Import F : FRAME ADDR)
  (Import FS : FRAME_STACK ADDR F)
  (MEM : EXEC_ALLOCATABLE_FREE_MEMORY_FRESH ADDR SB AID)
  (Import FH_MEM : FRAME_HEAP_MEMORY_BASE ADDR SB H F FS MEM) <: FULL_EXEC_MEMORY_MODEL' ADDR SB AID H F FS FH_MEM FH_MEM FH_MEM.
  (*** READABLE_MEMORY *)
  Definition read_byte_exec (m : Memory) (ptr : addr) : err SByte :=
    MEM.read_byte_exec (memory_byte_map m) ptr.

  (*** WRITEABLE_MEMORY *)
  Definition write_byte_exec (m1 : Memory) (ptr : addr) (b : SByte) : err Memory :=
    match m1 with
    | (MkMemory bm1 fs h) =>
        bm2 <- MEM.write_byte_exec bm1 ptr b;;
        ret (MkMemory bm2 fs h)
    end.

  (** MEMORY_ALLOCATE *)
  Definition allocate_block_exec (m1 : Memory) (bytes : list SByte) (aid : AllocationId) : Error.OOM (Memory * (addr * list addr))
    :=
    match m1 with
    | (MkMemory bm1 fs h) =>
       '(bm2, ptrs) <- MEM.allocate_block_exec bm1 bytes aid;;
        ret (MkMemory bm2 fs h, ptrs)
    end.

  Definition free_byte_exec (m1 : Memory) (addr : Z) : Memory
    :=
    match m1 with
    | (MkMemory bm1 fs h) =>
        MkMemory (MEM.free_byte_exec bm1 addr) fs h
    end.

  Definition free_bytes_exec (m : Memory) (ptrs : list Z) : Memory
    := fold_left (fun m' ptr => free_byte_exec m' ptr) ptrs m.

  (** Stack allocations *)
  Include (EXEC_MEMORY_STACK_ALLOCATE ADDR SB AID F FS FH_MEM FH_MEM).
  Include (EXEC_MEMORY_STACK_POP_BASE ADDR SB F FS FH_MEM FH_MEM).

  (** Heap allocations *)
  Include (EXEC_MEMORY_HEAP_ALLOCATE ADDR SB AID H FH_MEM FH_MEM).
  Include (EXEC_MEMORY_HEAP_FREE ADDR SB H FH_MEM FH_MEM).
End EXEC_ALLOCATABLE_MEMORY_FRESH_TO_FULL_EXEC_MEMORY_MODEL'.

Module CORRECT_ALLOCATABLE_MEMORY_FRESH_TO_FULL_CORRECT_MEMORY_MODEL'
  (Import ADDR : BASIC_ADDRESS)
  (Import SB : SBYTE)
  (Import AID: ALLOCATION_ID)
  (Import H : HEAP ADDR)
  (Import F : FRAME ADDR)
  (Import FS : FRAME_STACK ADDR F)
  (MEM : CORRECT_ALLOCATABLE_FREE_MEMORY_FRESH ADDR SB AID)
  (Import FH_MEM : FRAME_HEAP_MEMORY_BASE ADDR SB H F FS MEM) <: FULL_CORRECT_MEMORY_MODEL' ADDR SB AID H F FS FH_MEM FH_MEM FH_MEM.

  (*** Spec *)
  Include (ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL' ADDR SB AID H F FS MEM FH_MEM).

  (*** Exec *)
  Include (EXEC_ALLOCATABLE_MEMORY_FRESH_TO_FULL_EXEC_MEMORY_MODEL' ADDR SB AID H F FS MEM FH_MEM).

  Hint Resolve
    MEM.allocate_block_free
    MEM.allocate_block_old_allocated
    MEM.allocate_block_old_reads
    MEM.allocate_block_allocated
    MEM.allocate_block_new_reads
    MEM.allocate_block_correct
    MEM.find_free_block_is_free
    MEM.find_free_block_length
    MEM.find_free_non_null'
    MEM.find_free_block_consecutive
    MEM.find_free_non_null
    MEM.find_free_block_head
    MEM.read_byte_correct
    MEM.read_byte_correct_err
    MEM.write_byte_correct
    MEM.write_byte_correct_err
    : BASE_MEM.

  Hint Unfold
    read_byte_exec
    write_byte_exec
    read_byte
    write_byte
    free_byte_exec
    allocate_block_exec
    : BASE_MEM.

  (*** Correctness Proofs *)
  Lemma read_byte_correct :
    forall (m : Memory) (ptr : addr)
      (sb : SByte),
      read_byte_exec m ptr = inr sb -> read_byte m ptr sb.
  Proof.
    intros * READ.
    eapply MEM.read_byte_correct; eauto.
  Qed.

  Lemma read_byte_correct_err :
    forall (m : Memory) (ptr : addr)
      (sb : SByte) (str : string),
      read_byte_exec m ptr = inl str -> ~ read_byte m ptr sb.
  Proof.
    intros * READ.
    eapply MEM.read_byte_correct_err; eauto.
  Qed.

  Lemma write_byte_correct :
    forall (m1 : Memory) (ptr : addr)
      (b : SByte) (m2 : Memory),
      write_byte_exec m1 ptr b = inr m2 ->
      write_byte m1 ptr b m2.
  Proof.
    intros * WRITE.
    destruct m1; cbn in *.
    break_match_hyp_inv.
    eexists; split;
      [ auto
      | eapply MEM.write_byte_correct; eauto
      ].
  Qed.

  Lemma write_byte_correct_err :
    forall (m1 : Memory) (ptr : addr)
      (b : SByte) (m2 : Memory)
      (str : string),
      write_byte_exec m1 ptr b = inl str ->
      ~ write_byte m1 ptr b m2.
  Proof.
    intros * WRITE.
    destruct m1; cbn in *.
    break_match_hyp_inv.
    intros (?&?&?); subst.
    eapply MEM.write_byte_correct_err in Heqs; eauto.
  Qed.

  Lemma allocate_block_correct :
    forall (m1 : Memory) (bytes : list SByte)
      (aid : AllocationId) (m2 : Memory)
      (ptrs : addr * list addr),
      allocate_block_exec m1 bytes aid =
        Error.NoOom (m2, ptrs) ->
      allocate_block m1 bytes aid m2 ptrs.
  Proof.
    intros * ALLOC.
    destruct m1; cbn in *.
    break_match_hyp_inv.
    destruct p; inv H0.
    eapply MEM.allocate_block_correct in Heqo.
    split; cbn; eauto with BASE_MEM.
    - eapply MEM.allocate_block_free in Heqo; eauto with BASE_MEM.
      split; cbn; eauto with BASE_MEM.
      eapply MEM.find_free_block_is_free; eauto.
    - eapply MEM.allocate_block_new_reads; eauto.
    - eapply MEM.allocate_block_allocated; eauto.
    - eapply MEM.allocate_block_old_allocated; eauto.
  Qed.

  Lemma free_byte_frees :
    forall (m1 : Memory) (ptr : addr) (m2 : Memory),
      free_byte_exec m1 (ptr_to_int ptr) = m2 ->
      addr_not_allocated m2 ptr.
  Proof.
    intros * FREE.
    autounfold with BASE_MEM in *.
    break_match_hyp_inv.
    eapply MEM.free_byte_frees; cbn in *; eauto with BASE_MEM.
  Qed.

  Lemma free_byte_other_allocations :
    forall m1 ptr m2,
      free_byte_exec m1 ptr = m2 ->
      forall p' aid,
        ptr_to_int p' <> ptr ->
        addr_allocated m1 p' aid <-> addr_allocated m2 p' aid.
  Proof.
    intros * FREE p' aid DISJOINT.
    autounfold with BASE_MEM in *.
    break_match_hyp_inv.
    eapply MEM.free_byte_other_allocations; cbn; eauto with BASE_MEM.
  Qed.

  Lemma free_byte_other_reads :
    forall m1 ptr m2,
      free_byte_exec m1 ptr = m2 ->
      forall p' byte,
        ptr_to_int p' <> ptr ->
        read_byte m1 p' byte <-> read_byte m2 p' byte.
  Proof.
    intros * FREE p' aid DISJOINT.
    autounfold with BASE_MEM in *.
    break_match_hyp_inv.
    eapply MEM.free_byte_other_reads; cbn; eauto with BASE_MEM.
  Qed.

  Lemma free_byte_comm :
    forall m1 ptr1 ptr2,
      free_byte_exec (free_byte_exec m1 ptr1) ptr2 = free_byte_exec (free_byte_exec m1 ptr2) ptr1.
  Proof.
    intros m1 ptr1 ptr2.
    unfold free_byte_exec in *.
    destruct m1.
    rewrite MEM.free_byte_comm.
    reflexivity.
  Qed.

  Include (CORRECT_MEMORY_FREE_BYTE_EXTRAS ADDR SB AID FH_MEM).

  Lemma free_byte_exec_sub_mem :
    forall bm fs h ptr,
      free_byte_exec (MkMemory bm fs h) ptr = MkMemory (MEM.free_byte_exec bm ptr) fs h.
  Proof.
    auto.
  Qed.

  Lemma free_bytes_exec_sub_mem :
    forall ptrs bm fs h,
      free_bytes_exec (MkMemory bm fs h) ptrs = MkMemory (MEM.free_bytes_exec bm ptrs) fs h.
  Proof.
    induction ptrs;
      intros *; auto.

    rewrite free_bytes_exec_cons'.
    setoid_rewrite <- IHptrs.
    reflexivity.
  Qed.

  Lemma stack_allocate_block_succeeds_correct :
    forall (m m' : Memory)
      (ptrs : addr * list addr)
      (bytes : list SByte)
      (aid : AllocationId),
      stack_allocate_block_exec m bytes aid =
        inr (Error.NoOom (m', ptrs)) ->
      stack_allocate_block m bytes aid (inr (m', ptrs)).
  Proof.
    intros * STACK.
    autounfold with BASE_MEM in *.
    unfold stack_allocate_block_exec in *.
    repeat break_match_hyp_inv.
    red.
    exists m0, ptrs.
    split.
    - apply allocate_block_correct; eauto.
    - rewrite Heqo0.
      reflexivity.
  Qed.

  Lemma stack_allocate_block_err_correct :
    forall (m : Memory) (s : string)
      (bytes : list SByte)
      (aid : AllocationId),
      stack_allocate_block_exec m bytes aid = inl s ->
      stack_allocate_block m bytes aid (inl s).
  Proof.
    intros * STACK.
    autounfold with BASE_MEM in *.
    unfold stack_allocate_block_exec in *.
    repeat break_match_hyp_inv.
    red.
    exists m0, p0.
    split.
    - apply allocate_block_correct; eauto.
    - rewrite Heqo0.
      reflexivity.
  Qed.

  Lemma stack_pop_correct :
    forall m1 m2 : Memory,
      stack_pop_exec m1 = Some m2 -> stack_pop m1 m2.
  Proof.
    intros * POP.
    cbn in *.
    repeat break_match_hyp_inv.
    split.
    - (* pop frame *)
      eexists; split.
      rewrite peek_pop, Heqo; cbn.
      reflexivity.
      rewrite Memory_frame_stack_modify_spec; auto.
    - (* bytes freed *)
      intros * PTRIN.
      destruct m1; cbn in *.
      intros aid ALLOC.
      unfold addr_allocated in *.
      unfold ptr_in_current_frame in PTRIN.
      break_match_hyp_inv.
      cbn in Heqo0.
      rewrite peek_pop, Heqo in Heqo0; inv Heqo0.
      rewrite free_bytes_exec_sub_mem in ALLOC.
      cbn in ALLOC.
      eapply MEM.free_bytes_exec_frees; eauto.
      apply ptr_in_frame_ptrs_in_frame; auto.
    - (* Non frame allocations preserved *)
      intros * PTRIN.
      destruct m1; cbn in *.
      rewrite free_bytes_exec_sub_mem.
      cbn; unfold addr_allocated; cbn.
      eapply MEM.free_bytes_exec_other_allocations; eauto.
      unfold ptr_in_current_frame in PTRIN.
      cbn in *.
      rewrite peek_pop, Heqo in PTRIN.
      cbn in PTRIN.
      apply Forall_forall.
      intros x H CONTRA; subst.
      apply ptr_in_frame_ptrs_in_frame in H.
      rewrite PTRIN in H.
      discriminate.
    - (* Non frame reads preserved *)
      intros * PTRIN.
      destruct m1; cbn in *.
      rewrite free_bytes_exec_sub_mem.
      cbn; unfold read_byte; cbn.
      eapply MEM.free_bytes_exec_other_reads; eauto.
      unfold ptr_in_current_frame in PTRIN.
      cbn in *.
      rewrite peek_pop, Heqo in PTRIN.
      cbn in PTRIN.
      apply Forall_forall.
      intros x H CONTRA; subst.
      apply ptr_in_frame_ptrs_in_frame in H.
      rewrite PTRIN in H.
      discriminate.
  Qed.

  Lemma heap_allocate_block_correct :
    forall (m m' : Memory)
      (ptrs : addr * list addr)
      (bytes : list SByte)
      (aid : AllocationId),
      heap_allocate_block_exec m bytes aid =
        Error.NoOom (m', ptrs) ->
      heap_allocate_block m bytes aid (m', ptrs).
  Proof.
    intros * ALLOC.
    autounfold with BASE_MEM in *.
    unfold heap_allocate_block_exec in *.
    repeat break_match_hyp_inv.
    red.
    exists m0, ptrs.
    split.
    - apply allocate_block_correct; eauto.
    - auto.
  Qed.

  Lemma addr_allocated_Modify_heap_invariant :
    forall m ptr aid f,
      addr_allocated m ptr aid <->
        addr_allocated (Memory_heap_modify m f) ptr aid.
  Proof.
    intros m ptr aid f.
    destruct m; cbn.
    unfold addr_allocated; cbn.
    reflexivity.
  Qed.

  #[global] Hint Resolve -> addr_allocated_Modify_heap_invariant : MEM.
  #[global] Hint Resolve <- addr_allocated_Modify_heap_invariant : MEM.

  Lemma addr_not_allocated_Modify_heap_invariant :
    forall m ptr f,
      addr_not_allocated m ptr <->
        addr_not_allocated (Memory_heap_modify m f) ptr.
  Proof.
    intros m ptr f.
    unfold addr_not_allocated.
    split; intros NOT aid CONTRA; eapply NOT; eauto with MEM.
  Qed.

  #[global] Hint Resolve -> addr_not_allocated_Modify_heap_invariant : MEM.
  #[global] Hint Resolve <- addr_not_allocated_Modify_heap_invariant : MEM.

  Lemma read_byte_Modify_heap_invariant :
    forall m ptr aid f,
      read_byte m ptr aid <->
        read_byte (Memory_heap_modify m f) ptr aid.
  Proof.
    intros m ptr aid f.
    destruct m; cbn.
    unfold read_byte; cbn.
    reflexivity.
  Qed.

  #[global] Hint Resolve -> read_byte_Modify_heap_invariant : MEM.
  #[global] Hint Resolve <- read_byte_Modify_heap_invariant : MEM.

  Lemma heap_free_free_spec :
    forall (m : Memory) (root : addr)
      (m' : Memory),
      heap_free_exec m root = Some m' -> free_spec m root m'.
  Proof.
    intros m root m' FREE.
    unfold heap_free_exec in *.
    cbn in *.
    break_match_hyp_inv.
    split.
    - (* bytes freed *)
      intros ptr PTRIN.
      destruct m; cbn.
      apply addr_not_allocated_Modify_heap_invariant.
      eapply free_bytes_exec_frees; eauto with MEM.
      unfold ptr_in_memory_heap in PTRIN.
      cbn in PTRIN.
      eapply ptr_in_heap_ptrs_in_heap; eauto.
    - (* block bytes preserved *)
      intros ptr aid PTRIN.
      destruct m; cbn.
      rewrite <- addr_allocated_Modify_heap_invariant.
      eapply free_bytes_exec_other_allocations.
      reflexivity.
      cbn in *.
      apply Forall_forall.
      intros x H.
      unfold ptr_in_memory_heap in *; cbn in *.
      intros CONTRA; subst.
      eapply ptr_in_heap_ptrs_in_heap in H.
      rewrite H in PTRIN; inv PTRIN.
    - (* reads preserved *)
      intros ptr aid PTRIN.
      destruct m; cbn.
      rewrite <- read_byte_Modify_heap_invariant.
      eapply free_bytes_exec_other_reads.
      reflexivity.
      cbn in *.
      apply Forall_forall.
      intros x H.
      unfold ptr_in_memory_heap in *; cbn in *.
      intros CONTRA; subst.
      eapply ptr_in_heap_ptrs_in_heap in H.
      rewrite H in PTRIN; inv PTRIN.
    - (* Block is free *)
      split.
      + intros ptr PTRIN.
        erewrite Memory_heap_modify_spec; eauto; cbn.
        eapply free_root_in_heap_removes_ptrs; eauto.
      + erewrite Memory_heap_modify_spec; eauto; cbn.
        eapply free_root_in_heap_removes_root; eauto.
      + intros * DISJOINT.
        erewrite (Memory_heap_modify_spec (free_bytes_exec m (ptrs_in_heap (Memory_heap m) root))
                 (Memory_heap_modify (free_bytes_exec m (ptrs_in_heap (Memory_heap m) root))
          (fun _ : Heap => t0))); eauto; cbn.
        eapply free_root_in_heap_preserves_other_roots; eauto.
      + intros * DISJOINT.
        erewrite (Memory_heap_modify_spec (free_bytes_exec m (ptrs_in_heap (Memory_heap m) root))
                 (Memory_heap_modify (free_bytes_exec m (ptrs_in_heap (Memory_heap m) root))
          (fun _ : Heap => t0))); eauto; cbn.
        eapply free_root_in_heap_preserves_other_roots'; eauto.
  Qed.

  Lemma heap_free_correct :
    forall (m : Memory) (ptr : addr)
      (m' : Memory),
      heap_free_exec m ptr = Some m' -> heap_free m ptr m'.
  Proof.
    intros m ptr m' FREE.
    red; cbn.
    split.
    - unfold heap_free_exec in *.
      cbn in *.
      break_match_hyp_inv.

      split.
      + unfold root_ptr_in_memory_heap.
        destruct (root_ptr_in_heap (Memory_heap m) ptr) eqn:ROOT; auto.
        exfalso.
        apply free_root_in_heap_root_not_in_heap in ROOT.
        rewrite Heqo in ROOT; inv ROOT.
      + admit.
      + admit.
    - apply heap_free_free_spec; eauto.
  Admitted.

End CORRECT_ALLOCATABLE_MEMORY_FRESH_TO_FULL_CORRECT_MEMORY_MODEL'.
