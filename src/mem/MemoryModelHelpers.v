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

Notation err := (sum string).

Module Type ALLOCATABLE_MEMORY_FRESH (ADDR : BASIC_ADDRESS) (SB : SBYTE) (AID : ALLOCATION_ID) :=
  ALLOCATABLE_MEMORY ADDR SB AID <+ CORE_MEMORY_FRESH_STORE_ID ADDR SB <+ CORE_MEMORY_FRESH_AID ADDR SB AID.

(** Add a heap and stack to allocatable memory *)
Module ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL
  (Import ADDR : BASIC_ADDRESS)
  (Import SB : SBYTE)
  (Import AID : ALLOCATION_ID)
  (Import H : HEAP ADDR)
  (Import F : FRAME ADDR)
  (Import FS : FRAME_STACK ADDR F)
  (MEM : ALLOCATABLE_MEMORY_FRESH ADDR SB AID) <: FULL_MEMORY_MODEL ADDR SB AID H F FS.

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

  (** STACK *)
  Definition Memory_frame_stack := memory_frame_stack.
  Definition Memory_frame_stack_modify (m : Memory) (f : FrameStack -> FrameStack) : Memory :=
    match m with
    | MkMemory bm fs h =>
        MkMemory bm (f fs) h
    end.

  Lemma Memory_frame_stack_modify_spec :
    forall (m1 m2 : Memory) (f : FrameStack -> FrameStack) (fs1 fs2 : FrameStack),
      fs1 = Memory_frame_stack m1 ->
      m2 = Memory_frame_stack_modify m1 f -> fs2 = Memory_frame_stack m2 -> fs2 = f fs1.
  Proof.
    intros m1 m2 f fs1 fs2 H H0 H1.
    subst.
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


  (** MEMORY_ALLOCATE *)
  Record allocate_block' (m1 : Memory) (bytes : list SByte) (aid : AID.t) (m2 : Memory) (ptrs : (addr * list addr)) : Prop :=
    { (* Minimal set *)
      allocate_block_free : find_free_block m1 (length bytes) ptrs
    ; allocate_block_new_reads : Forall2 (fun b ptr => read_byte m2 ptr b) bytes (snd ptrs)
    ; allocate_block_old_reads : forall b ptr, read_byte m1 ptr b -> read_byte m2 ptr b
    ; allocate_block_allocated : Forall (fun ptr => addr_allocated m2 ptr aid) (snd ptrs)
    ; allocate_block_non_null : Forall (fun ptr => is_null ptr = false) (snd ptrs)

      (* Extras *)
    ; allocate_block_preserves_heap : Memory_heap m1 = Memory_heap m2
    ; allocate_block_preserves_stack : Memory_frame_stack m1 = Memory_frame_stack m2
    }.

  (* Make module types happy... *)
  Definition allocate_block := allocate_block'.

  (** Stack allocations *)
  (* It's a little unclear if OOM or err should take precedence... Currently OOM takes precedence. *)
  Definition stack_allocate_block
    (m : Memory) (bytes : list SByte) (aid : AllocationId) (res : err (Memory * (addr * list addr))) : Prop :=
    exists m' ptrs,
      allocate_block m bytes aid m' ptrs /\
        match add_all_to_current_frame (Memory_frame_stack m') (snd ptrs) with
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

  Include (ALL_READS_PRESERVED ADDR SB).

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

End ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL.
