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
Class MemMonad (MemState : Type) (AllocationId : Type) (M : Type -> Type)
      `{Monad M}
      `{MonadAllocationId AllocationId M} `{MonadStoreID M} `{MonadMemState MemState M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} : Type
  :=
  {
    MemMonad_runs_to_prop {A} (ma : M A) (ms : MemState) (res : OOM (MemState * A)) : Prop;
    MemMonad_runs_to {A} (ma : M A) (ms : MemState) : option (MemState * A);
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

  Instance MemStateT_MonadAllocationId {M} :
    MonadAllocationId AllocationId (MemStateT M).
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
    : MemMonad MemState AllocationId (MemStateT (itree E)).
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

Module MemoryState (LP : LLVMParams) (MP : MemoryParams LP).

End MemoryState.

Module MemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.

  Require Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.

  Parameter MemState : Type.
  Definition MemPropT (X: Type): Type :=
    MemState -> err (OOM (MemState * X)%type) -> Prop.

  (* Instance MemPropT_Monad : Monad MemPropT. *)
  (* Proof. *)
  (*   split. *)
  (*   - (* ret *) *)
  (*     intros T x. *)
  (*     unfold MemPropT. *)
  (*     intros ms [err_msg | [[ms' res] | oom_msg]]. *)
  (*     + exact False. (* error is not a valid behavior here *) *)
  (*     + exact (ms = ms' /\ x = res). *)
  (*     + exact True. (* Allow OOM to refine anything *) *)
  (*   - (* bind *) *)
  (*     intros A B ma amb. *)
  (*     unfold MemPropT in *. *)

  (*     intros ms [err_msg | [[ms'' b] | oom_msg]]. *)
  (*     + (* an error is valid when ma errors, or the continuation errors... *) *)
  (*       refine *)
  (*         ((exists err, ma ms (inl err)) \/ *)
  (*          (exists ms' a, *)
  (*              ma ms (inr (NoOom (ms', a))) -> *)
  (*              (exists err, amb a ms' (inl err)))). *)
  (*     + (* No errors, no OOM *) *)
  (*       refine *)
  (*         (exists ms' a k, *)
  (*             ma ms (inr (NoOom (ms', a))) -> *)
  (*             amb a ms' (inr (NoOom (ms'', k a)))). *)
  (*     + (* OOM is always valid *) *)
  (*       exact True. *)
  (* Defined. *)

  (* To triple check, but the following makes more sense to me *)
  Instance MemPropT_Monad : Monad MemPropT.
  Proof.
    split.
    - (* ret *)
      refine (fun _ v s r => match r with
                          | inl _ => False
                          | inr (NoOom (s',r')) => s' = s /\ r' = v
                          | inr (Oom _) => True
                          end).
    - (* bind *)
      refine (fun A B ma amb sa r =>
                match r with
                | inl err            =>
                    ma sa (inl err) \/
                      (exists sab a, ma sa (inr (NoOom (sab, a))) /\
                                  (exists err, amb a sab (inl err)))
                | inr (NoOom (sb,r)) =>
                    exists sab a,
                    ma    sa  (inr (NoOom (sab, a))) /\
                      amb a sab (inr (NoOom (sb, r)))
                | inr (Oom _)         => True
                end
             ).
  Defined.

  Instance MemPropT_MonadMemState : MonadMemState MemState MemPropT.
  Proof.
    split.
    - (* get_mem_state *)
      unfold MemPropT.
      intros ms [err_msg | [[ms' a] | oom_msg]].
      + exact True.
      + exact (ms = ms' /\ a = ms).
      + exact True.
    - (* put_mem_state *)
      unfold MemPropT.
      intros ms_to_put ms [err_msg | [[ms' t] | oom_msg]].
      + exact True.
      + exact (ms_to_put = ms').
      + exact True.
  Defined.

  Instance MemPropT_RAISE_OOM : RAISE_OOM MemPropT.
  Proof.
    split.
    - intros A msg.
      unfold MemPropT.
      intros ms [err | [_ | oom]].
      + exact False. (* Must run out of memory, can't error *)
      + exact False. (* Must run out of memory *)
      + exact True. (* Don't care about message *)
  Defined.

  Instance MemPropT_RAISE_ERROR : RAISE_ERROR MemPropT.
  Proof.
    split.
    - intros A msg.
      unfold MemPropT.
      intros ms [err | [_ | oom]].
      + exact True. (* Any error will do *)
      + exact False. (* Must error *)
      + exact False. (* Must error *)
  Defined.

  Definition MemPropT_assert {X} (assertion : Prop) : MemPropT X
    := fun ms ms'x =>
         match ms'x with
         | inl _ =>
             assertion
         | inr (NoOom (ms', x)) =>
             ms = ms' /\ assertion
         | inr (Oom s) =>
             assertion
         end.

  Definition MemPropT_assert_post {X} (Post : X -> Prop) : MemPropT X
    := fun ms ms'x =>
         match ms'x with
         | inl _ =>
             True
         | inr (NoOom (ms', x)) =>
             ms = ms' /\ Post x
         | inr (Oom s) =>
             True
         end.

  Section Handlers.
    Variable (E F: Type -> Type).
    Context `{FailureE -< E}.

    Variable MemM : Type -> Type.
    Context `{MemM_MemMonad : MemMonad MemState Provenance MemM}.

    (** Addresses *)
    Definition disjoint_ptr_byte (a b : addr) :=
      ~ ptr_overlap a b.

    (*** Primitives *)

    (** Reads *)
    Parameter read_byte_MemPropT : addr -> MemPropT SByte.
    Definition read_byte_prop (ms : MemState) (ptr : addr) (byte : SByte) : Prop
      := read_byte_MemPropT ptr ms (inr (NoOom (ms, byte))).

    (** Allocations *)
    (* Is a byte allocated with a given AllocationId? *)
    Parameter addr_allocated_prop : addr -> AllocationId -> MemPropT bool.

    Definition byte_allocated_MemPropT (ptr : addr) (aid : AllocationId) : MemPropT unit :=
      m <- get_mem_state;;
      b <- addr_allocated_prop ptr aid;;
      MemPropT_assert (b = true).

    Definition byte_allocated (ms : MemState) (ptr : addr) (aid : AllocationId) : Prop
      := byte_allocated_MemPropT ptr aid ms (inr (NoOom (ms, tt))).

    Definition byte_not_allocated (ms : MemState) (ptr : addr) : Prop
      := forall (aid : AllocationId), ~ byte_allocated ms ptr aid.

    (** Frame stacks *)
    Parameter Frame : Type.
    Parameter ptr_in_frame : Frame -> addr -> Prop.

    Parameter FrameStack : Type.
    Parameter peek_frame_stack : FrameStack -> Frame -> Prop.
    Parameter pop_frame_stack : FrameStack -> FrameStack -> Prop.

    Parameter mem_state_frame_stack : MemState -> FrameStack -> Prop.

    (** Allocation ids / store ids *)
    Parameter used_allocation_id : MemState -> AllocationId -> Prop.
    Parameter used_store_id : MemState -> store_id -> Prop.

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

    (** Allocations *)
    Definition allocations_preserved (m1 m2 : MemState) : Prop :=
      forall ptr aid, byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid.

    (** Provenances / allocation ids *)
    Definition extend_allocation_ids (ms : MemState) (new_aid : AllocationId) (ms' : MemState) : Prop
      := (forall aid, used_allocation_id ms aid -> used_allocation_id ms' aid) /\
           ~ used_allocation_id ms new_aid /\
           used_allocation_id ms' new_aid.

    Definition preserve_allocation_ids (ms ms' : MemState) : Prop
      := forall p, used_allocation_id ms p <-> used_allocation_id ms' p.

    (** Store ids *)
    Definition extend_store_ids (ms : MemState) (new_sid : store_id) (ms' : MemState) : Prop
      := (forall p, used_store_id ms p -> used_store_id ms' p) /\
           ~ used_store_id ms new_sid /\
           used_store_id ms' new_sid.

    Definition preserve_store_ids (ms ms' : MemState) : Prop
      := forall sid, used_store_id ms sid <-> used_store_id ms' sid.

    (** Frame stack *)
    Definition frame_stack_preserved (m1 m2 : MemState) : Prop
      := forall fs,
        mem_state_frame_stack m1 fs <-> mem_state_frame_stack m2 fs.

    (*** Other helpers *)
    Import MP.GEP.
    Require Import List.
    Import ListNotations.
    Import LP.
    Import ListUtil.
    Import Utils.Monads.

    (* TODO: Move this? *)
    Definition intptr_seq (start : Z) (len : nat) : OOM (list IP.intptr)
      := Util.map_monad (IP.from_Z) (Zseq start len).

    Definition get_consecutive_ptrs (ptr : addr) (len : nat) : MemPropT (list addr) :=
      ixs <- lift_OOM (intptr_seq 0 len);;
      lift_err_RAISE_ERROR
        (Util.map_monad
           (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
           ixs).

    (*** Allocation id operations *)
    Instance MemPropT_MonadAllocationId : MonadAllocationId AllocationId MemPropT.
    Proof.
      split.
      - (* fresh_allocation_id *)
        unfold MemPropT.
        intros ms [err | [[ms' new_aid] | oom]].
        + exact True.
        + exact
            ( extend_allocation_ids ms new_aid ms' /\
                preserve_store_ids ms ms' /\
                read_byte_preserved ms ms' /\
                write_byte_allowed_all_preserved ms ms' /\
                allocations_preserved ms ms' /\
                frame_stack_preserved ms ms'
            ).
        + exact True.
    Defined.

    (*** Store id operations *)
    Instance MemPropT_MonadStoreID : MonadStoreID MemPropT.
    Proof.
      split.
      - (* fresh_sid *)
        unfold MemPropT.
        intros ms [err | [[ms' new_sid] | oom]].
        + exact True.
        + exact
            ( extend_store_ids ms new_sid ms' /\
                preserve_allocation_ids ms ms' /\
                read_byte_preserved ms ms' /\
                write_byte_allowed_all_preserved ms ms' /\
                allocations_preserved ms ms' /\
                frame_stack_preserved ms ms'
            ).
        + exact True.
    Defined.

    (*** Reading from memory *)
    Record read_byte_spec (ms : MemState) (ptr : addr) (byte : SByte) : Prop :=
      { read_byte_allowed_spec : read_byte_allowed ms ptr;
        read_byte_value : read_byte_prop ms ptr byte;
      }.

    Definition read_byte_spec_MemPropT (ptr : addr) : MemPropT SByte:=
      fun m1 res =>
           match res with
           | inr (NoOom (m2, byte)) => m1 = m2 /\ read_byte_spec m1 ptr byte
           | _ => True (* Allowed to run out of memory or fail *)
           end.

    (*** Framestack operations *)
    Definition empty_frame (f : Frame) : Prop :=
      forall ptr, ~ ptr_in_frame f ptr.

    Record add_ptr_to_frame (f1 : Frame) (ptr : addr) (f2 : Frame) : Prop :=
      {
        old_frame_lu : forall ptr', ptr_in_frame f1 ptr' -> ptr_in_frame f2 ptr';
        new_frame_lu : ptr_in_frame f2 ptr;
      }.

    Record empty_frame_stack (fs : FrameStack) : Prop :=
      {
        no_pop : (forall f, ~ pop_frame_stack fs f);
        empty_fs_empty_frame : forall f, peek_frame_stack fs f -> empty_frame f;
      }.

    Record push_frame_stack_spec (fs1 : FrameStack) (f : Frame) (fs2 : FrameStack) : Prop :=
      {
        can_pop : pop_frame_stack fs2 fs1;
        new_frame : peek_frame_stack fs2 f;
      }.

    Definition ptr_in_current_frame (ms : MemState) (ptr : addr) : Prop
      := forall fs, mem_state_frame_stack ms fs ->
               forall f, peek_frame_stack fs f ->
                    ptr_in_frame f ptr.

    (** mempush *)
    Record mempush_operation_invariants (m1 : MemState) (m2 : MemState) :=
      {
        mempush_op_reads : read_byte_preserved m1 m2;
        mempush_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
        mempush_op_allocations : allocations_preserved m1 m2;
        mempush_op_store_ids : preserve_store_ids m1 m2;
        mempush_op_allocation_ids : preserve_allocation_ids m1 m2;
      }.

    Record mempush_spec (m1 : MemState) (m2 : MemState) : Prop :=
      {
        fresh_frame :
        forall fs1 fs2 f,
          mem_state_frame_stack m1 fs1 ->
          empty_frame f ->
          push_frame_stack_spec fs1 f fs2 ->
          mem_state_frame_stack m2 fs2;

        mempush_invariants :
        mempush_operation_invariants m1 m2;
      }.

    Definition mempush_spec_MemPropT : MemPropT unit :=
      fun m1 res =>
        match res with
        | inr (NoOom (m2, _)) => mempush_spec m1 m2
        | _ => True (* Allowed to run out of memory or fail *)
        end.

    (** mempop *)
    Record mempop_operation_invariants (m1 : MemState) (m2 : MemState) :=
      {
        mempop_op_store_ids : preserve_store_ids m1 m2;
        mempop_op_allocation_ids : preserve_allocation_ids m1 m2;
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
          mem_state_frame_stack m1 fs1 ->
          pop_frame_stack fs1 fs2 ->
          mem_state_frame_stack m2 fs2;

        (* Invariants *)
        mempop_invariants : mempop_operation_invariants m1 m2;
      }.

    Definition mempop_spec_MemPropT : MemPropT unit :=
      fun m1 res =>
        match res with
        | inr (NoOom (m2, _)) => mempop_spec m1 m2
        | _ => True (* Allowed to run out of memory or fail *)
        end.

    (* Add a pointer onto the current frame in the frame stack *)
    Definition add_ptr_to_frame_stack (fs1 : FrameStack) (ptr : addr) (fs2 : FrameStack) : Prop :=
      forall f f' fs1_pop,
        peek_frame_stack fs1 f ->
        add_ptr_to_frame f ptr f' ->
        pop_frame_stack fs1 fs1_pop ->
        push_frame_stack_spec fs1_pop f' fs2.

    Fixpoint add_ptrs_to_frame_stack (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) : Prop :=
      match ptrs with
      | nil => fs1 = fs2
      | (ptr :: ptrs) =>
          forall fs',
            add_ptrs_to_frame_stack fs1 ptrs fs' ->
            add_ptr_to_frame_stack fs' ptr fs2
      end.

    (*** Writing to memory *)
    Record set_byte_memory (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
      {
        new_lu : read_byte_spec m2 ptr byte;
        old_lu : forall ptr' byte',
          disjoint_ptr_byte ptr ptr' ->
          (read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
      }.

    Record write_byte_operation_invariants (m1 m2 : MemState) : Prop :=
      {
        write_byte_op_preserves_allocations : allocations_preserved m1 m2;
        write_byte_op_preserves_frame_stack : frame_stack_preserved m1 m2;
        write_byte_op_read_allowed : read_byte_allowed_all_preserved m1 m2;
        write_byte_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
        write_byte_op_store_ids : preserve_store_ids m1 m2;
        write_byte_op_allocation_ids : preserve_allocation_ids m1 m2;
      }.

    Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
      {
        byte_write_succeeds : write_byte_allowed m1 ptr;
        byte_written : set_byte_memory m1 ptr byte m2;

        write_byte_invariants : write_byte_operation_invariants m1 m2;
      }.

    Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT unit
      := fun m1 res =>
           match res with
           | inr (NoOom (m2, _)) => write_byte_spec m1 ptr byte m2
           | _ => True (* Allowed to run out of memory or fail *)
           end.

    (*** Allocating bytes in memory *)
    Record allocate_bytes_succeeds_spec (m1 : MemState) (t : dtyp) (init_bytes : list SByte) (aid : AllocationId) (m2 : MemState) (ptr : addr) (ptrs : list addr) : Prop :=
      {
        (* The allocated pointers are consecutive in memory. *)
        (* m1 doesn't really matter here. *)
        allocate_bytes_consecutive : get_consecutive_ptrs ptr (length init_bytes) m1 (inr (NoOom (m1, ptrs)));

        (* Provenance *)
        address_provenance : forall ptr, In ptr ptrs -> address_provenance ptr = allocation_id_to_prov aid;

        (* Allocation ids *)
        allocate_bytes_aid_fresh : ~ used_allocation_id m1 aid;
        allocate_bytes_aid : used_allocation_id m2 aid;
        allocate_bytes_aids_preserved :
        forall aid',
          aid <> aid' ->
          (used_allocation_id m1 aid' <-> used_allocation_id m2 aid');

        (* byte_allocated *)
        allocate_bytes_was_fresh_byte : forall ptr, In ptr ptrs -> byte_not_allocated m1 ptr;
        allocate_bytes_now_byte_allocated : forall ptr, In ptr ptrs -> byte_allocated m2 ptr aid;
        allocate_bytes_preserves_old_allocations :
        forall ptr aid,
          ~ In ptr ptrs ->
          (byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid);

        (* read permissions *)
        alloc_bytes_new_reads_allowed :
        forall p, In p ptrs ->
             read_byte_allowed m2 p;

        alloc_bytes_old_reads_allowed :
        forall ptr',
          (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
          read_byte_allowed m1 ptr' <-> read_byte_allowed m2 ptr';

        (* reads *)
        alloc_bytes_new_reads :
        forall p ix byte,
          Util.Nth ptrs ix p ->
          Util.Nth init_bytes ix byte ->
          read_byte_prop m2 p byte;

        alloc_bytes_old_reads :
        forall ptr' byte,
          (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
          read_byte_prop m1 ptr' byte <-> read_byte_prop m2 ptr' byte;

        (* write permissions *)
        alloc_bytes_new_writes_allowed :
        forall p, In p ptrs ->
             write_byte_allowed m2 p;

        alloc_bytes_old_writes_allowed :
        forall ptr',
          (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
          write_byte_allowed m1 ptr' <-> write_byte_allowed m2 ptr';

        (* Add allocated bytes onto the stack frame *)
        allocate_bytes_add_to_frame :
        forall fs1 fs2,
          mem_state_frame_stack m1 fs1 ->
          add_ptrs_to_frame_stack fs1 ptrs fs2 ->
          mem_state_frame_stack m2 fs2;

        (* Store ids are preserved. *)
        allocate_bytes_store_ids :
        preserve_store_ids m1 m2;
      }.

    Definition allocate_bytes_spec_MemPropT' (t : dtyp) (init_bytes : list SByte) (aid : AllocationId)
      : MemPropT (addr * list addr)
      := fun m1 res =>
           match res with
           | inr (NoOom (m2, (ptr, ptrs))) =>
               allocate_bytes_succeeds_spec m1 t init_bytes aid m2 ptr ptrs
           | _ => True (* Allowed to run out of memory or fail *)
           end.

    Definition allocate_bytes_spec_MemPropT (t : dtyp) (init_bytes : list SByte)
      : MemPropT addr
      := aid <- fresh_allocation_id;;
         '(ptr, _) <- allocate_bytes_spec_MemPropT' t init_bytes aid;;
         ret ptr.

    (*** Aggregate things *)

    (** Reading uvalues *)
    Definition read_bytes_spec (ptr : addr) (len : nat) : MemPropT (list SByte) :=
      ptrs <- get_consecutive_ptrs ptr len;;

      (* Actually perform reads *)
      Util.map_monad (fun ptr => read_byte_spec_MemPropT ptr) ptrs.

    Definition read_uvalue_spec (dt : dtyp) (ptr : addr) : MemPropT uvalue :=
      bytes <- read_bytes_spec ptr (N.to_nat (sizeof_dtyp dt));;
      ret (from_ubytes bytes dt).

    (** Writing uvalues *)
    Definition write_bytes_spec (ptr : addr) (bytes : list SByte) : MemPropT unit :=
      ptrs <- get_consecutive_ptrs ptr (length bytes);;
      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      Util.map_monad_ (fun '(ptr, byte) => write_byte_spec_MemPropT ptr byte) ptr_bytes.

    Definition write_uvalue_spec (dt : dtyp) (ptr : addr) (uv : uvalue) : MemPropT unit :=
      sid <- fresh_sid;;
      bytes <- lift_OOM (to_ubytes uv dt sid);;
      write_bytes_spec ptr bytes.

    (** Allocating dtyps *)
    Definition generate_undef_bytes (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
      N.recursion
        (fun (x : N) => ret [])
        (fun n mf x =>
           rest_bytes <- mf (N.succ x);;
           x' <- IP.from_Z (Z.of_N x);;
           let byte := uvalue_sbyte (UVALUE_Undef dt) dt (UVALUE_IPTR x') sid in
           ret (byte :: rest_bytes))
        (sizeof_dtyp dt) 0%N.

    (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
    Definition allocate_dtyp_spec (dt : dtyp) : MemPropT addr :=
      sid <- fresh_sid;;
      bytes <- lift_OOM (generate_undef_bytes dt sid);;
      allocate_bytes_spec_MemPropT dt bytes.

    (*** Handling memory events *)
    Definition handle_memory_prop : MemoryE ~> MemPropT
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush_spec_MemPropT
           | MemPop =>
               mempop_spec_MemPropT
           | Alloca t =>
               addr <- allocate_dtyp_spec t;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue_spec t a
               | _ =>
                   (* UB if loading from something that isn't an address *)
                   fun _ _ => False
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue_spec t a v
               | _ =>
                   (* UB if writing something to somewhere that isn't an address *)
                   fun _ _ => False
               end
           end.
  End Handlers.
End MemoryModelSpec.
