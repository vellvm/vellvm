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

  Instance MemPropT_Monad : Monad MemPropT.
  Proof.
    split.
    - (* ret *)
      intros T x.
      unfold MemPropT.
      intros ms [err_msg | [[ms' res] | oom_msg]].
      + exact False. (* error is not a valid behavior here *)
      + exact (ms = ms' /\ x = res).
      + exact True. (* Allow OOM to refine anything *)
    - (* bind *)
      intros A B ma amb.
      unfold MemPropT in *.

      intros ms [err_msg | [[ms'' b] | oom_msg]].
      + (* an error is valid when ma errors, or the continuation errors... *)
        refine
          ((exists err, ma ms (inl err)) \/
           (exists ms' a, 
               ma ms (inr (NoOom (ms', a))) ->
               (exists err, amb a ms' (inl err)))).
      + (* No errors, no OOM *)
        refine
          (exists ms' a k,
              ma ms (inr (NoOom (ms', a))) ->
              amb a ms' (inr (NoOom (ms'', k a)))).
      + (* OOM is always valid *)
        exact True.
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

  Section Handlers.
    Variable (E F: Type -> Type).
    Context `{FailureE -< E}.

    Variable MemM : Type -> Type.
    Context `{MemM_MemMonad : MemMonad MemState Provenance MemM}.

    Parameter write_byte_allowed : MemState -> addr -> Prop.
    Parameter write_byte_prop : MemState -> addr -> SByte -> MemState -> Prop.

    (* Parameters of the memory state module *)
    Parameter read_byte_MemPropT : addr -> MemPropT SByte.
    Definition read_byte_prop (ms : MemState) (ptr : addr) (byte : SByte) : Prop
      := read_byte_MemPropT ptr ms (inr (NoOom (ms, byte))).

    Parameter addr_allocated_prop : addr -> MemPropT bool.

    Definition byte_allocated_MemPropT (ptr : addr) : MemPropT unit :=
      m <- get_mem_state;;
      b <- addr_allocated_prop ptr;;
      MemPropT_assert (b = true).

    Definition byte_allocated (ms : MemState) (ptr : addr) : Prop
      := byte_allocated_MemPropT ptr ms (inr (NoOom (ms, tt))).

    Definition allocations_preserved (m1 m2 : MemState) : Prop :=
      forall ptr, byte_allocated m1 ptr <-> byte_allocated m2 ptr.

    Parameter disjoint_ptr_byte : addr -> addr -> Prop.

    Parameter Frame : Type.
    Parameter ptr_in_frame : Frame -> addr -> Prop.

    Parameter FrameStack : Type.
    Parameter peek_frame_stack : FrameStack -> Frame -> Prop.
    Parameter pop_frame_stack : FrameStack -> FrameStack -> Prop.
    (* Parameter push_frame_stack : FrameStack -> Frame -> FrameStack -> Prop. *)

    Parameter mem_state_frame_stack : MemState -> FrameStack -> Prop.

    (*** Reading from memory *)
    Record read_byte_spec (ms : MemState) (ptr : addr) (byte : SByte) : Prop :=
      { read_byte_allocated : byte_allocated ms ptr;
        read_byte_value : read_byte_prop ms ptr byte;
      }.

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
    Record mempush_spec (m1 : MemState) (m2 : MemState) : Prop :=
      {
        (* All allocations are preserved *)
        mempush_allocations :
        allocations_preserved m1 m2;

        (* All reads are preserved *)
        mempush_lu : forall ptr byte,
          read_byte_spec m1 ptr byte <->
            read_byte_spec m2 ptr byte;

        fresh_frame :
        forall fs1 fs2 f,
          mem_state_frame_stack m1 fs1 ->
          empty_frame f ->
          push_frame_stack_spec fs1 f fs2 ->
          mem_state_frame_stack m2 fs2;
      }.

    (** mempop *)
    Record mempop_spec (m1 : MemState) (m2 : MemState) : Prop :=
      {
        (* all bytes in popped frame are freed. *)
        bytes_freed :
        forall ptr,
          ptr_in_current_frame m1 ptr ->
          ~byte_allocated m2 ptr;

        (* Bytes not allocated in the current frame have the same allocation status as before *)
        non_frame_bytes_preserved :
        forall ptr,
          (~ ptr_in_current_frame m1 ptr) ->
          byte_allocated m1 ptr <-> byte_allocated m2 ptr;

        non_frame_bytes_read :
        forall ptr byte,
          (~ ptr_in_current_frame m1 ptr) ->
          read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

        pop_frame :
        forall fs1 fs2,
          mem_state_frame_stack m1 fs1 ->
          pop_frame_stack fs1 fs2 ->
          mem_state_frame_stack m2 fs2;
      }.

    (* Add a pointer onto the current frame in the frame stack *)
    Definition add_ptr_to_frame_stack (fs1 : FrameStack) (ptr : addr) (fs2 : FrameStack) : Prop :=
      forall f f' fs1_pop,
        peek_frame_stack fs1 f ->
        add_ptr_to_frame f ptr f' ->
        pop_frame_stack fs1 fs1_pop ->
        push_frame_stack_spec fs1_pop f' fs2.

    Definition frame_stack_preserved (m1 m2 : MemState) : Prop
      := forall fs,
        mem_state_frame_stack m1 fs <-> mem_state_frame_stack m2 fs.

    (*** Writing to memory *)
    Record set_byte_memory (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
      {
        new_lu : read_byte_spec m2 ptr byte;
        old_lu : forall ptr' byte',
          disjoint_ptr_byte ptr ptr' ->
          (read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
      }.

    (* I'll need something like this? *)
    Parameter write_byte_allowed_allocated :
      forall m ptr, write_byte_allowed m ptr -> byte_allocated m ptr.

    Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
      {
        byte_write_succeeds : write_byte_allowed m1 ptr;
        byte_written : set_byte_memory m1 ptr byte m2;

        write_byte_preserves_allocations : allocations_preserved m1 m2;
        write_byte_preserves_frame_stack : frame_stack_preserved m1 m2;
      }.

    Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT unit
      := fun m1 res =>
           match res with
           | inr (NoOom (m2, _)) => write_byte_spec m1 ptr byte m2
           | _ => True (* Allowed to run out of memory or fail *)
           end.

    (*** Allocating bytes in memory *)
    Record allocate_byte_succeeds_spec (m1 : MemState) (t : dtyp) (init_byte : SByte) (m2 : MemState) (ptr : addr) : Prop :=
      {
        was_fresh_byte : ~ byte_allocated m1 ptr;
        now_byte_allocated : byte_allocated m2 ptr;
        undef_byte_written : set_byte_memory m1 ptr init_byte m2;
        old_allocations_preserved :
        forall ptr',
          disjoint_ptr_byte ptr ptr' ->
          (byte_allocated m1 ptr' <-> byte_allocated m2 ptr');

        add_to_frame :
        forall fs1 fs2,
          mem_state_frame_stack m1 fs1 ->
          add_ptr_to_frame_stack fs1 ptr fs2 ->
          mem_state_frame_stack m2 fs2;
      }.

    Definition allocate_spec_MemPropT (t : dtyp) (init_byte : SByte) : MemPropT addr
      := fun m1 res =>
           match res with
           | inr (NoOom (m2, ptr)) =>
               allocate_byte_succeeds_spec m1 t init_byte m2 ptr
           | _ => True (* Allowed to run out of memory or fail *)
           end.    

    (*** Aggregate things *)

    Import MP.GEP.
    Require Import List.
    Import ListNotations.
    Import LP.
    Import ListUtil.
    Import Utils.Monads.

    (* TODO: Move this? *)
    Definition intptr_seq (start : Z) (len : nat) : OOM (list IP.intptr)
      := Util.map_monad (IP.from_Z) (Zseq start len).

    Definition write_bytes_spec (ptr : addr) (bytes : list SByte) : MemPropT unit :=
      (* Want OOM / errors to happen before any writes *)
      ixs <- lift_OOM (intptr_seq 0 (length bytes));;
      ptrs <- lift_err_RAISE_ERROR
               (Util.map_monad
                  (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
                  ixs);;

      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      foldM (fun _ '(ptr, byte) => write_byte_spec_MemPropT ptr byte) tt ptr_bytes.
    
    
    Definition memprop_bind {A B} (ma : MemState -> A -> MemState -> Prop) (k : MemState -> (MemState -> B -> MemState -> Prop)) : MemState -> B -> MemState -> Prop
      := fun ms_init b ms_final =>
           forall ms' a, ma ms_init a ms' ->
                    (k ms')
    .

    Require Import List.
    @fold_left (MemState * Prop) (list SByte) (fun '(ms, P) byte => )
    write_byte_spec
    
    Parameter write_bytes_prop : MemState -> addr -> list SByte -> MemState -> Prop.
    Parameter read_bytes_prop : MemState -> addr -> list SByte -> Prop.
    Parameter write_succeeds : MemState -> addr -> list SByte -> Prop.

    Record write_bytes_spec (m1 : MemState) (ptr : addr) (bytes : list SByte) (m2 : MemState) : Prop :=
      {
        succeeds : write_succeeds m1 ptr bytes;
        new_lu : length bytes <> 0 -> read_bytes_prop m2 ptr bytes
      }.
    
    Parameter read_bytes_prop : MemState -> list SByte -> MemState -> Prop.

    Record read_bytes_spec (m1 : MemState) (bytes : list SByte) (m2 
    (* Actually need allocate_spec etc for all of these *)
    Parameter push_fresh_frame_prop : MemState -> MemState -> Prop.

    Record push_fresh_frame_spec (m1 : MemState) (m2 : MemState) : Prop :=
      {
        
      }.

    Parameter free_frame_spec : MemState -> err MemState.
    Parameter allocate_spec : MemState -> MemState.

    Variable m : MemState.
    Definition handle_memory_prop : MemoryE ~> MemPropT E
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush => modify_mem_state push_fresh_frame;; ret tt
           | MemPop =>
               m <- get_mem_state;;
               m' <- lift_itree_memPropT (lift_pure_err (free_frame m));;
               put_mem_state m'
           | Alloca t => ret DVALUE_None
           | Load t a => ret UVALUE_None
           | Store t a v => ret tt
           | GEP t v vs => ret UVALUE_None
           | ItoP t i => ret UVALUE_None
           | PtoI t a => ret UVALUE_None
           end.
  End Handlers.
End MemoryModelSpec.
