
Module MemoryModelPrimitivesLLVM (LP : LLVMParams) :> MemoryModelPrimitives LP.
  Import LP.
  Import DV ADDR SZ PROV PTOI.
  Module OP := Operations LP.
  Import OP.
  Import GEP SELECT COMPARE MBYTES CONVERT.

  Section Datatype_Definition.

    (* Memory consists of bytes which have a provenance associated with them. *)
    Definition byte := (memory_byte * AllocationId)%type.

    (* Memory is just a map of mem_bytes. *)
    Definition memory := IntMap byte.

    (** ** Frame and Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition frame := list addr.
    Inductive framestack : Type :=
    | Singleton (f : frame)
    | Snoc (s : framestack) (f : frame).

    (** ** Heaps *)
    Definition block := list addr.
    Definition heap := IntMap block.

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Record memory_stack : Type :=
      mkMemoryStack
        { memory_stack_memory : memory;
          memory_stack_frame_stack : framestack;
          memory_stack_heap : heap;
        }.

    (** Some operations on memory *)
    Definition set_byte_raw (mem : memory) (phys_addr : Z) (byte : byte) : memory :=
      IM.add phys_addr byte mem.

    Definition read_byte_raw (mem : memory) (phys_addr : Z) : option byte :=
      IM.find phys_addr mem.

  End Datatype_Definition.

  #[global] Opaque set_byte_raw.
  #[global] Opaque read_byte_raw.

  (** ** MemState
      A memory stack enriched with a provenance
   *)
  Record state :=
    mkState
      { state_memory_stack : memory_stack;
        (* Used to keep track of allocation ids in use *)
        state_provenance : Provenance;
      }.

  Definition memory_empty : memory := IntMaps.empty.
  Definition frame_empty : framestack := Singleton [].
  Definition heap_empty : heap := IntMaps.empty.
  Definition empty_memory_stack : memory_stack :=
    mkMemoryStack memory_empty frame_empty heap_empty.

  (** ** Initial memory state
   *)
  Definition initial_memory_state : state :=
    mkState empty_memory_stack initial_provenance.

  (** ** state get memory *)
  Definition state_get_memory (ms : state) : memory_stack :=
    ms.(state_memory_stack).
  (** ** state put memory *)
  Definition state_put_memory (mem' : memory_stack) (ms : state) : state :=
    let '(mkState mem prov) := ms in
    (mkState mem' prov).
  (** ** state get provenance *)
  Definition state_get_provenance (ms : state) : Provenance :=
    ms.(state_provenance).

  (** ** Read byte memory *)
  Definition read_byte_memory
    (ptr : addr) (mem_stack : memory_stack) : option memory_byte :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    let mem := memory_stack_memory mem_stack in
    '(byte,aid) <- read_byte_raw mem addr ;;
    if access_allowed pr aid
    then Some byte
    else None.

  (** ** Is allocated *)
  (* was: addr_allocated_prop_memory *)
  Definition is_addr_allocated (ptr : addr) (aid : AllocationId) (mem_stack : memory_stack) : bool :=
    let mem := memory_stack_memory mem_stack in
    match read_byte_raw mem (ptr_to_int ptr) with
    | None => false
    | Some (byte, aid') =>
        aid_eq_dec aid aid'
    end.

