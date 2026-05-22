Require Import Morphisms.

From Vellvm Require Import
  Numeric.Integers
  Utilities
  Syntax.

From ITree Require Import
  ITree
  Basics.Basics
  Events.Exception
  Eq.Eqit
  Events.StateFacts
  Events.State.

From ExtLib Require Import
  Structures.Functor.

From Stdlib Require Import
  ZArith
  Strings.String
  Relations
  RelationClasses
  Wellfounded.

Import Basics.Basics.Monads.
Import Monad.
Import EitherMonad.

From Vellvm.Semantics Require Import
  DynamicValues
  VellvmIntegers
  Params
  LLVMEvents
  Params.Memory
  Operations.
From Stdlib Require Import FunctionalExtensionality.
Import Logic.

(* TODO: Move this *)
Definition repeatMN {A m} `{Monad m} (n : N) (ma : m A) : m (list A)
  := sequence (repeatN n ma).

(* TODO: Move. Also, do I really have to define this? *)
Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
  := match xs, ys with
     | [], _        => []
     | _, []        => []
     | a::xs', b::ys' => f a b :: zipWith f xs' ys'
     end.

Definition zip {X Y} (xs : list X) (ys : list Y) := zipWith (fun a b => (a, b)) xs ys.

Section MemoryModel.
  Context {Pa : Params} {MMP : @MemoryModelPrimitives Pa}.

  Definition get_consecutive_ptrs (ptr : addr) (len : nat) : EOB (list addr) :=
    ixs <- intptr_seq 0 len;;
    map_monad
      (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
      ixs.

  (** Reading dvalues *)
  Definition read_bytes (ptr : addr) (len : nat) : memM (list memory_byte) :=
    ptrs <- lift (get_consecutive_ptrs ptr len);;
    (* Actually perform reads *)
    map_monad read_byte ptrs.
  
  Definition read_dvalue (dt : dtyp) (ptr : addr) : memM dvalue :=
    bytes <- read_bytes ptr (N.to_nat (sizeof_dtyp dt));;
    lift (memory_bytes_to_dvalue bytes dt).

  (** Writing dvalues *)
  Definition write_bytes (ptr : addr) (bytes : list memory_byte) : memM unit :=
    ptrs <- lift (get_consecutive_ptrs ptr (List.length bytes));;
    let ptr_bytes := zip ptrs bytes in
    (* Actually perform writes *)
    map_monad_ (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

  Definition write_dvalue (dt : dtyp) (ptr : addr) (v : dvalue) : memM unit :=
    write_bytes ptr (dvalue_to_memory_bytes v dt).

  Definition generate_num_poison_bytes_h
    (start_ix : N) (num : N) (dt : dtyp) : list memory_byte :=
    N.recursion 
      (fun (x : N) => [])
      (fun n mf x =>
         let rest_bytes := mf (N.succ x) in
         MByte (DVALUE_Poison dt) dt x :: rest_bytes)
      num start_ix.

  Definition generate_num_poison_bytes (num : N) (dt : dtyp) : list memory_byte :=
    generate_num_poison_bytes_h 0 num dt.

  Definition generate_poison_bytes (dt : dtyp) : list memory_byte :=
    generate_num_poison_bytes (sizeof_dtyp dt) dt.

  (** Allocating dtyps *)
  Definition allocate_bytes (init_bytes : list memory_byte) : memM addr :=
    pr <- fresh_prov;;
    allocate_bytes_with_pr init_bytes pr.

  Definition allocate_dtyp (dt : dtyp) (num_elements : N) : memM addr :=
    if dtyp_eqb dt DTYPE_Void
    then mub "allocating void type"
    else element_bytes <- repeatMN num_elements (ret (generate_poison_bytes dt));;
         let bytes := List.concat element_bytes in
         allocate_bytes bytes.

  (** Malloc *)
  Definition malloc_bytes (init_bytes : list memory_byte) : memM addr :=
    pr <- fresh_prov;;
    malloc_bytes_with_pr init_bytes pr.

  (* (** Handle memcpy *) *)
  Definition memcpy (src dst : addr) (len : Z) (volatile : bool) : memM unit :=
    if Z.ltb len 0
    then
      mub "memcpy given negative length."
    else
      (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
           memory from the source location to the destination location, which
           must either be equal or non-overlapping. *)
      
      if orb (no_overlap dst len src len)
           (Z.eqb (ptr_to_int src) (ptr_to_int dst))
      then 
        src_bytes <- read_bytes src (Z.to_nat len);;
        (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
        write_bytes dst src_bytes
      else
        mub "memcpy with overlapping or non-equal src and dst memory locations.".

  (** memset spec *)
  Definition memset
    (dst : addr) (val : int8) (len : Z) (volatile : bool) : memM unit :=
    if Z.ltb len 0
    then
      mub "memset given negative length."
    else
      let byte := MByte (DVALUE_I 8 val) (DTYPE_I 8) 0 in
      write_bytes dst (repeatN (Z.to_N len) byte).

  Definition handle_memoryM : MemoryE ~> memM :=
    fun T m =>
      match m with
      | MemPush => mempush
      | MemPop => mempop
      | Alloca t n align =>
          addr <- allocate_dtyp t n;;
          ret (DVALUE_Addr addr)
      | Load t a =>
          match a with
          | DVALUE_Addr a =>
              read_dvalue t a
          | _ => mub "Loading from something that isn't an address."
          end
      | Store t a v =>
          match a with
          | DVALUE_Addr a =>
              write_dvalue t a v
          | _ => mub "Writing something to somewhere that isn't an address."
          end
      end.

End MemoryModel.

Section Implementation.
  Context {Pa : Params}.
  
  Definition byte := (memory_byte * allocationId)%type.
  Definition memory := IntMap byte.
  (** ** Frame and Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
   *)
  Definition Frame := list addr.
  Inductive Framestack : Type :=
  | Singleton (f : Frame)
  | Snoc (s : Framestack) (f : Frame).

  (** ** Heaps *)
  Definition block := list addr.
  Definition Heap := IntMap block.

  (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
   *)
  Record Memory_stack : Type :=
    mkMemoryStack
      { Memory_stack_memory : memory;
        Memory_stack_frame_stack : Framestack;
        Memory_stack_heap : Heap;
      }.

  Definition memory_empty : memory := IntMaps.empty.
  Definition frame_empty : Framestack := Singleton [].
  Definition heap_empty : Heap := IntMaps.empty.
  Definition empty_memory_stack : Memory_stack :=
    mkMemoryStack memory_empty frame_empty heap_empty.

  (** ** MemState
      A memory stack enriched with a provenance
   *)
  Record State :=
    mkState
      { state_memory_stack : Memory_stack;
        (* Used to keep track of allocation ids in use *)
        state_provenance : provenance;
      }.

  Instance MemoryModelStateV : @MemoryModelState Pa :=
    {|
      memory_stack := Memory_stack ;
      state := State ;
      frame := Frame ;
      framestack := Framestack ;
      heap := Heap ;
      state_get_memory := state_memory_stack ;
      state_get_provenance := state_provenance ;
      memory_stack_framestack := Memory_stack_frame_stack ;
      memory_stack_heap  := Memory_stack_heap ;
      state_put_memory s m := let '(mkState m' p) := s in mkState m p ;
      initial_state := mkState empty_memory_stack initial_provenance ;
      initial_frame := [] ;
      initial_heap := heap_empty ;
    |}.

  (** Operations on memory *)
  Definition read_byte_raw_mem (mem : memory) (phys_addr : Z) : option byte :=
    IM.find phys_addr mem.
  Definition set_byte_raw_mem  (mem : memory) (phys_addr : Z) (byte : byte) : memory :=
    IM.add phys_addr byte mem.
  Definition next_key_mem (mem : memory) : Z :=
    next_key mem.

  (** Add block to memory with a given allocation id *)
  Definition memory_bytes_to_bytes
    (aid : allocationId) (bytes : list memory_byte) : list byte :=
    map (fun b => (b, aid)) bytes.

  (* Register a concrete address in a frame *)
  Definition add_to_frame (m : memory_stack) (k : addr) : memory_stack :=
    let '(mkMemoryStack m s h) := m in
    match s with
    | Singleton f => mkMemoryStack m (Singleton (k :: f)) h
    | Snoc s f => mkMemoryStack m (Snoc s (k :: f)) h
    end.

  (* Register a list of concrete addresses in a frame *)
  Definition add_all_to_frame (ks : list addr) (m : memory_stack) : memory_stack
    := fold_left (fun ms k => add_to_frame ms k) ks m.

  (* Register a ptr with the heap *)
  Definition add_to_heap (m : memory_stack) (root : addr) (ptr : addr) : memory_stack :=
    let '(mkMemoryStack m s h) := m in
    let h' := add_with (ptr_to_int root) ptr ret cons h in
    mkMemoryStack m s h'.

  (* Register a list of concrete addresses in the heap *)
  Definition add_all_to_heap' (m : memory_stack) (root : addr) (ks : list addr) : memory_stack
    := fold_left (fun ms k => add_to_heap ms root k) ks m.

  Definition add_all_to_heap (ks : list addr) (m : memory_stack) : memory_stack
    := match ks with
       | [] => m
       | (root :: _) =>
           add_all_to_heap' m root ks
       end.

  Definition get_frame_stack : memM Framestack :=
    fun s => ret (s,Memory_stack_frame_stack (state_get_memory s)).
  Definition get_frame : memM Frame :=
    fs <- get_frame_stack ;;
    match fs with
    | Singleton f | Snoc _ f => ret f
    end. 
  Definition get_mem : memM memory :=
    fun s => ret (s,Memory_stack_memory (state_get_memory s)).
  Definition get_framestack : memM Framestack :=
    fun s => ret (s,Memory_stack_frame_stack (state_get_memory s)).
  
  Definition app_state : (state -> state) -> memM unit :=
    fun f s => ret (f s, tt).
  Definition app_mem_stack : (Memory_stack -> Memory_stack) -> memM unit :=
    fun f s =>
      ret ({| state_memory_stack := f s.(state_memory_stack) ;
             state_provenance := state_provenance s |},tt).
  Definition upd_mem_stack (m : Memory_stack) : memM unit := app_mem_stack (fun _ => m).
  Definition app_mem : (memory -> memory) -> memM unit :=
    fun f s =>
      ret ({| state_memory_stack :=
               {| Memory_stack_memory     := f s.(state_memory_stack).(Memory_stack_memory) ;
                 Memory_stack_frame_stack := s.(state_memory_stack).(Memory_stack_frame_stack);
                 Memory_stack_heap        := s.(state_memory_stack).(Memory_stack_heap)
               |};
             state_provenance := state_provenance s |},tt).
  Definition upd_mem (m : memory) : memM unit := app_mem (fun _ => m).
  Definition app_frame_stack : (Framestack -> Framestack) -> memM unit :=
    fun f s =>
      ret ({| state_memory_stack :=
               {| Memory_stack_memory     := s.(state_memory_stack).(Memory_stack_memory) ;
                 Memory_stack_frame_stack := f s.(state_memory_stack).(Memory_stack_frame_stack);
                 Memory_stack_heap        := s.(state_memory_stack).(Memory_stack_heap)
               |};
             state_provenance := state_provenance s |},tt).
  Definition upd_frame_stack (fs : Framestack) : memM unit := app_frame_stack (fun _ => fs).
  Definition app_frame_stack_eob : (Framestack -> EOB Framestack) -> memM unit :=
    fun f =>
      fs <- get_framestack ;;
      f' <- lift (f fs) ;;
      upd_frame_stack f'.
  
  Definition next_key : memM Z :=
    m <- get_mem ;;
    ret (next_key_mem m).

  Definition push_frame_stack (f : Frame) (fs : Framestack) : Framestack :=
    Snoc fs f.
  Definition pop_frame_stack (fs : Framestack) : EOB Framestack :=
    match fs with
    | Singleton f => raise_error "Last frame, cannot pop."%string
    | Snoc s f => ret s
    end.

  Definition read_byte_raw (msg : string) (phys_addr : Z) : memM byte :=
    fun s =>
      match read_byte_raw_mem (Memory_stack_memory (state_get_memory s)) phys_addr with
      | Some b => ret (s,b)
      | None => Mub msg
      end.
  
  Definition set_byte_raw (phys_addr : Z) (byte : byte) : memM unit :=
    m <- get_mem ;;
    upd_mem (set_byte_raw_mem m phys_addr byte).

  (** Add block to memory with a given allocation id *)
  Definition add_block (aid : allocationId) (ptr : addr)
    (ptrs : list addr) (init_bytes : list memory_byte) : memM unit :=
    let mem_bytes := memory_bytes_to_bytes aid init_bytes in
    m <- get_mem;;
    upd_mem (add_all_index mem_bytes (ptr_to_int ptr) m).

  (** Add pointers to the stack frame *)
  Definition add_ptrs_to_frame (ptrs : list addr) : memM unit :=
    app_mem_stack (add_all_to_frame ptrs).
  
  Definition add_ptrs_to_heap (ptrs : list addr) : memM unit :=
    app_mem_stack (add_all_to_heap ptrs).
 
  (** Add a block of bytes to memory, and register it in the current stack frame. *)
  Definition add_block_to_stack (aid : allocationId) (ptr : addr)
    (ptrs : list addr) (init_bytes : list memory_byte) : memM unit :=
    add_block aid ptr ptrs init_bytes;;
    add_ptrs_to_frame ptrs.

  (** Add a block of bytes to memory, and register it in the heap. *)
  (* Should we make sure ptr (the root) is added even if ptrs is empty? *)
  Definition add_block_to_heap (aid : allocationId) (ptr : addr)
    (ptrs : list addr) (init_bytes : list memory_byte) : memM unit :=
    add_block aid ptr ptrs init_bytes;;
    add_ptrs_to_heap ptrs.

  Definition Read_byte (ptr : addr) : memM memory_byte :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    '(byte,aid) <- read_byte_raw "Reading from unallocated memory." addr;;
    if access_allowed pr aid
    then ret byte
    else mub ("Read from memory with invalid provenance").

  (** Writes *)
  Definition Write_byte (ptr : addr) (byte : memory_byte) : memM unit :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    '(_,aid) <- read_byte_raw "Writing to unallocated memory" addr ;;
    if access_allowed pr aid
    then set_byte_raw addr (byte,aid)
    else mub "Trying to write to memory with invalid provenance".

  Definition get_free_block (len : nat) (pr : provenance) : memM (addr * list addr) :=
    let aid := provenance_to_allocation_id pr in
    addr <- next_key ;;
    ptr <- lift (int_to_ptr addr (allocation_id_to_prov aid)) ;;
    ptrs <- lift (get_consecutive_ptrs ptr len);;
    ret (ptr,ptrs).

  Definition Allocate_bytes_with_pr (init_bytes : list memory_byte) (pr : provenance) : memM addr :=
    let len := List.length init_bytes in
    let aid := provenance_to_allocation_id pr in
    '(ptr, ptrs) <- get_free_block len pr;;
    add_block_to_stack aid ptr ptrs init_bytes;;
    ret ptr.

  (** Heap allocation *)
  Definition Malloc_bytes_with_pr (init_bytes : list memory_byte) (pr : provenance) : memM addr :=
    let len := List.length init_bytes in
    let aid := provenance_to_allocation_id pr in
    '(ptr, ptrs) <- get_free_block len pr;;
    add_block_to_heap aid ptr ptrs init_bytes;;
    ret ptr.

  Definition Mempush : memM unit :=
    app_frame_stack (push_frame_stack initial_frame).

  Definition free_byte (b : Z) (m : memory) : memory :=
    delete b m.

  Definition free_frame_memory (f : Frame) (m : memory) : memory :=
    fold_left (fun m key => free_byte (ptr_to_int key) m) f m.

  (** Stack free *)
  Definition Mempop : memM unit :=
    f <- get_frame ;;
    app_frame_stack_eob pop_frame_stack;;
    app_mem (free_frame_memory f).

  Instance MemoryModelPrimitivesV : @MemoryModelPrimitives Pa :=
    {|
      mm_state := MemoryModelStateV ;
      read_byte := Read_byte ;
      write_byte := Write_byte ;
      allocate_bytes_with_pr := Allocate_bytes_with_pr ;
      malloc_bytes_with_pr := Malloc_bytes_with_pr ;
      mempush := Mempush ;
      mempop := Mempop ;
    |}.
  
End Implementation.


