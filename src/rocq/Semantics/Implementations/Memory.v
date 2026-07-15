Require Import Morphisms.

From Vellvm Require Import
  Numeric
  Utils
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
  EOU
  VellvmIntegers
  Params
  LLVMEvents
  Interfaces.Memory
  Operations.
From Stdlib Require Import FunctionalExtensionality.
Import Logic.

Section MemoryModel.
  Context {Pa : Params} {MMP : @MemoryModelPrimitives Pa}.

  (* We would like a better representation than a list *) 
  Definition get_consecutive_ptrs (p : ptr) (size : N) : EOU (list ptr) :=
    ixs <- intptr_seq 0 size;;
    map_monad
      (fun ix => handle_gep_ptr (DTYPE_I 8) p [DVALUE_Base (DVALUE_Iptr ix)])
      ixs.

  (** Reading dvalues *)
  Definition read_bytes (p : ptr) (size : N) : memM (list memory_byte) :=
    ptrs <- lift (get_consecutive_ptrs p size);;
    (* Actually perform reads *)
    map_monad read_byte ptrs.
  
  Definition read_dvalue (dt : dtyp) (p : ptr) : memM dvalue :=
    bytes <- read_bytes p (sizeof_dtyp dt);;
    lift (memory_bytes_to_dvalue bytes dt).

  (** Writing dvalues *)
  Definition write_bytes (p : ptr) (bytes : list memory_byte) : memM unit :=
    ptrs <- lift (get_consecutive_ptrs p (N.length bytes));;
    let ptr_bytes := zip ptrs bytes in
    (* Actually perform writes *)
    loop_monad (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

  Definition write_dvalue (dt : dtyp) (p : ptr) (v : dvalue) : memM unit :=
    write_bytes p (dvalue_to_memory_bytes v dt).

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
  Definition allocate_bytes (init_bytes : list memory_byte) (align : N) : memM ptr :=
    pr <- fresh_prov;;
    allocate_bytes_with_pr init_bytes align pr.

  Definition allocate_dtyp (dt : dtyp) (num_elements : N) (align : N) : memM ptr :=
    if dtyp_eqb dt DTYPE_Void
    then mub "allocating void type"
    else element_bytes <- repeatMN num_elements (ret (generate_poison_bytes dt));;
         let bytes := List.concat element_bytes in
         allocate_bytes bytes align.

  Definition handle_memoryM : MemoryE ~> memM :=
    fun T m =>
      match m with
      | MemPush => mempush
      | MemPop => mempop
      | Alloca t n align =>
          let align :=
            match align with
            | None => 8%N
            | Some align => align
            end in
          ptr <- allocate_dtyp t n align;;
          ret (DVALUE_Base (DVALUE_Pointer ptr))
      | Load t a =>
          match a with
          | DVALUE_Base (DVALUE_Pointer a) =>
              read_dvalue t a
          | _ => mub "Loading from something that isn't an ptress."
          end
      | Store t a v =>
          match a with
          | DVALUE_Base (DVALUE_Pointer a) =>
              write_dvalue t a v
          | _ => mub "Writing something to somewhere that isn't an address."
          end
      end.

  (** ** Memory-sensitive intrinsics *)
  
  (** Malloc *)
  Definition malloc_bytes (init_bytes : list memory_byte) (align : N) : memM ptr :=
    pr <- fresh_prov;;
    malloc_bytes_with_pr init_bytes align pr.

  (** Handle memcpy *)
  Definition memcpy (src dst : ptr) (size : N) (volatile : bool) : memM unit :=
    (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
           memory from the source location to the destination location, which
           must either be equal or non-overlapping. *)
    
    if orb (no_overlap dst size src size)
         (Z.eqb (ptr_to_int src) (ptr_to_int dst))
    then 
      src_bytes <- read_bytes src size;;
      (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
      write_bytes dst src_bytes
    else
      mub "memcpy with overlapping or non-equal src and dst memory locations.".

  (** memset spec *)
  Definition memset
    (dst : ptr) (val : int8) (len : Z) (volatile : bool) : memM unit :=
    if Z.ltb len 0
    then
      mub "memset given negative length."
    else
      let byte := MByte (DVALUE_I 8 val) (DTYPE_I 8) 0 in
      write_bytes dst (repeatN (Z.to_N len) byte).
  
  Definition handle_memcpy (args : list dvalue_base) : memM unit :=
    match args with
    | DVALUE_Pointer dst ::
        DVALUE_Pointer src ::
        DVALUE_I sz size ::
        DVALUE_I _ volatile :: [] (* volatile ignored *)  =>
        memcpy src dst (Z.to_N (unsigned size)) (equ volatile VellvmIntegers.one)
    | DVALUE_Pointer dst ::
        DVALUE_Pointer src ::
        DVALUE_Iptr size ::
        DVALUE_I _ volatile :: [] (* volatile ignored *)  =>
        memcpy src dst (Z.to_N (to_Z size)) (equ volatile VellvmIntegers.one)
    | _ => merr "Unsupported arguments to memcpy."
    end.
  
  Definition handle_memset (args : list dvalue_base) : memM unit.
    refine
      (match args with
       | DVALUE_Pointer dst ::
           DVALUE_I sz_val val ::
           DVALUE_I sz_len len ::
           DVALUE_I sz_vol volatile :: [] (* volatile ignored *)  =>
           _
       | _ => merr "Unsupported arguments to memset."
       end).

    destruct (Pos.eq_dec sz_val 8); subst.
    - exact
        (memset dst val (unsigned len) (equ volatile VellvmIntegers.one)).
    - exact (merr "Unsupported arguments to memset.").
  Defined. 

  Definition handle_malloc (args : list dvalue_base) (align : N) : memM ptr :=
    match args with
    | [DVALUE_I bitwidth sz] =>
        malloc_bytes (generate_num_poison_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8)) align
    | [DVALUE_Iptr sz] =>
        malloc_bytes (generate_num_poison_bytes (Z.to_N (to_unsigned sz)) (DTYPE_I 8)) align
    | _ => merr "Malloc: invalid arguments."
    end.

  Definition handle_free (args : list dvalue_base) : memM unit :=
    match args with
    | [DVALUE_Pointer ptr] => free ptr
    | _ => merr "Free: invalid arguments."
    end.

  Definition NONE := DVALUE_Base DVALUE_None.
  
  Definition handle_intrinsicM : IntrinsicE ~> memM :=
    fun T e =>
      match e with
      | Intrinsic t name args _ =>
          args' <- lift (map_monad dvalue_to_dvalue_base args) ;;
          (* Pick all arguments, they should all be unique. *)
          (* TODO: add more variants to memcpy *)
          (* FIXME: use reldec typeclass? *)
          if orb (Rocqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
               (Rocqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
          then
            handle_memcpy args' ;;
            ret (inr NONE)
          else
            if orb (Rocqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                 (Rocqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
            then
              handle_memset args' ;;
              ret (inr NONE)
            else
              if (Rocqlib.proj_sumbool (string_dec name "malloc"))
              then
                (* NOTE: We are defaulting to 64 for now,
                   it should be implemented as the best alignment
                   given the size.
                 *)
                ptr <- handle_malloc args' 8%N;;
                ret (inr (DVALUE_Base (DVALUE_Pointer ptr)))
              else
                if (Rocqlib.proj_sumbool (string_dec name "free"))
                then
                  handle_free args' ;;
                  ret (inr NONE)
                else
                  merr ("Unknown intrinsic: " ++ name)
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
  Definition Frame := list ptr.
  Inductive Framestack : Type :=
  | Singleton (f : Frame)
  | Snoc (s : Framestack) (f : Frame).

  (** ** Heaps *)
  Definition block := list ptr.
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
      state := State ;
      memory_stack := Memory_stack ;
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
  Definition read_byte_raw_mem (mem : memory) (phys_ptr : Z) : option byte :=
    IM.find phys_ptr mem.
  Definition set_byte_raw_mem  (mem : memory) (phys_ptr : Z) (byte : byte) : memory :=
    IM.add phys_ptr byte mem.
  
 (** Add block to memory with a given allocation id *)
  Definition memory_bytes_to_bytes
    (aid : allocationId) (bytes : list memory_byte) : list byte :=
    map (fun b => (b, aid)) bytes.

  (* Register a concrete ptress in a frame *)
  Definition add_to_frame (m : memory_stack) (k : ptr) : memory_stack :=
    let '(mkMemoryStack m s h) := m in
    match s with
    | Singleton f => mkMemoryStack m (Singleton (k :: f)) h
    | Snoc s f => mkMemoryStack m (Snoc s (k :: f)) h
    end.

  (* Register a list of concrete addresses in a frame *)
  Definition add_all_to_frame (ks : list ptr) (m : memory_stack) : memory_stack
    := fold_left (fun ms k => add_to_frame ms k) ks m.

  (* Register a ptr with the heap *)
  Definition add_to_heap (m : memory_stack) (root : ptr) (p : ptr) : memory_stack :=
    let '(mkMemoryStack m s h) := m in
    let h' := add_with (ptr_to_int root) p ret cons h in
    mkMemoryStack m s h'.

  (* Register a list of concrete addresses in the heap *)
  Definition add_all_to_heap' (m : memory_stack) (root : ptr) (ks : list ptr) : memory_stack
    := fold_left (fun ms k => add_to_heap ms root k) ks m.

  Definition add_all_to_heap (ks : list ptr) (m : memory_stack) : memory_stack
    := match ks with
       | [] => m
       | (root :: _) =>
           add_all_to_heap' m root ks
       end.

  Definition get_frame_stack : memM Framestack :=
    s <- get ;;
    ret (Memory_stack_frame_stack (state_get_memory s)).
  Definition get_frame : memM Frame :=
    fs <- get_frame_stack ;;
    match fs with
    | Singleton f | Snoc _ f => ret f
    end. 
  Definition get_mem : memM memory :=
    s <- get ;;
    ret (Memory_stack_memory (state_get_memory s)).
  Definition get_framestack : memM Framestack :=
    s <- get ;;
    ret (Memory_stack_frame_stack (state_get_memory s)).
  Definition get_provenance : memM provenance :=
    s <- get ;;
    ret (state_get_provenance s).
  Definition get_heap : memM heap :=
    s <- get ;;
    ret (Memory_stack_heap (state_get_memory s)).
  Definition app_provenance (f : provenance -> provenance) : memM unit :=
    s <- get ;;
    put {| state_memory_stack := s.(state_memory_stack) ;
          state_provenance := f s.(state_provenance) |}.
   Definition app_state (f : state -> state) : memM unit :=
    s <- get ;;
    put (f s). 
  Definition app_mem_stack (f : Memory_stack -> Memory_stack) : memM unit :=
    s <- get ;;
    put {| state_memory_stack := f s.(state_memory_stack) ;
          state_provenance := state_provenance s |}.
  Definition upd_provenance (p : provenance) : memM unit := app_provenance (fun _ => p).
  Definition upd_mem_stack (m : Memory_stack) : memM unit := app_mem_stack (fun _ => m).
  Definition app_mem (f : memory -> memory) : memM unit :=
    s <- get ;;
    put {| state_memory_stack :=
             {| Memory_stack_memory     := f s.(state_memory_stack).(Memory_stack_memory) ;
               Memory_stack_frame_stack := s.(state_memory_stack).(Memory_stack_frame_stack);
               Memory_stack_heap        := s.(state_memory_stack).(Memory_stack_heap)
             |};
           state_provenance := state_provenance s |}.
  Definition upd_mem (m : memory) : memM unit := app_mem (fun _ => m).
  Definition app_heap (f : heap -> heap) : memM unit :=
    s <- get ;;
    put {| state_memory_stack :=
             {| Memory_stack_memory     := s.(state_memory_stack).(Memory_stack_memory) ;
               Memory_stack_frame_stack := s.(state_memory_stack).(Memory_stack_frame_stack);
               Memory_stack_heap        := f s.(state_memory_stack).(Memory_stack_heap)
             |};
           state_provenance := state_provenance s |}.
  Definition upd_heap (h : heap) : memM unit := app_heap (fun _ => h).
  Definition app_frame_stack (f : Framestack -> Framestack) : memM unit :=
    s <- get ;;
    put {| state_memory_stack :=
               {| Memory_stack_memory     := s.(state_memory_stack).(Memory_stack_memory) ;
                 Memory_stack_frame_stack := f s.(state_memory_stack).(Memory_stack_frame_stack);
                 Memory_stack_heap        := s.(state_memory_stack).(Memory_stack_heap)
               |};
             state_provenance := state_provenance s |}.
  Definition upd_frame_stack (fs : Framestack) : memM unit := app_frame_stack (fun _ => fs).
  Definition app_frame_stack_eob : (Framestack -> EOU Framestack) -> memM unit :=
    fun f =>
      fs <- get_framestack ;;
      f' <- lift (f fs) ;;
      upd_frame_stack f'.
  
  Definition push_frame_stack (f : Frame) (fs : Framestack) : Framestack :=
    Snoc fs f.
  Definition pop_frame_stack (fs : Framestack) : EOU Framestack :=
    match fs with
    | Singleton f => raise_error "Last frame, cannot pop."%string
    | Snoc s f => ret s
    end.

  Definition read_byte_raw (msg : string) (phys_ptr : Z) : memM byte :=
    s <- get ;;
    match read_byte_raw_mem (Memory_stack_memory (state_get_memory s)) phys_ptr with
    | Some b => ret b
    | None => Mub msg
    end.
  
  Definition set_byte_raw (phys_addr : Z) (byte : byte) : memM unit :=
    m <- get_mem ;;
    upd_mem (set_byte_raw_mem m phys_addr byte).

  (** Add block to memory with a given allocation id *)
  Definition add_block (aid : allocationId) (p : ptr)
    (ptrs : list ptr) (init_bytes : list memory_byte) : memM unit :=
    let mem_bytes := memory_bytes_to_bytes aid init_bytes in
    m <- get_mem;;
    upd_mem (add_all_index mem_bytes (ptr_to_int p) m).

  (** Add pointers to the stack frame *)
  Definition add_ptrs_to_frame (ptrs : list ptr) : memM unit :=
    app_mem_stack (add_all_to_frame ptrs).
  
  Definition add_ptrs_to_heap (ptrs : list ptr) : memM unit :=
    app_mem_stack (add_all_to_heap ptrs).
 
  (** Add a block of bytes to memory, and register it in the current stack frame. *)
  Definition add_block_to_stack (aid : allocationId) (p : ptr)
    (ptrs : list ptr) (init_bytes : list memory_byte) : memM unit :=
    add_block aid p ptrs init_bytes;;
    add_ptrs_to_frame ptrs.

  (** Add a block of bytes to memory, and register it in the heap. *)
  (* Should we make sure ptr (the root) is added even if ptrs is empty? *)
  Definition add_block_to_heap (aid : allocationId) (p : ptr)
    (ptrs : list ptr) (init_bytes : list memory_byte) : memM unit :=
    add_block aid p ptrs init_bytes;;
    add_ptrs_to_heap ptrs.

  Definition Read_byte (p : ptr) : memM memory_byte :=
    let addr := ptr_to_int p in
    let pr := ptr_provenance p in
    '(byte,aid) <- read_byte_raw "Reading from unallocated memory." addr;;
    if access_allowed pr aid
    then ret byte
    else mub ("Read from memory with invalid provenance").

  (** Writes *)
  Definition Write_byte (p : ptr) (byte : memory_byte) : memM unit :=
    let addr := ptr_to_int p in
    let pr := ptr_provenance p in
    '(_,aid) <- read_byte_raw "Writing to unallocated memory" addr ;;
    if access_allowed pr aid
    then set_byte_raw addr (byte,aid)
    else mub "Trying to write to memory with invalid provenance".

  Definition get_free_block (size : N) (align : N) (pr : provenance) : memM (ptr * list ptr) :=
    let aid := provenance_to_allocation_id pr in
    addr <- next_key size align ;;
    ptr <- lift (int_to_ptr addr (allocation_id_to_prov aid)) ;;
    ptrs <- lift (get_consecutive_ptrs ptr size);;
    ret (ptr,ptrs).

  Definition Allocate_bytes_with_pr (init_bytes : list memory_byte) (align : N) (pr : provenance) : memM ptr :=
    let size := N.length init_bytes in
    let aid := provenance_to_allocation_id pr in
    '(ptr, ptrs) <- get_free_block size align pr;;
    add_block_to_stack aid ptr ptrs init_bytes;;
    ret ptr.

  (** Heap allocation *)
  Definition Malloc_bytes_with_pr (init_bytes : list memory_byte) (align : N) (pr : provenance) : memM ptr :=
    let size := N.length init_bytes in
    let aid := provenance_to_allocation_id pr in
    '(ptr, ptrs) <- get_free_block size align pr;;
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

  Definition free_block_memory (b : block) (m : memory) : memory :=
    fold_left (fun m key => free_byte (ptr_to_int key) m) b m.

  Definition Free (p : ptr) : memM unit :=
    let raw_addr := ptr_to_int p in
    h <- get_heap ;;
    match lookup raw_addr h with
    | None => mub "Attempt to free non-heap allocated address."
    | Some block =>
        let h' := delete raw_addr h in
        app_mem (free_block_memory block);;
        upd_heap h'
    end.
  
  Instance MemoryModelPrimitivesV : @MemoryModelPrimitives Pa :=
    {|
      mm_state := MemoryModelStateV ;
      read_byte := Read_byte ;
      write_byte := Write_byte ;
      allocate_bytes_with_pr := Allocate_bytes_with_pr ;
      malloc_bytes_with_pr := Malloc_bytes_with_pr ;
      mempush := Mempush ;
      mempop := Mempop ;
      free := Free
    |}.
  
End Implementation.


