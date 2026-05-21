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

From Vellvm.Semantics Require Import
  DynamicValues
  VellvmIntegers
  Params
  LLVMEvents
  Operations.

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

From Stdlib Require Import FunctionalExtensionality.
Import Logic.

Open Scope Z.

Inductive memB {S A P : Type} (X : Type) : Type :=
| Mret (x : X) : memB X
| Moom (s : string) : memB X
| Mub  (s : string) : memB X
| Merr (s : string) : memB X
| Mfresh_addr (σ : S) (k : A -> memB X) : memB X
| Mfresh_prov (σ : S) (k : P -> memB X) : memB X.

Arguments memB : clear implicits.
Arguments Moom {S A P} [X].
Arguments Mub  {S A P} [X].
Arguments Merr {S A P} [X].
Arguments Mfresh_addr {S A P} [X].
Arguments Mfresh_prov {S A P} [X].
Fixpoint memB_bind {S A P X Y} (c : memB S A P X) (k : X -> memB S A P Y) : memB S A P Y :=
  match c with
  | Mret x => k x
  | Moom s => Moom s
  | Mub s => Mub s
  | Merr s => Merr s
  | Mfresh_addr σ g => Mfresh_addr σ (fun a => memB_bind (g a) k)
  | Mfresh_prov σ g => Mfresh_prov σ (fun a => memB_bind (g a) k)
  end.

#[global] Instance memB_mon {S A P} : Monad (memB S A P) :=
  {| ret _ x := Mret x ;
    bind _ _ c k := memB_bind c k |}.

Definition memS S A P := stateT S (memB S A P).
Definition lift {S A P} : EOB ~> memS S A P :=
  fun _ c => match c with
          | raise_ret x => ret x
          | raise_oom s   => fun σ => Moom s
          | raise_ub s    => fun σ => Mub  s
          | raise_error s => fun σ => Merr s
          end.
Definition mub        {S A P X} s : memS S A P X := fun σ => Mub s.
Definition merr       {S A P X} s : memS S A P X := fun σ => Merr s.
Definition moom       {S A P X} s : memS S A P X := fun σ => Moom s.
Definition fresh_addr {S A P}     : memS S A P A := fun σ => Mfresh_addr σ (fun a => ret (σ,a)). 
Definition fresh_prov {S A P}     : memS S A P P := fun σ => Mfresh_prov σ (fun p => ret (σ,p)). 

(*** Internal state of memory *)
Class MemoryModelState {Pa : Params} :=
  {
    
    memory_stack : Type;
    state : Type;
    (* Type for frames and frame stacks *)
    frame : Type;
    framestack : Type;
    (* Heaps *)
    heap : Type;
    
    (* Accessors *)
    state_get_memory : state -> memory_stack;
    state_get_provenance : state -> provenance;
    memory_stack_framestack : memory_stack -> framestack;
    memory_stack_heap : memory_stack -> heap;

    (* Update *)
    state_put_memory : state -> memory_stack -> state;

    (* Initial state *)
    initial_state : state;
    initial_frame : frame;
    initial_heap : heap;

  }.

Definition memM {Pa : Params} {MMS : @MemoryModelState Pa} :=
  memS state addr provenance.

(*** Primitives on memory *)
Class MemoryModelPrimitives {Pa : Params} :=
  {
    mm_state :: @MemoryModelState Pa ;

    (** Reads *)
    read_byte : addr -> memM memory_byte ;

    (** Writes *)
    write_byte : addr -> memory_byte -> memM unit ;

    (** Stack allocations *)
    allocate_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

    (** Heap operations *)
    malloc_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

  }.

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
  Definition memcpy (src dst : addr) (len : Z) (volatile : bool) : memM unit.
    refine (if Z.ltb len 0
            then
              mub "memcpy given negative length."
            else
              (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
           memory from the source location to the destination location, which
           must either be equal or non-overlapping. *)
              
        if orb (no_overlap dst len src len)
               (Z.eqb (ptr_to_int src) (ptr_to_int dst))
        then _ else _).
    (*       src_bytes <- read_bytes src (Z.to_nat len);; *)

    (*       (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *) *)
    (*       write_bytes dst src_bytes *)
    (*     else *)
    (*       raise_ub "memcpy with overlapping or non-equal src and dst memory locations.". *)

    (* (** memset spec *) *)
    (* Definition memset `{MemMonad MemM (itree Eff)} *)
    (*   (dst : addr) (val : int8) (len : Z) (sid : store_id) (volatile : bool) : MemM unit := *)
    (*   if Z.ltb len 0 *)
    (*   then *)
    (*     raise_ub "memset given negative length." *)
    (*   else *)
    (*     let byte := uvalue_sbyte (@UVALUE_I 8 val) (DTYPE_I 8) 0 sid in *)
    (*     write_bytes dst (repeatN (Z.to_N len) byte). *)


End MemoryModelPrimitives.
