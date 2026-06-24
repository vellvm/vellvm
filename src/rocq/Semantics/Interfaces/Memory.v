Require Import Morphisms.

From Vellvm Require Import
  Numeric
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
  EOU
  VellvmIntegers
  Params
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

Inductive memS {S A P : Type} (X : Type) : Type :=
| Mret (x : X) : memS X
| Moom (s : string) : memS X
| Mub  (s : string) : memS X
| Merr (s : string) : memS X
| Mget (k : S -> memS X) : memS X
| Mput (σ : S) (k : memS X) : memS X
(* | Mfresh_addr (k : A -> memS X) : memS X *)
| Mnext_key (k : Z -> memS X) : memS X
| Mfresh_prov (k : P -> memS X) : memS X.

Arguments memS : clear implicits.
Arguments Moom {S A P} [X].
Arguments Mub  {S A P} [X].
Arguments Merr {S A P} [X].
Arguments Mget {S A P} [X].
Arguments Mput {S A P} [X].
(* Arguments Mfresh_addr {S A P} [X]. *)
Arguments Mnext_key {S A P} [X].
Arguments Mfresh_prov {S A P} [X].
Fixpoint memS_bind {S A P X Y} (c : memS S A P X) (k : X -> memS S A P Y) : memS S A P Y :=
  match c with
  | Mret x => k x
  | Moom s => Moom s
  | Mub s => Mub s
  | Merr s => Merr s
  | Mget g => Mget (fun σ => memS_bind (g σ) k)
  | Mput σ g => Mput σ (memS_bind g k)
  (* | Mfresh_addr g => Mfresh_addr (fun a => memS_bind (g a) k) *)
  | Mnext_key g => Mnext_key (fun a => memS_bind (g a) k)
  | Mfresh_prov g => Mfresh_prov (fun a => memS_bind (g a) k)
  end.

#[global] Instance memS_mon {S A P} : Monad (memS S A P) :=
  {| ret _ x := Mret x ;
    bind _ _ c k := memS_bind c k |}.

(* Definition memS S A P := stateT S (memB S A P). *)
Definition lift {S A P} : EOU ~> memS S A P :=
  fun _ c => match c with
          | raise_ret x => ret x
          | raise_oom s   => Moom s
          | raise_ub s    => Mub  s
          | raise_error s => Merr s
          end.
Definition mub        {S A P X} s : memS S A P X := Mub s.
Definition merr       {S A P X} s : memS S A P X := Merr s.
Definition moom       {S A P X} s : memS S A P X := Moom s.
Definition put {S A P} (σ: S) : memS S A P unit := Mput σ (ret tt).
Definition get {S A P}  : memS S A P S := Mget (fun σ => ret σ).
Definition next_key {S A P} : memS S A P Z := Mnext_key (fun a => ret a). 
Definition fresh_prov {S A P} : memS S A P P := Mfresh_prov (fun p => ret p). 

(*** Internal state of memory *)
(* TODO: MemoryModelPrimitives feels fairly reasonable, but what is exposed
   in MemoryModelState feels quite random.
 *)
Class MemoryModelState {Pa : Params} :=
  {
    
    state        : Type;
    memory_stack : Type;
    (* Type for frames and frame stacks *)
    frame        : Type;
    framestack   : Type;
    (* Heaps *)
    heap         : Type;
    
    (* Accessors *)
    state_get_memory        : state -> memory_stack;
    state_get_provenance    : state -> provenance;
    memory_stack_framestack : memory_stack -> framestack;
    memory_stack_heap       : memory_stack -> heap;

    (* Update *)
    state_put_memory        : state -> memory_stack -> state;

    (* Initial state *)
    initial_state           : state;
    initial_frame           : frame;
    initial_heap            : heap;

  }.

Section MemM.
  Context {Pa : Params} {MMS : @MemoryModelState Pa}.

  Definition memM := memS state addr provenance.

  (* Definition get_state  : memM state := fun s => ret (s,s). *)
  (* Definition get_memory : memM memory_stack := fun s => ret (s, state_get_memory s). *)

End MemM.

(*** Primitives on memory *)
Class MemoryModelPrimitives {Pa : Params} :=
  {
    mm_state :: @MemoryModelState Pa ;

    (** Reads *)
    read_byte : addr -> memM memory_byte ;

    (** Writes *)
    write_byte : addr -> memory_byte -> memM unit ;

    (** Stack allocations *)
    (* TODO: The list of bytes get huge in practice when allocating big chunk of memory.
       For performance reasons, it might be better to take a different representation here
       ([Fin n -> memory_byte] for [n] the length of the list?)
     *)
    allocate_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

    (** Heap operations *)
    malloc_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

    (* The free intrinsics is implementation specific to avoid exposing
       in the interface both the lookup from heap to blocs, and an iterator
       over them. TODO: rethink if we are happy with it.
     *)
    free : addr -> memM unit ;
      
    (** Frame stacks *)
    mempush : memM unit ;
    mempop  : memM unit ;

  }.
