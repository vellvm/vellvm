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
(* TODO: MemoryModelPrimitives feels fairly reasonable, but what is exposed
   in MemoryModelState feels quite random.
 *)
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

Section MemM.
  Context {Pa : Params} {MMS : @MemoryModelState Pa}.

  Definition memM := memS state addr provenance.

  Definition get_state  : memM state := fun s => ret (s,s).
  Definition get_memory : memM memory_stack := fun s => ret (s, state_get_memory s).

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
    allocate_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

    (** Heap operations *)
    malloc_bytes_with_pr : list memory_byte -> provenance -> memM addr ;

    (** Frame stacks *)
    mempush : memM unit ;
    mempop  : memM unit ;

  }.
