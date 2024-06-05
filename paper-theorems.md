# Introduction

**Note:** This markdown file is a copy of `paper-theorems.org`. This
file is provided for completeness, but the org-mode file may be
preferable as it contains direct links to lines within the files.

This file maps some of the important definitions and lemmas to the
actual development. It is worth noting that some of the names have
changed in the paper for clarity, and some of the definitions have been
simplified and specialized within the paper as well.

The bulk of the memory model itself is contained within:

-   [file:src/coq/Handlers/MemoryModel.v](src/coq/Handlers/MemoryModel.v)
-   [file:src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   [file:src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v](src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v)
-   [file:src/coq/Handlers/MemoryModelImplementation.v](src/coq/Handlers/MemoryModelImplementation.v)

The refinement relations between infinite and finite memory models are
contained in:

-   [file:src/coq/Semantics/InfiniteToFinite/Conversions/BaseConversions.v](src/coq/Semantics/InfiniteToFinite/Conversions/BaseConversions.v)
-   [file:src/coq/Semantics/InfiniteToFinite/Conversions/DvalueConversions.v](src/coq/Semantics/InfiniteToFinite/Conversions/DvalueConversions.v)
-   [file:src/coq/Semantics/InfiniteToFinite/Conversions/EventConversions.v](src/coq/Semantics/InfiniteToFinite/Conversions/EventConversions.v)
-   [file:src/coq/Semantics/InfiniteToFinite/Conversions/TreeConversions.v](src/coq/Semantics/InfiniteToFinite/Conversions/TreeConversions.v)
-   [file:src/coq/Semantics/InfiniteToFinite/LangRefine.v](src/coq/Semantics/InfiniteToFinite/LangRefine.v)
-   [file:src/coq/Semantics/InfiniteToFinite.v](src/coq/Semantics/InfiniteToFinite.v)

Top level refinements and interpreter soundness:

-   [file:src/coq/Theory/Refinement.v](src/coq/Theory/Refinement.v)
-   [file:src/coq/Theory/TopLevelRefinements.v](src/coq/Theory/TopLevelRefinements.v)

Values and semantics:

-   [file:src/coq/Syntax/DynamicTypes.v](src/coq/Syntax/DynamicTypes.v)
-   [file:src/coq/Semantics/DynamicValues.v](src/coq/Semantics/DynamicValues.v)
-   [file:src/coq/Handlers/MemoryModules/FiniteSizeof.v](src/coq/Handlers/MemoryModules/FiniteSizeof.v)
-   [file:src/coq/Semantics/LLVMEvents.v](src/coq/Semantics/LLVMEvents.v)
-   [file:src/coq/Semantics/Denotation.v](src/coq/Semantics/Denotation.v)
-   [file:src/coq/Handlers/Concretization.v](src/coq/Handlers/Concretization.v)
-   [file:src/coq/Semantics/TopLevel.v](src/coq/Semantics/TopLevel.v)

# Section 3

Memory configurations from Figure 2 are defined by `MemState` in
[file:src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v](src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v).
It consists of a high watermark to keep track of the provenance and a
`memory_stack` which contains the actual state of memory.

-   [MemState](src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v)
-   [memory~stack~](src/coq/Handlers/MemoryModules/FiniteSpecPrimitives.v)

The memory itself is represented as a finite IntMap of symbolic bytes
associated with a provenance. The `memory_stack` also contains a stack
and a heap.

## Operations

The operations described in Figure 5 are mapped as follows:

-   find~bk~
    -   [find~freeblock~](src/coq/Handlers/MemoryModel.v)
-   read~b~
    -   [read~bytespecMemPropT~](src/coq/Handlers/MemoryModel.v)
-   write~b~
    -   [write~bytespecMemPropT~](src/coq/Handlers/MemoryModel.v)
-   alloca~post~
    -   [allocate~bytespostconditions~](src/coq/Handlers/MemoryModel.v)
-   malloc~post~
    -   [malloc~bytespostconditions~](src/coq/Handlers/MemoryModel.v)
-   free
    -   [free~specMemPropT~](src/coq/Handlers/MemoryModel.v)
-   pushf
    -   [mempush~specMemPropT~](src/coq/Handlers/MemoryModel.v)
-   popf
    -   [mempop~specMemPropT~](src/coq/Handlers/MemoryModel.v)
-   fresh is called fresh~provenance~ in the development and is a
    parameter of the memory model

## Infinite to finite refinement

This is slightly more involved in the development because the memory
model is parameterized by a memory monad, instead of just using the
Result type directly like in the paper.

-   lifting symbolic bytes from Figure 7
    -   [lift~SByte~](src/coq/Semantics/InfiniteToFinite.v)
-   lifting pointers from Figure 7
    +[fin~toinfaddr~](src/coq/Semantics/InfiniteToFinite/LangRefine.v)
-   lifting memory configurations from Figure 7
    -   [lift~MemState~](src/coq/Semantics/InfiniteToFinite.v)
-   Lemma 3.1 read~bytespec~ refinement
    -   [fin~infreadbytespec~](src/coq/Semantics/InfiniteToFinite.v)

# Section 4

-   Events
    -   [file:src/coq/Semantics/LLVMEvents.v](src/coq/Semantics/LLVMEvents.v)
-   Interpreter levels (Figure 8)
-   [file:src/coq/Theory/Refinement.v](src/coq/Theory/Refinement.v)
-   Values
    -   [Dynamic values (Section
        4.2)](src/coq/Semantics/DynamicValues.v)
    -   [Undef values (Section
        4.2.2)](src/coq/Semantics/DynamicValues.v)
-   Symbolic Bytes
    -   [Symbolic Bytes (Section
        4.2.2)](src/coq/Handlers/MemoryModules/FiniteSizeof.v)
-   Serialization
    -   [serialize~sbytes~](src/coq/Handlers/MemoryModel.v)
-   Deserialization
    -   [deserialize~sbytes~](src/coq/Handlers/MemoryModel.v)

## Section 4.3

Concretization is implemented using a generic monadic function, allowing
it to be used in both the specification and the executable interpreter.

-   Concretization
    -   [concretize~uvalueM~](src/coq/Handlers/Concretization.v)

## Section 4.4

-   Refinement between itrees at the second level of interpretation
    -   [refine~L2~](src/coq/Theory/Refinement.v)
-   Refinement between itrees at the fourth level of interpretation,
    after handling memory and pick events
    -   [refine~L4~](src/coq/Theory/Refinement.v)
-   Refinement after the final level of interpretation of VIR,
    incorporating OOM and UB.
    -   [refine~L6~](src/coq/Theory/Refinement.v)
-   hasUB
    -   [contains~UB~](src/coq/Theory/ContainsUBOriginal.v)
-   eutt~oom~
    -   [refine~OOMh~](src/coq/Handlers/OOM.v)
-   Theorem 4.1, refinement between levels
    -   [refine~01~](src/coq/Theory/TopLevelRefinements.v)
-   Theorem 4.2, transitivity of refinement
    -   [Transitive~refineL6~](src/coq/Theory/Refinement.v)

## Section 4.5

-   Infinite to finite refinement relation
    -   [L0~E1E2oruttstrict~](src/coq/Semantics/InfiniteToFinite/LangRefine.v)
    -   [L1~E1E2oruttstrict~](src/coq/Semantics/InfiniteToFinite/LangRefine.v)
    -   [L2~E1E2oruttstrict~](src/coq/Semantics/InfiniteToFinite/LangRefine.v)
    -   [L6~E1E2oruttstrict~](src/coq/Semantics/InfiniteToFinite.v)
-   orutt
    -   [oruttF](src/coq/Utils/OOMRutt.v)
-   Theorem 4.3 infinite-to-finite top-level refinement
    -   [model~E1E2L6oruttstrictsound~](src/coq/Semantics/InfiniteToFinite.v)

The names of some of these lemmas is a bit more generic in the
development, as opposed to the paper. The `E1E2` part of these lemmas is
in reference to the different event types for the itrees in the
different instantiations of the language. For the purposes of this paper
these will be the infinite / finite instances of the language.

# Section 5

-   optimization examples
    -   [file:src/coq/Theory/OOMRefinementExamples.v](src/coq/Theory/OOMRefinementExamples.v)

# Section 6

-   read~b~^run^ (Figure 11)
    -   [read~byte~](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   write~b~^run^ (Figure 11)
    -   [write~byte~](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   pushf^run^ (Figure 11)
    -   [mempush](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   popf^run^ (Figure 11)
    +[mempop](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   alloca^run^ (Figure 11)
    -   [allocate~bytes~](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   malloc^run^ (Figure 11)
    -   [malloc~bytes~](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   free^run^ (Figure 11)
    -   [free](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)
-   Executable correctness lemma example (Section 6.1.1)
    -   [read~bytecorrect~](src/coq/Handlers/MemoryModules/FiniteExecPrimitives.v)

## Section 6.2

-   Theorem 6.1: Interpreter soundness
    -   [interpreter~sound~](src/coq/Theory/TopLevelRefinements.v)

# Handler correctness

Proofs that handlers for finite LLVM memory events and intrinsics refine
the infinite versions.

-   [handle~loadfininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~loadfininfub~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~storefininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~storefininfub~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~allocafininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~mallocfininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~freespecfininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~freefininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~intrinsicfininf~](src/coq/Semantics/InfiniteToFinite.v)
-   [handle~memcpyfininf~](src/coq/Semantics/InfiniteToFinite.v)

# Notes on differences from the paper

The presentation in the paper has been cleaned up and definitions have
been made more consistent for readability reasons. Some noteworthy
changes include:

-   The paper is more consistent about the terms \"pointer\" and
    \"address\"
    -   In the paper Figure 2 defines a pointer `Ptr` as an address
        `Addr` paired with a provenance `Prov`. The `Addr` type is the
        type of the physical addresses in memory, and will be
        instantiated with either the `Z` type for the infinite memory
        model, or the `int64` type for the finite memory model.
    -   In the development the `Ptr` type is actually called `addr`
        instead.
-   Definitions have been simplified and specialized within the body of
    the paper.
    -   The development provides quite abstract interfaces allowing most
        data structures in memory to be swapped out with other potential
        implementations, as long as they satisfy some properties. For
        instance, Figure 2 defines `Memory` as a finite map from
        physical addresses to bytes (and their associated provenance),
        the development leaves this abstract and gives axiomatic
        specifications for the effects of different operations in the
        `MemoryModelSpecPrimitives`, allowing for a variety of
        implementations. In the executable implementation, however,
        `memory` is defined using finite integer maps in Coq.
-   The implementation makes a distinction between AllocationIds and
    provenances
    -   The concept behind each of these is the same, we just allow for
        different representations in case, for instance, a pointer might
        have additional permissions associated with it.

# Axioms in the development

The proofs of the lemmas rely upon certain classical axioms, proof
irrelevance, and also the \`bisimulation~iseq~\` axiom from the itrees
library. Here we list the assumptions for some of the important theorems
in the development.

## Theorem 4.3: [model~E1E2L6oruttstrictsound~](src/coq/Semantics/InfiniteToFinite.v)

``` coq
Axioms:
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec : forall P : nat -> Prop, (forall n : nat, {P n} + {~ P n}) -> {n : nat | ~ P n} + {forall n : nat, P n}
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
FunctionalExtensionality.functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
EqAxiom.bisimulation_is_eq : forall (E : Type -> Type) (R : Type) (t1 t2 : ITreeDefinition.itree E R), Eqit.eq_itree eq t1 t2 -> t1 = t2
```

## Theorem 6.1: [interpreter~sound~](src/coq/Theory/TopLevelRefinements.v)

``` coq
Axioms:
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec
  : forall P : nat -> Prop,
    (forall n : nat, {P n} + {~ P n}) ->
    {n : nat | ~ P n} + {forall n : nat, P n}
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
EqAxiom.bisimulation_is_eq
  : forall (E : Type -> Type) (R : Type) (t1 t2 : ITreeDefinition.itree E R),
    Eqit.eq_itree eq t1 t2 -> t1 = t2
```

## Lemma 3.1: [fin~infreadbytespec~](src/coq/Semantics/InfiniteToFinite.v)

``` coq
Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
```

## Theorem 4.2: [Transitive~refineL6~](src/coq/Theory/Refinement.v)

``` coq
Axioms:
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
EqAxiom.bisimulation_is_eq
  : forall (E : Type -> Type) (R : Type) (t1 t2 : ITreeDefinition.itree E R),
    Eqit.eq_itree eq t1 t2 -> t1 = t2
```
