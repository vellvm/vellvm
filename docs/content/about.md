---
title: "About"
---


# The LLVM Intermediate Representation

LLVM IR is a programming language used as a compiler [intermediate representation](https://en.wikipedia.org/wiki/Intermediate_representation) that sits in between high-level source languages (like C or Rust) and low-level machine code as executed on actual processors (like x86, arm, or RISC-V).  It is widely used in industry via the [Clang](https://clang.llvm.org/) C compiler, but features in numerous other projects.

The "informal" specification of LLVM IR programs is described by the [LLVM Language Reference Manual (LangRef)](https://llvm.org/docs/LangRef.html).  This document explains what LLVM IR code can and cannot do, which, in turn, informs programmers and compiler implementors about how to write their code. However, **the LLVM IR spec is complicated!** It can have bugs and inconsistencies.  Those can lead to program crashes, security vulnerabilities, or performance problems in real-world code.


See the [example below]({{< ref "#example" >}}) for a taste of the LLVM IR's subtleties.



# Vellvm

### Formal Specification

Vellvm is a _formal specification_ for the semantics of LLVM IR.  As such, it aims to give a machine-represented *mathematical model* of the details described in LangRef.  Vellvm describes what behaviors are permitted by and expected of LLVM IR code. 

The Vellvm specification is code implemented in the [Rocq](https://rocq-prover.org) interactive theorem prover. In practice, it consists of a collection of Rocq datatypes, functions, and propositions that characterize the sets of possible behaviors of LLVM IR programs.  Since LLVM IR programs can do quite complicated things (they are nondeterministic, have complex memory operations, and interface with external code), describing these behaviors precisely and in a useful form is highly non-trivial.

See more details, see the [structure of the formalism.](/vellvm/structure/)

### Behavioral Refinement 

The Vellvm specification also includes the notion of a _refinement_, which is a mathematical definition of what it means for one LLVM IR program to correctly _implement_ the "same" behavior as another one. Due to nondeterminism in the semantics, there may be more than one allowed refinement.

This definition says what it means for an _implementation_ of the LLVM IR spec (e.g. the one provided by [llc](https://llvm.org/docs/CommandGuide/llc.html)) to be correct. It also says what program optimizations and other transformations are allowed to do. A correct program transformation must always yield a refinement of the source.

Vellvm provides a mathematical framework in Rocq for defining and proving properties about such refinements.

### Executable interpreter 

Vellvm also includes an [executable interpreter](/vellvm/tests) that is itself proved to be a refinement of the spec and therefore a valid implementation.  The interpeter is useful for comparing Vellvm's semantics to other implementations of the LLVM IR, and it can be used to find bugs by differential testing via tools like [Csmith](https://github.com/csmith-project/csmith) or [yarpgen](https://github.com/intel/yarpgen).

Although it doesn't (yet!) rise to the level of a [_reference implementation_](https://en.wikipedia.org/wiki/Reference_implementation)--the LLVM IR still has many dark corners and under-specified operations--Vellvm's interpeter and semantics goes a long way towards clarifying the behavior of LLVM IR programs.

## Applications

Given the above, Vellvm can be (and has been!) used to:

- Find bugs in Clang and other LLVM IR-based compilers.

- Uncover inconsistencies in the LangRef specification (which can lead to bugs or confusion)

- Prove properties about compiler analyses and optimizations

- Construct verified compilers in the same vein as [CompCert](https://compcert.org/) or [CakeML](https://cakeml.org/). 

- Implement domain specific languages in Rocq. 

- Serve as a playground for experimenting with alternate LLVM IR semantics

- Try out programming languages theory on thorny semantic models

We have explored many of these applications in our [research projects](/vellvm/research/), but there are many more applications to explore.

# Example 

As a small example of the complexity of LLVM IR semantics, consider the following program snippet of code that "simply" adds 17 to the 32-bit integer `%x` and names the result `%sum`.

```llvm
%sum = add i32 %x, 17
```

Even this tiny example has many subtleties:

 - If `%x` is close to the maximum 32-bit integer value, the result might overflow and the semantics needs to specify whether the arithmetic "wraps" or triggers an error.  (Here,  the result wraps around and the answer will be taken mod 2^32.)
 
 - A programmer could use a "no unsigned wrap" flag, `nuw`, to indicate that such overflows should instead trigger an error, in which case `%sum` will get the (so-called) `poison` value when an overflow occurs. LLVM IR uses `poison` to indicate _deferred_ undefined behavior, which is useful for reasoning about the refinement of program optimizations.

 - However, since LLVM IR supports `poison` values, it also needs to say what happens if the input `%x` is `poison`, regardless of whether the addition overflows and even when there is no `nuw` flag. If `%x` is `poison` then the result `%sum` is also `poison`.

 - This is just a piece of the story, because LLVM IR also supports the `undef` value, which stands for a [_set_ of possible results](https://llvm.org/docs/LangRef.html#undefined-values).  This means that the `add` operation has to be defined when one or both of its arguments is `undef`. If `%x` is fully `undef` then `%sum` will also be `undef`, but other cases must also be considered... For example, if `add i32 %x, %x` may not be a multiple of `2` if `%x` is `undef`!

This is just one taste of the complexities of LLVM IR. The LLVM IR computation model hides many other low-level implementation details, such as the precise addresses of data stored in memory and the exact implementation of functions calls, but it also exposes other low-level features, such as the ability to cast between pointer values and integers (via `inttoptr` and `ptrtoint`). 


