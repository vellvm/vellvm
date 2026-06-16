---
title: "FAQ"
---

# LLVM Compatibility

## What version of LLVM IR does Vellvm support?

LLVM IR is a rapidly moving target.  Vellvm aims to provide _parsing_ support for all of LLVM IR as of {{}}.  However, the vellvm formal semantics and interpreter may not support all of LLVM IR's features.  See below for more details.

## What features of LLVM IR does Vellvm support?

 Vellvm covers most features of the core *sequential* fragment of LLVM IR as per its informal specification in [LangRef](https://llvm.org/docs/LangRef.html).

 - basic operations on arbitrary bit-width integers
 - doubles, floats, structs, arrays, pointers
 - casts
 - `undef` and `poison`
 - SSA-structured control-flow-graphs
 - global data
 - mutually-recursive functions
 - some intrinsics (in a user-extensible way)

## What about `undef`?

 The Vellvm _semantic model_ currently includes `undef` as a source of nondeterminism, so the meaning of an LLVM IR program is a _set_ of possible behaviors.  The Vellvm _executable interpreter_ currently picks a default value for `undef` depending on its type.

##  What computation features are _not_ supported?
 - full C++-style exceptions via the `landing_pad` and related instructions
 - architecture-specific floatint point values
 - inlined assembly
 - concurrency and concurrency-related instructions

## What about instruction annotations?
 
Many LLVM IR instructions support various annotations (such as `noalias`) that are intended to allow the semantics to trigger **undefined behavior** under certain circumstances.  While Vellvm aims to support as many of these as it can, the set of annotations changes often and the intended meaning can sometimes be unclear, so we try to support them in a _best effort_ but sound way.  (That is, we won't rule a behavior as UB unless it actually is---"true" LLVM IR may exhibit more UB than Vellvm semantics.


## What about libraries?

 Vellvm does not yet provide support for many C standard library functions, but it does support some basics:
 
 - `puts`
 - `printf` 
 - `malloc`
 
 Additionally, any code that can be expressed a an LLVM IR `.ll` file can be linked into the Vellvm interpreter.  See the code in the `src/libll` folder and information about [running tests](../tests) for an example.



# Miscellany

## How do I pronounce "Vellvm"?

It is pronounced like the word "[vellum](https://en.wikipedia.org/wiki/Vellum)".  (Romans wrote the Latin alphabet using the symbol "v" for both "v" and "u"...)
