---
title: "Structure"
---

# Structure of the development

This description refers to the `dev` branch as of June 10, 2026.

The development is organized as follows.


## Rocq formalization

The core of the project is encompassed by the Rocq formalization of LLVM IR and the proof of its metatheory.
This formalization is entirely contained in the `src/rocq` folder.

More specifically, the following selection of files are among the most important to understand the development:

Syntax, in `src/rocq/Syntax/`
- `LLVMAst.v` the front VIR internal AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`     the VIR internal AST as used for the semantics.

Semantics, in `src/rocq/Semantics/`:
- `DynamicValues.v` definition of the dynamic values and underdefined values.
- `LLVMEvents.v`    inventory of all events.
- `Denotation.v`    definitions of the representation of VIR programs as ITrees.
- `Handlers/`       includes the code for all of the handlers. They are broken up into files based on the nature of the event handled, each file hence corresponding to a subsection.
- `TopLevel.v`      provides the full model and the full interpreter, by plugging all components together.

Theory, in `src/rocq/Theory/`:
- `src/rocq/Utils/PropT.v` metatheory required to reason about sets of itrees, i.e. about the propositional monad transformer.
- `InterpreterMCFG.v`     the layers of interpretation and some of their metatheory
- `InterpreterCFG.v`      the same layers of interpretation and metatheory, but when reasoning about single functions (i.e. single cfg)
- `Refinement.v`          definition of the refinement relations between layers of interpretations
- `TopLevelRefinements.v` proof of inclusion of the refinement relations between layers of interpretations; proof of soundness of the interpreter as described in Section 5
- `DenotationTheory`      Equational theory to reason directly about the structure of vir programs; in particular, reasoning principles about open control-flow-graphs.

## OCaml front-end and driver for execution and testing

On the OCaml side, we provide a parser for legal LLVM IR syntax as well as an
infrastructure to run differential tests between our interpreter and llc.
These unverified parts of the development live in the `src/ml` folder.

- `extracted/Extract.v`    instructions for the extraction of the development to OCaml
- `libvellvm/interpreter.ml`  OCaml driver for running the interpreter; the `step` function walks over the ITree that remains after complete interpretation of the denotation of a program
- `libvellvm/llvm_parser.mly` the parser, adapted from Vellvm,
- `testing/assertion.ml`   custom annotations of llvm programs as comments used to define our tests.
- `main.ml`                top-level from which our executable is obtained.

## Test suite

Our current test-suite of LLVM programs for which we compare our semantics against llc is stored in `tests/`

- `tests/` directory containing the test suite of LLVM IR programs 

See [tests](../tests) for more examples and documentation about using Vellvm for executable testing.
