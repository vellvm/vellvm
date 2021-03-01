# Vellvm
[![Build Status](https://travis-ci.com/vellvm/vellvm.svg?branch=master)](https://travis-ci.com/vellvm/vellvm)

Vellvm is an ongoing project aiming at the formal verification in the Coq proof
assistant of a compilation infrastructure inspired by the LLVM compiler.

As such, its central piece is Verified IR (VIR), a Coq formalization of the
semantics of (a subset of) the LLVM IR that is intended for _formal
verification_ of LLVM-based software. 
It is being developed at the University of Pennsylvania as part of the DeepSpec project.

After VIR, the second component whose development is reaching maturity is the verification of 
a verified front-end for the [Helix](https://github.com/vzaliva/helix) chain of compilation.

### See:
 - [Vellvm](http://www.cis.upenn.edu/~stevez/vellvm/)
 - [DeepSpec](http://deepspec.org)
 - [LLVM](http://llvm.org)

# Participants
 - Steve Zdancewic
 - Yannick Zakowski
 - Calvin Beck
 - Irene Yoon
 
## Past Contributors
 - Vivien Durey 
 - Dmitri Garbuzov 
 - Olek Gierczak
 - William Mansky
 - Milo Martin
 - Santosh Nagarakatte 
 - Emmett Neyman 
 - Christine Rizkallah 
 - Robert Zajac
 - Richard Zhang 
 - Jianzhou Zhao

---

# Structure of the development

The development is organized as follows.

## Local libraries

Stored in the `lib` folder. Currently the only dependency that needs to be installed locally is the itree one:
- `lib/InteractionTrees` contains the version of the ITrees library that we have used in our development. 

The library will be built as the same time as the Vir development via the Makefile.

Although we have made significant contributions to the itree library for the sake of this project, most of it
is orthogonal to the material described in this paper, and can be treated entirely as an external library to understand this project.

The content of Section 5.1 that gives a taste of how the underlying equational theory works can be found in more details in
the files`lib/InteractionTrees/theories/Eq/Eq.v` and `lib/InteractionTrees/theories/Eq/UpToTaus.v`.

## Coq formalization

The core of the project is encompassed by the Coq formalization of LLVM IR and the proof of its metatheory. 
This formalization is entirely contained in the `src/coq` folder. 

More specifically, the following selection of files are among the most important to understand the development:

Syntax, in `src/coq/Syntax/`
- `LLVMAst.v` the front VIR internal AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`     the VIR internal AST as used for the semantics. 

Semantics, in `src/coq/Semantics/`:
- `DynamicValues.v` definition of the dynamic values and underdefined values discussed in Section 2.2.
- `LLVMEvents.v`    inventory of all events as described in Section 4.1.
- `Denotation.v`    definitions of the representation of VIR programs as ITrees as described in Section 4.2.
- `Handlers/`       includes the code for all of the handlers described in Section 4.3. They are broken up into files 
                    based on the nature of the event handled, each file hence corresponding to a subsection.
- `TopLevel.v`      provides the full model and the full interpreter, by plugging all components together, 
                    i.e. the final result of Section 4.4.

Theory, in `src/coq/Theory/`:
- `src/coq/Utils/PropT.v` metatheory required to reason about sets of itrees, i.e. about the propositional monad transformer.
- `InterpreterMCFG.v`     the layers of interpretation shown in Figure 6 and some of their metatheory
- `InterpreterCFG.v`      the same layers of interpretation and metatheory, but when reasoning about single functions (i.e. single cfg)
- `Refinement.v`          definition of the refinement relations between layers of interpretations
- `TopLevelRefinements.v` proof of inclusion of the refinement relations between layers of interpretations;
                          proof of soundness of the interpreter as described in Section 5
- `DenotationTheory`      Equational theory to reason directly about the structure of vir programs;
                          in particular, reasoning principles about open control-flow-graphs.

## OCmal front-end and driver for execution and testing

On the OCaml side, we provide a parser for legal LLVM IR syntax as well as an
infrastructure to run differential tests between our interpreter and llc.
These unverified parts of the development live in the `src/ml` folder.

- `extracted/Extract.v`    instructions for the extraction of the development to OCaml
- `libvir/interpreter.ml`  OCaml driver for running the interpreter; the `step` function 
                                 walks over the ITree that remains after complete interpretation of the denotation of a program
- `libvir/llvm_parser.mly` the parser, adapted from Vellvm, as discussed in Section 4.5.
- `testing/assertion.ml`   custom annotations of llvm programs as comments used to define our tests.
- `main.ml`                top-level from which our executable is obtained.

## Test suite

Our current test-suite of LLVM programs for which we compare our semantics against llc is stored in `tests/`

- `tests/` directory containing the test suite of LLVM IR programs discussed in Section 6

# Installing / Compiling Vir

### Assumes: 
  - coq   : version 8.12 
  - External Coq libraries: 
    * ext-lib    (installed via, e.g. opam install coq-ext-lib)
    * paco       (installed via, e.g. opam install coq-paco)
    * flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    * ceres      (installed via, e.g. opam install coq-ceres)
    * mathcomp   (installed via, e.g. opam install coq-mathcomp-ssreflect)
    * simple-io  (installed via, e.g. opam install coq-simple-io)
    WARNING: you should not have the itree opam package in your switch to avoid conflict with the extended version of the library we provide locally
  - Additional opam packages: 
    * dune       (installed via, e.g. opam install dune)
    * menhir     (installed via, e.g. opam install menhir)
    * qcheck     (installed via, e.g. opam install qcheck)
  - llvm (not required for compiling, only for differential testing)

Compilation:

1. Install all external dependencies
2. Clone the vellvm git repo with the `--recurse-submodule` option
1. Run `make` in the /src directory: it will first compile the itree / quickchick libraries, then vir, and finally extract the OCaml executable

# Running

The executable `vir` will be found in `src/`.
Do `src/vir -help` from the command line to see all available options.
In particular:
- `src/vir -interpret tests/ll/factorial.ll` to run our interpreter on a given file.
- `src/vir --test` to run the test suite against llc
- `src/vir --test-file tests/ll/factorial.ll` to test a specific file against llc



