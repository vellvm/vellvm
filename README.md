# Vellvm
[![Build Status](https://travis-ci.com/vellvm/vellvm.svg?branch=master)](https://travis-ci.com/vellvm/vellvm)

Vellvm is a Coq formalization of the semantics of (a subset of) the
LLVM compiler IR that is intended for _formal verification_ of
LLVM-based software.  It is being developed at the
University of Pennsylvania as part of the DeepSpec project.

### See:
 - [Vellvm](http://www.cis.upenn.edu/~stevez/vellvm/)
 - [DeepSpec](http://deepspec.org)
 - [LLVM](http://llvm.org)

# Participants
 - Steve Zdancewic
 - Yannick Zakowski
 - Calvin Beck
 - Olek Gierczak

## Past Contributors
 - Vivien Durey 
 - Dmitri Garbuzov 
 - William Mansky
 - Milo Martin
 - Santosh Nagarakatte 
 - Emmett Neyman 
 - Christine Rizkallah 
 - Robert Zajac
 - Richard Zhang 
 - Jianzhou Zhao

---

# Structure of the repository

/src/ci   - travis configuration

/src/coq  - Coq formalization (see StepSemantics.v)

/src/ml   - OCaml glue code for working with ollvm

/src/ml/extracted - OCaml code extracted from the files in /src/coq directory

/src/doc - coqdoq  [not useful yet]

/lib  - for 3rd party libraries [as git submodules]

/tests - various LLVM source code tests

# Installing / Compiling Vellvm

### Assumes: 
  - coqc   : version 8.8.0   (and coqdep, etc.)
  - Coq packages: 
    - ext-lib    (installed via, e.g. opam install coq-ext-lib)
    - paco       (installed via, e.g. opam install coq-paco)
    - flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    - itree      (installed via, e.g. opam install coq-itree)
- ocamlc : version 4.04    (probably works with 4.03 or later)
  - OPAM packages: dune, menhir, [optional: llvm  (for llvm v. 3.8)]

Compilation:

1. clone the vellvm git repo with `--recurse-submodule` option (`git clone --recurse-submodules`)
2. run `make` in the /src directory

# Running

Do `src/vellvm -help` from the command line.

Try `src/vellvm -interpret tests/ll/factorial.ll`.


# Notes

### coq-flocq

On some OSX configurations the opam installation for coq-flocq fails with a
permissions error `# Failed to create server: Operation not permitted` caused by
opam's sandboxing scripts.  The solution is to temporarily disable opam's
sandboxing by editing ~/.opam/config to remove the lines having to do with
`wrap-*-commands:`.

