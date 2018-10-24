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
  - Coq packages: ext-lib    (installed via, e.g. opam install coq-ext-lib)
  - ocamlc : version 4.04    (probably works with 4.02 or later)
  - OPAM packages: ocamlbuild, menhir, [optional: llvm  (for llvm v. 3.8)]

Compilation:

1. clone the vellvm git repo with `--recurse-submodule` option (`git clone --recurse-submodules`)
2. update CompCert submodule to coq 8.7.1 compatible version:
   1. `cd lib/CompCert && git pull origin master`
3. compile 3rd party libraries:
   1. CompCert: `cd lib/Compcert && ./configure x86_64-macosx && make`
   2. Compile Paco: `make -C lib/paco/src`
   3. Compile InteractionTrees
	  - run `make` from the InteractionTrees directory  (do _not_ use `setup.sh`
        since that will clone another copy of paco and we already assume ext-lib exists)
4. run `make` in the /src directory

# Running

Do `src/vellvm -help` from the command line.

Try `src/vellvm -interpret tests/ll/factorial.ll`.
