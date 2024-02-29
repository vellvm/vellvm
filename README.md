# Introduction

This is the implementation of our memory model and LLVM semantics. The
relevant theorems and definitions are linked to in the
`paper-theorems.org` file.

## Compilation:

Compilation is done by running `make` in the `src/` directory. The
following versions of things should be used to compile the project
with coq 8.19:

>     - install   ocamlbuild             0.14.3
>     - install   conf-g++               1.0
>     - install   conf-bash              1             [required by base]
>     - install   coq-ext-lib            0.12.0
>     - install   menhirSdk              20231231
>     - install   easy-format            1.3.4
>     - install   menhirLib              20231231
>     - install   coq-ceres              0.4.1
>     - install   re                     1.11.0
>     - install   menhirCST              20231231
>     - install   ounit2                 2.2.7
>     - install   coq-paco               4.2.0
>     - install   qcheck-core            0.21.3
>     - install   camlp-streams          5.0.1
>     - install   coq-flocq              4.1.4
>     - recompile base                   v0.16.3       [upstream or system changes]
>     - install   coq-simple-io          1.8.0
>     - install   menhir                 20231231
>     - install   coq-itree              5.1.2
>     - install   qcheck-ounit           0.21.3
>     - install   biniou                 1.2.2
>     - recompile ppx_sexp_conv          v0.16.0       [uses base]
>     - recompile ppx_compare            v0.16.0       [uses base]
>     - install   atd                    2.15.0
>     - install   qcheck                 0.21.3
>     - install   atdgen-runtime         2.15.0
>     - recompile ppx_hash               v0.16.0       [uses base]
>     - install   atdts                  2.15.0
>     - install   atdgen                 2.15.0
>     - recompile coq-serapi             8.19.0+0.19.0 [uses ppx_compare, ppx_sexp_conv]
>     - install   elpi                   1.18.2
>     - install   coq-elpi               2.0.2
>     - install   coq-hierarchy-builder  1.7.0
>     - install   coq-mathcomp-ssreflect 2.2.0
>     - install   coq-quickchick         2.0.2

Compilation takes a long time, and it is picky about dependencies. If
you have used nix before consider looking at `nix.org` for details.

# Running TwoPhase

The executable `twophase` will be found in `src/`.
Do `src/twophase -help` from the command line to see all available options.
In particular:
- `src/twophase -interpret tests/ll/factorial.ll` to run the interpreter on a given file.
- `cd src && ./twophase -test` to run the test suite against clang
- `src/twophase -test-file tests/ll/gep2.ll` to test a specific file using inlined assertions
