# Introduction

This is the implementation of our memory model and LLVM semantics. The
relevant theorems and definitions are linked to in the
`paper-theorems.org` file (or `paper-theorems.md`, which has the same
content).

## Build Dependencies

**NOTE:** The VM for the artifact already contains all of the
dependencies. This section **can be skipped** if you are using the
VM. The VM uses nix to handle the dependencies, and nix-direnv is set
up to automatically include dependencies in your shell's path when you
enter the artifact directory. `nix develop .` can be used to
explicitly drop you into a shell with all of the dependencies if
desired, but this shouldn't be necessary.

The project is *picky* about dependencies. If you have used nix before
consider looking at `nix.org` for details. For opam the following
should give you the appropriate versions of all of the dependencies:

```
opam pin add coq 8.19.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

The following versions of things should be used to compile the project
with coq 8.19. If the project does not compile it is likely that you
have an incompatible set of dependencies, and you should install the
versions below:

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

Additionally, some of the tests use `clang` for comparison. The
`clang` version that we compare against is `13.0.1`. The LLVM IR is a
rapidly evolving language, so comparing against a different version of
`clang` may result in more failed tests than expected, for instance
due to changes in the syntax of the language.

## Compilation:

Compilation takes a long time (maybe an hour or so) and a fair amount
of RAM (you should have 16GB available). With the dependencies
installed you should be able to build the project by simply running
the following commands:

```
cd src/
make
```

# Running Vellvm

After compiling the project the executable `vellvm` will be found in `src/`.
Do `src/vellvm -help` from the command line to see all available options.

In particular:
- `src/vellvm -interpret tests/ll/factorial.ll` to run the interpreter on a given file.
- `src/vellvm -test-file tests/ll/gep2.ll` to test a specific file using inlined assertions

## Test Suites

From the `src` directory we can run the test suites. The basic unit test suite can be run with:

```
./vellvm -test-suite
```

Which should run a suite of 152 unit tests for the interpreter which
should all pass. Additionally

```
./vellvm -test
```

Runs a larger suite of assertion based tests from the `../tests/`
directory, as well as pretty printer / parser tests.

The assertions are `.ll` files which contain a comment with an `ASSERT
EQ` statement that specifies the expected return value of a function
when called with specific arguments.

The pretty printer is tested by first running clang on the `.ll` file
to make sure it's a valid LLVM file according to clang (if not we
ignore these, and consider the test a pass, tests may involve
additional vellvm-specific syntax like the `iptr` type we've
added). If it's a valid LLVM file we parse it with vellvm, pretty
print the parsed LLVM AST into an LLVM IR file, and then run `clang`
on it again to ensure that `clang` still recognizes the file.

**NOTE: clang version 13.0.1 is expected for the comparison. Other versions may fail.**

The following error messages from `clang` are expected to show up when
running the pretty-printer test cases:

```
$ ./vellvm -test 
(* -------- Vellvm Test Harness -------- *)
../tests/iptr/iptr.ll:2:15: error: expected type
  %p = alloca iptr
              ^
1 error generated.
../tests/must-fail/float-literal-size.ll:2:14: error: floating point constant invalid for type
  ret float  127.900000000000005684341886080801486968994140625
             ^
1 error generated.
```

The first one is from a test file with the `iptr` syntax we've added,
and the latter is a test case which is expected to fail because of an
invalid floating point literal.

Even more tests from the alive2 test-suite can be run as
follows:

```
./vellvm -enable-srctgt-tests -test
```

(**note**: the order of the flags matters)

Some of these alive2 tests are currently **expected to fail**. The
alive2 test suite compares a `src` function to a `tgt` function, where
the `tgt` function is expected to be a refinement of the `src`
function. We execute these tests by randomly generating arguments to
the `src` and `tgt` functions and then comparing their outputs. This
approach is, unfortunately, not valid for the alive2 test cases which
are not executable --- for instance there are test cases where the
`src` functions contain `undef` and the `tgt` function returns a
completely arbitrary value, our executable implementation will not
explore all possible choices for the `undef` value, so we cannot
determine that `tgt`is a refinement of `src` automatically. We have
already disabled some of these alive2 tests, as well as some which use
datatypes, operations, and datalayouts (e.g., big endian layouts) that
are unsupported in vellvm. Furthermore, our test-case generator is
under active development and currently does not handle some tricky
cases fully, like pointer arguments to `src` and `tgt`, so test cases
are expected to fail as a result of this as well. The number of
failing tests varies for each run due to the random generation, but
roughly 52 tests are expected to fail.

# Structure of the development

The `paper-theorems.org`file maps the theorems in the paper to the
theorems in the development, but for the curious this section will
describe the overall structure of the project.

Within the `src/` directory the main important directories are

- `src/coq/`
- `src/ml/`

The `src/coq/` directory contains the bulk of the development as well
as the lemmas presented in the paper along with their proofs. The
`src/ml/` directory contains the `ocaml` portion of the executable
interpreter. The executable interpreter itself is extracted from the
Coq development, but the `ocaml` code is used to implement the command
line executable, LLVM IR parser, and the test framework is implemented
in the `ocaml` code as well.

## The Coq development

The Coq development itself is broken up into a few important files and directories.

Syntax, in `src/coq/Syntax/`
- `LLVMAst.v` the front VIR internal AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`     the VIR internal AST as used for the semantics.

Semantics, in `src/coq/Semantics/`:
- `DynamicValues.v` definition of the dynamic values and underdefined values.
- `LLVMEvents.v`       inventory of all events.
- `Denotation.v`      definitions of the representation of VIR programs as ITrees.
- `Handlers/`            includes the code for all of the handlers.
- `Handlers/MemoryModules` contains some of the modules for the memory model.
- `TopLevel.v`      provides the full model and the full interpreter, by plugging all components together.

## Test suite

Our current test-suite of LLVM programs for which we compare our semantics against llc is stored in `tests/`

- `tests/` directory containing the test suite of LLVM IR programs discussed in Section 6
