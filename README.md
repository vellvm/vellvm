# Vellvm - verified LLVM IR

[![Opam build for vellvm](https://github.com/vellvm/vellvm/actions/workflows/vellvm.yml/badge.svg)](https://github.com/vellvm/vellvm/actions/workflows/vellvm.yml)
[![Nix build for vellvm](https://github.com/vellvm/vellvm/actions/workflows/test.yml/badge.svg)](https://github.com/vellvm/vellvm/actions/workflows/test.yml)

Vellvm is an ongoing project aiming at the formal verification in the Rocq proof
assistant of a compilation infrastructure inspired by the LLVM compiler.  

Check out the [Vellvm home page](https://vellvm.github.io/vellvm/) for more information.

# Installing / Compiling Vellvm

## Assumes:
  - OCaml 4.14.1 (typically installed via `opam`, see below)
  - Rocq 9.1.1
  - opam  2.0.0+
  - Clang 14.0.1+ (available for Mac OSX in XCode 4.2+, or installed via, e.g. `sudo apt-get install clang`)
  - `gnu-sed`
     + `sed` defaults to `gnu-sed` on linux.
	 + for Mac OS X with [homebrew](https://brew.sh/), do `brew install gnu-sed` and then create a symlink from `sed` to the `gsed` executable in your path.)

## Compilation:

1. Clone the vellvm git repo with the `--recurse-submodule` option
   - If you forgot to clone recursively, run `git submodule update --init --recursive` to fetch the extra libraries in `lib/`
3. Install all external dependencies
   - Note: you should be able to install all of the opam libraries by running `make opam` in the `src/` directory.
4. Run `make vellvm` in the `src/` directory: it will produce the OCaml executable called `vellvm`
   - Note: running just `make` will _also_ build all of Vellvm's metatheory, which is necessary for proving things, but takes much longer
  
## opam, Rocq, and opam dependencies

`opam` is available via [homebrew](https://brew.sh/) on Mac, and most system's package managers on Linux, e.g. `sudo apt-get install opam`.

If this is the first time you are using opam you need to initialize it:
  - On Linux: `opam init`
  - On Mac:  `opam init --disable-sandboxing` (sandboxing needs to be disabled due to a known [issue](https://github.com/ocaml/opam-repository/issues/12973)).

Then:

1. Create a vellvm development *opam switch* with:
   `opam switch create vellvm ocaml-base-compiler.4.14.1`.

2. Make sure the switch is activated (see the instructions in the output of the previous command), e.g.:
   `eval $(opam env --switch=vellvm)` (omit the dollar sign if using fish shell)

3. Add the Rocq package repository:
   `opam repo add rocq-released https://rocq-prover.org/opam/released`.

4. Install Rocq:
   `opam pin add rocq-core 9.1.1`

5. Install opam dependencies (run in the root directory of the project):
   `opam install -y --verbose --deps-only .`

Note: the dependency constraints in the opam file should be sufficient
for installing `vellvm`, however if you are having compilation
problems [checking the logs from CI may give you the appropriate
versions](https://github.com/vellvm/vellvm/actions/workflows/vellvm.yml),
as shown
[here](https://github.com/vellvm/vellvm/issues/364#issuecomment-2113331499).

## Using nix:

If you are a nix user, another way to install / compile Vellvm is with nix. Instructions can be found [here](nix.org).

# Running Vellvm

See the details over on the [Vellvm page](https://vellvm.github.io/vellvm/tests). The TLDR is:

The executable `vellvm` will be found in `src/`.
Do `src/vellvm -help` from the command line to see all available options.
In particular:
- `src/vellvm -i tests/ll/factorial.ll` to run the interpreter on a given file.
- `cd src && ./vellvm -test` to run the test suite
- `src/vellvm -test-file tests/ll/gep2.ll` to test a specific file using inlined assertions


