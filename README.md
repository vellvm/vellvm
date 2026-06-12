# Vellvm


[![Opam build for vellvm](https://github.com/vellvm/vellvm/actions/workflows/vellvm.yml/badge.svg)](https://github.com/vellvm/vellvm/actions/workflows/vellvm.yml)
[![Nix build for vellvm](https://github.com/vellvm/vellvm/actions/workflows/test.yml/badge.svg)](https://github.com/vellvm/vellvm/actions/workflows/test.yml)

https://vellvm.github.io/vellvm/

Vellvm is an ongoing project aiming at the formal verification in the Rocq proof
assistant of a compilation infrastructure inspired by the LLVM compiler.

The central piece of Vellvm is the Verified IR (VIR), a Rocq formalization of the
semantics of (a subset of) the [LLVM IR](https://www.llvm.org/) that is intended for _formal
verification_ of LLVM-based software.
It is being developed at the University of Pennsylvania as part of the [DeepSpec](https://www.deepspec.org) project.

After VIR, the second component whose development is reaching maturity is the verification of
a verified front-end for the [Helix](https://github.com/vzaliva/helix) chain of compilation.


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
   - Note: you should be able to install all of the opam libraries  with `make opam` in the `src/` directory.
4. Run `make` in the `src/` directory: it will produce the OCaml executable called `vellvm`

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

The executable `vellvm` will be found in `src/`.
Do `src/vellvm -help` from the command line to see all available options.
In particular:
- `src/vellvm -interpret tests/ll/factorial.ll` to run the interpreter on a given file.
- `cd src && ./vellvm -test` to run the test suite against clang
- `src/vellvm -test-file tests/ll/gep2.ll` to test a specific file using inlined assertions


# Adding a new test case

One way to create new test cases for Vellvm is to compile a C program using `clang` and then add assertions to turn it in to an executable for adding assertions.  The steps below illustrate this process:

1. Create a C program (e.g. in the directory `tests/c`), for instance, `example.c`.

 - The C program should not use C libraries (yet!), which are not part of the LLVM IR standard, but the program should be able to use general C language features.

For example: the following C program contains a simple function called `foo` that multiplies its input by 3:

```
int foo(int x) {
  return 3*x;
}
```

2. Compile the C program using `clang` with the `-emit-llvm` and `-S` flags to generate an LLVM `.ll` version.

```
~/vellvm/tests/c> clang -S -emit-llvm example.c
```

3. The resulting `.ll` file should look something like this:
```
~/vellvm/tests/c> cat example.ll
; ModuleID = 'example.c'
source_filename = "example.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @foo(i32) #0 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  %3 = load i32, i32* %2, align 4
  %4 = mul nsw i32 3, %3
  ret i32 %4
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 15]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple clang version 11.0.0 (clang-1100.0.33.16)"}
```

4. Edit the `.ll` file to add some assertions about the behavior of the program.  For example, we could add the following three assertions (the last of which is actually incorrect):

 - The syntax for each assertion is a comment of the form: `; ASSERT EQ: <typ> <val> = call <typ> @<fun>(<typ1> arg1, ..., <typN> argN)`


```
; ASSERT EQ: i32 0 = call i32 @foo(i32 0)
; ASSERT EQ: i32 3 = call i32 @foo(i32 1)
; ASSERT EQ: i32 5 = call i32 @foo(i32 2)
```

5. Run vellvm with the `-test-file example.ll` flags to see the results of running the test cases:

```
~/vellvm/tests/c> ../../src/vellvm -test-file example.ll
(* -------- Vellvm Test Harness -------- *)

example:
  passed - UVALUE_I32(0) = foo(UVALUE_I32(0))
  passed - UVALUE_I32(3) = foo(UVALUE_I32(1))
  failed - UVALUE_I32(5) = foo(UVALUE_I32(2))
	   ERROR: not equal
(*-------------------------------------- *)
Passed: 2/3
Failed: 1/3
```

6. The command `vellvm -test-dir <dir>` will run the `ASSERT`s found in all the `.ll` files in directory `<dir>`.
