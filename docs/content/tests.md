---
title: "Tests"
---

# Running Vellvm

The `vellvm` executable can be used to run LLVM IR code in `.ll` files by using the `-i` or `-interpret` flags.  By default the interpeter will look for an entry point called `main` (but note that does not accept command-line arguments).

```bash
~/vellvm> vellvm -i tests/ll/factorial.ll 
(* -------- Vellvm Test Harness -------- *)
Processing: tests/ll/factorial.ll
Program terminated with: i64 120
```

You can "link" several `.ll` files together by using the `-l` or `-L` flags.  The `src/libll` directory contains some minimal library support for C and Rust programs, along with an implementation of `printf`.

# Adding a new test case

One way to create new test cases for Vellvm is to compile a C program using `clang` and then add assertions to turn it in to an executable for adding assertions.  The steps below illustrate this process:

1. Create a C program (e.g. in the directory `tests/c`), for instance, `example.c`.

 - The C program should not use C libraries (yet!), which are not part of the LLVM IR standard, but the program should be able to use general C language features.

For example: the following C program contains a simple function called `foo` that multiplies its input by 3:

```c
int foo(int x) {
  return 3*x;
}
```

2. Compile the C program using `clang` with the `-emit-llvm` and `-S` flags to generate an LLVM `.ll` version.

```bash
~/vellvm/tests/c> clang -S -emit-llvm example.c
```

3. The resulting `.ll` file should look something like this:
```llvm
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


```llvm
; ASSERT EQ: i32 0 = call i32 @foo(i32 0)
; ASSERT EQ: i32 3 = call i32 @foo(i32 1)
; ASSERT EQ: i32 5 = call i32 @foo(i32 2)
```

5. Run vellvm with the `-test-file example.ll` flags to see the results of running the test cases:

```bash
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
