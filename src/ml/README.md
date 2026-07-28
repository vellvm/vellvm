# Vellvm Executable

## Behavior of `vellvm`:

By default, `vellvm file1.ll ... fileN.ll` will simply _parse_ each of the files provided and then link them together.
Various flags enable further processing and / or testing and executation.

See `vellvm -h` for the current list of options.

Note: the various `-test*` options interrupt processing of the vellvm command-line arguments, so 
`-l file` and `-L dir` options should come *before* the `-test*` directive.

# Linking vs. processing

Linking: The `-l` and `-L` directives tell vellvm to include the `.ll` code verbatim (with no processing).

Processing: Any `.ll` files passed as command-line arguments (i.e. without `-l`) are subject to the `-O` and `-emit-llvm` flags.

# Output

Processed outputs generated via the `-emit-llvm` or `-print-ast` options are generated (by default) in the `output` directory.

# Vellvm Testing Infrastructure

This code provides a means to add Vellvm semantics tests as `.ll` files with
some markup in the comments.  A single file might contain several tests so
that a single function might be called more than once or multiple similar
functions might be run.

A valid test file is an LLVM `.ll` file some of whose comments are interpreted
as assertions.  The test infrastructure supports three shape of assertions

## ASSERT EQ

```
; ASSERT EQ: <typ> <lit> = call <typ> <@function_name> (<typ_1> <lit_1>, ..., <typ_n> <lit_n>)
```

This represents a test case asserting that the result of calling function
`@function_name` with the given inputs yields the answer `lit`.  Here `T` and
`typ_1` ... `typ_n` are LLVM IR types (that do not mention names or pointers).
The `lit` and `lit_1` ... `lit_n` are LLVM IR literal values.  The legal LLVM IR
literals that can appear in the assertions correspond to a subset of Vellvm
DVALUEs that can be interpreted without needing any program context
(i.e. variables, globals, or pointers).

## ASSERT SUCCEEDS

```
; ASSERT SUCCEEDS: call <typ> <@function_name> (<typ_1> <lit_1>, ..., <typ_n> <lit_n>)
```

This represents a test case asserting that the result of calling function
`@function_name` with the given inputs does not fail, disregarding the result.

## ASSERT FAILS

```
; ASSERT FAILS: call <typ> <@function_name> (<typ_1> <lit_1>, ..., <typ_n> <lit_n>)
```

This represents a test case asserting that the result of calling function
`@function_name` with the given inputs fails.

## Example

Here is a simple, complete example of a test file in the form permitted by the
tester:

```
define i32 @shl_test(i32 %x, i32 %amt) {
  %1 = shl i32 %x, %amt
  ret i32 %1
}
; ASSERT EQ: i32 3 = call i32 @shl_test(i32 3, i32 0)
; ASSERT EQ: i32 6 = call i32 @shl_test(i32 3, i32 1)
; ASSERT EQ: i32 12 = call i32 @shl_test(i32 3, i32 2)
; ASSERT SUCCEEDS: call i32 @shl_test(i32 3, i32 3)
```

# Structure

- main.ml: 
  entry point for vellvm executable

- platform.ml:
  utilities for interfacing with linux / OS X file system, shell scripts, running clang
  
- debugger.ml - interactive stepping debugger
- interpreter.ml - executable interpreter

- frontendTest.ml - test harness for parsing and pretty-printing
- test.ml - test harness for `ASSERT` based test cases
