# Vellvm Testing Infrastructure

This code provides a means to add Vellvm semantics tests as `.ll` files with
some markup in the comments.  A single file might contain several tests so
that a single function might be called more than once or multiple similar
functions might be run.


A valid test file is an LLVM `.ll` file some of whose comments are interpreted
as assertions.  The test infrastructure supports `ASSERT EQ:` comments
of the form:

```
; ASSERT EQ: <typ> <lit> = call <typ> <@function_name> (<typ_1> <lit_1>, ..., <typ_n> <lit_n>)
```

and `ASSERT POISON:` comments of the form:
```
; ASSERT POISON: call <typ> <@function_name> (<typ_1> <lit_1>, ..., <typ_n> <lit_n>)
```

This represents a test case asserting that the result of calling function
`@function_name` with the given inputs yields the answer `lit`.  Here `T` and
`typ_1` ... `typ_n` are LLVM IR types (that do not mention names or pointers).
The `lit` and `lit_1` ... `lit_n` are LLVM IR literal values.  The legal LLVM IR
literals that can appear in the assertions correspond to a subset of Vellvm
UVALUEs that can be interpreted without needing any program context
(i.e. variables, globals, or pointers).


```
lit :=
| Lit_I1 (x:int1)
| Lit_I8 (x:int8)
| Lit_I32 (x:int32)
| Lit_I64 (x:int64)
| Lit_Double (x:ll_double)
| Lit_Float (x:ll_float)
| Lit_Undef (t:dtyp)
| Lit_Poison
| Lit_Struct        (fields: list lit)
| Lit_Packed_struct (fields: list lit)
| Lit_Array         (elts: list lit)
| Lit_Vector        (elts: list lit)
```

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
; ASSERT POISON: call i32 @main(i32 0, i32 0)
```
