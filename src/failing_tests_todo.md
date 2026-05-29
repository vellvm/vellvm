# `make test` failures on the `ctrees-minimal` branch

Snapshot taken 2026-05-29, after restoring `make vellvm` linkage.

`./vellvm -l libll/rust-intrinsics.ll -test` runs three phases. Totals:

| Phase | Suite | Passed | Failed |
|---|---|---:|---:|
| 1 | Built-in `Test.suite` (`exec_tests`) | 149/153 | 4 |
| 2 | Pretty-printing round-trip (`test_pp_dir ../tests`) | 679/742 | 63 |
| 3 | Assertion tests (`test_dir ../tests`) | 259/264 | 5 |

## Category A — Pretty-printer bug: `null` for non-pointer types  (~63 phase-2 + 1 phase-3)

**All 63 phase-2 pretty-printing failures share one root cause.** Clang rejects the round-tripped `.v.ll` with `error: null must be a pointer type`. In LLVM IR, the `null` literal is only valid for pointer types; for everything else (i1/i8/i32/vectors/aggregates) the printer must emit `zeroinitializer` (or a typed zero like `0` / `false`).

Sampled cases:

```
%v = insertelement <2 x i32> null, i32 %a, i32 0      ; <2 x i32> not pointer
ret i32 null                                          ; i32 not pointer
@g = global {i8, i32} null                            ; aggregate, needs zeroinit
%cond.fr = freeze i1 null                             ; i1 not pointer
%t0 = udiv <2 x i4> <i4 null, i4 -1>, %x              ; vector elt not pointer
%5 = insertvalue {ptr, i32} null, ptr %2, 0, !dbg !N  ; aggregate
```

Almost certainly a side-effect of the undef/null collapse on this branch: the printer path for "default value of dtyp" was unified to `null`, but it must dispatch on `dtyp` and emit `zeroinitializer` for non-pointer types.

The `insertAndExtractValue.ll` failure in phase 2 is also Category A. (Its phase-3 failure is Category D — see below.)

**Fix:** one location in the pretty-printer.

## Category B — Stand-in `dvalue` equality is too strict  (1 phase-3)

- `tests/memory/loadAndStore.ll @testAlloca` — got and expected dvalues pretty-print *identically* (`[i32 0, i32 1, i32 2, i32 3]`) but the harness reports them unequal.

Caused by the `Stdlib.compare ... = 0` substitute introduced in `ml/main.ml`, `ml/tester.ml`, `ml/testing/assertion.ml` to replace `DV.dvalue_eqb`, which is no longer extracted. `Stdlib.compare` traverses the abstract `Obj.t`-backed `addr` / `iptr` payloads byte-wise and finds spurious differences.

**Fix:** re-export `dvalue_eqb` from `rocq/Semantics/DynamicValues.v` (add it to `Separate Extraction` in `Extract.v`), or write a structural OCaml comparator that does not compare opaque address bytes.

## Category C — External function / intrinsic coverage gap  (2 phase-3)

- `tests/ll/hello.ll` — `Could not look up global id printf`.
- `tests/ll/printf.ll` — `Uninterpreted Call: ... DTYPE_Pointer, 1 dvalues`.

`TopLevel.PREDEFINED_FUNCTIONS` is now `List.concat []` in `rocq/Semantics/TopLevel.v:278` (the `printf_definition` entry is commented out), so `printf` is unknown to the linker pass and reaches the interpreter as an external call.

**Fix:** re-add `printf` (and `puts`) to the predefined-functions table, in the same spirit as the existing `putchar_denotation` / `puts_denotation` already defined in `TopLevel.v`.

## Category D — Minimal-interpreter semantic gaps  (4 phase-1 + 2 phase-3)

All match deferred work documented in `ctrees_minimal_todos.md`.

Phase 1:
- `tests/ll/bitcast2.ll` — `Undefined Behavior: Division by poison`.
- `tests/ll/extract_value_undef.ll` — `Undefined Behavior: Division by poison`.
- `tests/ll/gep_undef.ll` — `handle_gep_h: unsupported index type`.

  The first two used to propagate poison; the new minimal semantics traps the
  division as UB. The third has GEP with an `undef` index. All three are direct
  consequences of the "no undef / single concrete monad" simplification.

- `tests/ll/invoke_throw.ll` — invoke/throw machinery. Exactly TODO #1 in
  `ctrees_minimal_todos.md` ("Re-introduce exception handling").

Phase 3:
- `tests/memory/insertAndExtractValue.ll @testExtractX` and `@testExtractY` —
  `insert_into_str: invalid aggregate data`. The serialization / aggregate path
  in the new minimal memory model rejects an `insertvalue` shape that the old
  model accepted. Aggregate-handling regression worth investigating alongside
  the broader minimal-memory work.

## Suggested order of attack

1. **Category A** — single printer fix, clears 63+ failures at once.
2. **Category B** — re-extract `dvalue_eqb` (small Rocq + extraction change).
3. **Category C** — re-add `printf`/`puts` denotations (small Rocq change).
4. **Category D** — branch-debt items; revisit when the minimal stack is more
   stable (poison propagation, exception machinery, aggregate insertvalue).
