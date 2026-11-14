# i1 arithmetic tests

`i1` is the degenerate integer width. Its values are 0 and 1, which read as
0 and -1 when signed, so `INT_MIN` is 1 and `INT_MAX` is 0. Nearly every flag
and corner case in the LangRef is reachable with one or two inputs, and several
come out differently than at wider types:

| Expression | Result | Why |
|---|---|---|
| `mul nsw i1 1, 1` | poison | (-1) × (-1) = 1 does not fit; `mul nuw i1 1, 1` is 1 |
| `add nsw i1 1, 1`, `add nuw i1 1, 1` | poison | -1 + -1 = -2; 1 + 1 = 2 |
| `sub nsw i1 0, 1` | poison | 0 - (-1) = 1 > `INT_MAX` |
| `shl`/`lshr`/`ashr i1 x, 1` | poison | a shift by the bit width, with or without flags |
| `sdiv i1 1, 1`, `srem i1 1, 1` | UB | `INT_MIN / -1` |
| `trunc nuw i8 255 to i1` | poison | only 0 and 1 survive `nuw` |
| `trunc nsw i8 1 to i1` | poison | only 0 and -1 survive `nsw` |
| `zext nneg i1 1`, `uitofp nneg i1 1` | poison | `i1 1` is negative |
| `sext i1 1`, `sitofp i1 1` | -1, -1.0 | |
| `fptosi double 1.0 to i1` | poison | signed range is {-1, 0}; `fptosi -1.0` is `true` |
| `icmp slt i1 1, 0` | true | 1 is -1 |
| `icmp samesign` on different operands | poison | different values have different signs |
| `getelementptr i8, ptr %p, i1 true` | `%p - 1` | GEP indices are signed |
| `extractelement <2 x i8> %v, i1 true` | element 1 | vector indices are unsigned |

The tests state what LLVM requires, not what Vellvm does today.

## Files

All of the files below are written by `gen-i1.py`. Edit the generator, not the
`.ll` files. Expected results come from a small reference model of the LangRef
in the generator, and every operation is run on every combination of `i1`
inputs.

**Defined results** (`tests/gen.py` print-all style, like
`tests/ll/gep-layout.ll`). Every case is an argument-free `i64` function,
`main` prints them all, and there is one `ASSERT EQ` per case:

```sh
clang -w tests/llvm-arith/i1/binop.ll -o a.out && ./a.out
```

| File | Contents |
|---|---|
| `binop.ll` | every binary operator × every flag combination × every defined input pair |
| `icmp.ll` | every predicate, with and without `samesign` |
| `cast.ll` | `trunc` (with `nuw`/`nsw`) from i2/i8/i32/i64; `zext` (`nneg`), `sext` to those; `uitofp` (`nneg`), `sitofp`, `fptoui`, `fptosi` at float and double; `bitcast`, `inttoptr`, `ptrtoint` |
| `control.ll` | literals (`true`, `1`, `-1`), `select`, `br`, `phi`, `switch`, calls (`zeroext`/`signext`), arithmetic identities |
| `switch-literals.ll` | `switch` cases spelled `i1 true` / `i1 false` (separate because Vellvm fails to parse it) |
| `memory.ll` | sizes and offsets, allocas, globals, arrays and structs of `i1`, `i1` as a GEP or vector index, `<8 x i1>` ↔ `i8` in memory |
| `vector-ops.ll` | lane-wise operators and `icmp` on `<4 x i1>`, `select`, casts, bitcasts, element access, shuffles |
| `intrinsics.ll` | `*.with.overflow`, saturating arithmetic, min/max, `abs`, `ctlz`/`cttz`/`ctpop`, `bitreverse`, `fshl`/`fshr`, `scmp`/`ucmp`, `vector.reduce.*` |

**Poison and undefined behavior** (`tests/gen.py --dispatch` style, like
`tests/ub`). The assertions call parameterised functions directly, with defined
controls next to the poison and UB cases. A native run can't observe poison, so
the generated tail gives one entry point per assertion:

```sh
clang -w tests/llvm-arith/i1/binop-poison.ll -o a.out && ./a.out 7    # case 7 natively
llubi --entry-function=ub_case_7 tests/llvm-arith/i1/binop-poison.ll  # reports poison / UB
```

| File | Contents |
|---|---|
| `binop-poison.ll` | flag violations, shifts by the bit width, poison operands |
| `div-rem-ub.ll` | division and remainder: zero or poison divisor, `INT_MIN / -1`, poison dividend, vector lanes |
| `cast-poison.ll` | `trunc nuw`/`nsw` (also from i128), `zext nneg`, `uitofp nneg`, out-of-range `fptoui`/`fptosi`, `icmp samesign`, casts of poison |
| `control-poison.ll` | `select` and logical and/or with poison arms, `freeze`, `phi`, memory round trips, branching on poison |
| `vector-poison.ll` | poison in single lanes; out-of-range element indices |
| `intrinsics-poison.ll` | `abs` of `INT_MIN`, `ctlz`/`cttz` of 0, saturating shifts by the bit width |

The remaining files (`add_nsw.ll`, `mul.ll`, `vector.ll`, …) are the older
hand-written tests, one case per file.

## Regenerating and checking

```sh
python3 tests/llvm-arith/i1/gen-i1.py            # rewrite the .ll files
cd src && make i1-tests                          # write them only if one is missing (`make test` does this)
python3 tests/llvm-arith/i1/gen-i1.py --check    # confirm the expectations against clang and llubi
./vellvm -L libll -test-dir ../tests/llvm-arith/i1               # from src/
python3 tests/ub/compare.py tests/llvm-arith/i1/*-poison.ll tests/llvm-arith/i1/div-rem-ub.ll
```

`--check` compiles each print-all file with clang at `-O0` and `-O2` and
compares the printed results with the assertions. For each dispatch case it
runs llubi and compares the value, poison, or UB (and its line) with the
assertion, and where the result is defined it also compares the native output.

## Status

As of 2026-11-14 (after the `mul nsw`, `trunc nuw`/`nsw` and `nneg` fixes), with LLVM 23.1.2: all 1,488 generated
cases agree with clang and llubi. Vellvm passes 1,286 of them, fails 198, and
does not parse the 4 in `switch-literals.ll` (`-test-dir` skips that file
silently). What fails:

- **`udiv`/`sdiv`/`urem`/`srem` of a poison dividend by 0** give poison, not UB.
- **`getelementptr` with an `i1` index** fails (`gep_steps: unsupported index
  type`).
- **`extractelement` / `insertelement` with index `i1 true`** give poison: the
  index is read as -1 instead of unsigned 1.
- **`switch` cases written `i1 true` / `i1 false`** don't parse.
- **Intrinsics at `i1`** are almost all uninterpreted calls: `libll` defines
  them only at wider types. Only `llvm.ushl.sat.i1` is handled.
