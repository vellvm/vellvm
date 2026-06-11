# `undef` tests

The `.ll` files in this directory all contain the `undef` keyword.

On the `ctrees-minimal` branch the minimal semantics has no dedicated
`undef` value: `undef` is parsed back into the AST (as `EXP_Undef`) but is
treated **semantically as `poison`** (see `src/ml/libvellvm/llvm_parser.mly`
and `denote_exp` in `src/rocq/Semantics/Denotation.v`).

These tests were previously quarantined while `undef` was unsupported. They
are reinstated here mainly to exercise the **round trip** — vellvm parses
`undef`, pretty-prints it back out (via `ShowAST`), and `clang` re-parses the
result — which the standard `make test` suite runs automatically over every
`.ll` file found under `../tests/` (`test_pp_dir`), together with any inline
`; ASSERT EQ:` annotations (`test_dir`).

Provenance: the sub-directories mirror the original locations these files
came from (`alive2/`, `ll/`, `io/`, `memory/`, …).

## Known failure

`memory/insertAndExtractValue.ll` passes the round-trip but fails 2/5 of its
`; ASSERT EQ:` assertions (`@testExtractX`, `@testExtractY`). Both build an
aggregate by inserting into `undef`:

```llvm
%agg1 = insertvalue {i32, float} undef, i32 1, 0
```

Because `undef` now denotes as `poison`, this calls `insert_into_str` (in
`src/rocq/Semantics/DynamicValues.v`) on a scalar `DVALUE_Poison`, which has
no aggregate structure to insert into, so it hits the
`"insert_into_str: invalid aggregate data"` error case. Under the old
`undef` semantics, `undef` was a real aggregate placeholder and these
assertions held.

Possible fix (not yet implemented): make `insert_into_str` and
`index_into_str_dv` handle `DVALUE_Poison` by materializing it — via the
`dtyp` it carries — into an aggregate of per-field `poison` values, so that
`insertvalue`/`extractvalue` propagate poison through aggregates (matching
LLVM, where `insertvalue poison, x, 0` yields `{ x, poison }`). The two
assertions could then be restored or expressed with `; ASSERT POISON:`.
