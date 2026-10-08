# Undefined-behavior tests

Executable tests for the cases where the LLVM LangRef
(`llvm-project/llvm/docs/LangRef.md`) and `UndefinedBehavior.md` say a program
has **immediate undefined behavior**, grouped by the instruction that triggers it.
Each file quotes the LangRef clause it tests in its header.

The corpus states what LLVM requires. It does not record what Vellvm does
today, so many of these assertions fail at the moment (see [Status](#status)).

One deliberate exception: this branch follows LLVM's plan to remove `undef` in
favor of `poison`, and Vellvm denotes `undef` as `poison`. In UB positions the
two agree (branching on either is UB). They differ only where `undef`'s "any
value" reading is masked, like `or i8 undef, 255`, which today's LangRef makes
255 but which is poison here. Such tests (`switch.ll`'s
`@switch_or_undef_255`) assert the poison answer and say so in a comment.

```sh
cd src
./vellvm -L libll -test-dir ../tests/ub            # whole directory
./vellvm -L libll -test-file ../tests/ub/load.ll   # one file
python3 ../tests/ub/compare.py                     # Vellvm vs llubi vs clang; see below
```

## Conventions

- `; ASSERT UB <line>: call <ty> @f(args)` asserts that calling `@f` raises UB,
  and `<line>` is the line of the instruction that should raise it. That
  instruction carries a `; <- UB @f` marker. `fill-ub-lines.py <files>` recomputes
  every `<line>` from the markers, so run it after editing a file.
- Every file ends with a generated *executable tail*. It holds one
  argument-free wrapper `@ub_case_N` per assertion (numbered in file order) and
  a `main` that runs case N alone when invoked as `./a.out N`. After adding,
  removing, or editing assertions, regenerate the tail with
  `python3 tests/gen.py --dispatch <files>` (after `fill-ub-lines.py`). The
  tail is appended at the end of the file, so it doesn't shift any asserted
  line.
- Most UB assertions come with a **control**: the same function called with
  well-defined arguments (`ASSERT EQ`/`ASSERT SUCCEEDS`). Some controls show a
  near miss that is only *poison* and not UB, for example `nonnull` without
  `noundef`. These controls check that the UB is detected for the right reason.
- Entry points take scalars, `ptr null`, or `poison`, because those are the only
  arguments the harness can pass. They return a non-`void` type, because
  `call void @f()` doesn't parse as an assertion. A `ptr` result is returned as
  `ptrtoint`, because the harness can't compare `ptr` results.
- Where the LangRef locates UB at a call boundary (`noundef`, `nonnull`, …), the
  marker is on the `call` (for parameter attributes) or on the callee's `ret`
  (for return attributes on the definition).

## Files

| File | What triggers UB |
|---|---|
| `udiv.ll`, `urem.ll` | divisor zero / poison / undef, including a single vector lane |
| `sdiv.ll`, `srem.ll` | the above plus `INT_MIN / -1`, and a poison dividend with divisor `-1` |
| `br.ll`, `switch.ll` | branching on poison or undef |
| `indirectbr.ll` | poison, undef, or null address |
| `unreachable.ll` | executing `unreachable` |
| `alloca.ll` | poison or undef element count; access through a zero-sized alloca |
| `load.ll`, `store.ll` | null, poison, or undef address; out of bounds; dangling stack; use after free; overestimated `align`; `!noundef`, `!nonnull`+`!noundef`, `!align`+`!noundef` metadata; store to a `constant` global; store outside `llvm.lifetime.start`/`end` |
| `getelementptr.ll` | dereferencing the poison result of `inbounds`/`nuw`/`nusw` violations or a poison index |
| `atomicrmw.ll`, `cmpxchg.ll` | null or poison address, out of bounds, misaligned |
| `provenance.ll` | access through a pointer *based on* the wrong object (gep across objects, integer constants, stale heap or stack pointers) |
| `call.ll` | poison, undef, null, or data-pointer callee; calling-convention mismatch |
| `call-param-attrs.ll` | `noundef`; `nonnull`, `align`, `range` combined with `noundef`; `dereferenceable(n)`, `dereferenceable_or_null(n)`; on the declaration or the call site |
| `call-param-nofpclass.ll` | `nofpclass` + `noundef` *(does not parse yet)* |
| `ret.ll` | return-value `noundef`, `nonnull`, `align`, `range`, `dereferenceable` |
| `call-fn-attrs.ll` | `noreturn` that returns, writes that violate `memory(...)`, `nocreateundeforpoison` |
| `call-fn-attrs-unwind.ll` | `nounwind` that unwinds *(uses Vellvm's throw intrinsic, so it runs only under Vellvm)* |
| `call-ptr-attrs.ll` | `readonly`, `readnone`, `captures(...)`, `nofree`, `noalias`, `initializes`, `writable` |
| `call-ptr-attrs-unparsed.ll` | `captures(ret: …)`, `!captures` store metadata *(does not parse in Vellvm yet)* |
| `call-ptr-attrs-nofreeobj.ll` | `nofreeobj` *(parsed by neither Vellvm nor LLVM 23.1)* |
| `intrinsics/memcpy.ll`, `memmove.ll`, `memset.ll` | poison or undef length; null or poison pointers with nonzero length; overlap (memcpy only); out of bounds; writing to a constant |
| `intrinsics/assume.ll`, `assume-bundles.ll` | a false or poison condition; violated `"nonnull"`, `"align"`, `"dereferenceable"` bundles |
| `libc/free.ll` | double free; freeing a stack, global, interior, or poison pointer |

## Status

As of 2026-10-08, `make interp` on `ub-tests` gives **194/301**
assertions passing, and the three files that don't parse report as failures. The
12 failing controls are all accounted for below: the poison-only attribute and
metadata cases, `initializes` read-before-write, lifetime, and memmove. Gaps by category:

**Already handled.** Division and remainder, including `INT_MIN / -1` and
`INT_MIN srem -1`; branching or
switching on poison or `undef`; `unreachable`; null, poison, out-of-bounds, dangling,
freed, and wrong-provenance loads, stores, and atomics; all of `provenance.ll`;
calls through poison, `undef`, or null (including `inttoptr 0`) function
pointers; memcpy overlap and out of bounds; memcpy/memset with a poison
length, or poison pointers and a nonzero length (a no-op with length 0), and
memset with a poison fill value (stores poison); double free, freeing non-heap memory, and
`free(poison)` (`free(null)` is a no-op, whatever the null pointer's provenance).

**Missing UB (Vellvm returns a value instead):**
- (`undef` now behaves exactly like poison. The remaining `undef` cases, the
  `alloca` count and a `noundef` return, fail for
  the same reasons as their poison counterparts listed here.)
- `alloca i32, i32 poison` is not UB *at the alloca*. The assertion passes only
  because the following store fails (the reported location is the store).
- Alignment is checked only for an explicit `align` on `load`. Not yet checked:
  `store`/`atomicrmw`/`cmpxchg` `align`, a `load` with no `align` (which has the
  type's ABI alignment), and the `align` attribute. (Allocas without `align`
  now get their type's natural alignment, vectors included.)
- `getelementptr` `inbounds`/`nuw`/`nusw` never produce poison.
- No parameter, return, or function attribute is enforced: `noundef`,
  `nonnull`, `align`, `dereferenceable[_or_null]`, `range`, `noreturn`,
  `nounwind`, `memory(...)`, `readonly`/`readnone`, `captures`, `nofree`,
  `noalias`, `initializes`, `writable`, `nocreateundeforpoison`. This also makes
  the poison-only controls fail (for example `nonnull` alone should yield poison).
- Load metadata `!noundef`, `!nonnull`, `!align` is ignored.
- `llvm.lifetime.start`/`end` are no-ops in `libll`, so dead stack objects
  aren't modeled.
- Stores to `constant` globals are allowed, directly and through memcpy/memset.
- `llvm.assume` is a no-op in `libll`, and assume operand bundles are ignored.
- Calling-convention mismatches aren't detected.

**Wrong kind of error (fails instead of UB):**
- `indirectbr`: "Unsupport itree terminator".
- Calls through data pointers become an uninterpreted external call.

**UB where LLVM has none:**
- (Not asserted) Vellvm raises UB when `cmpxchg` compares against poison. The
  LangRef doesn't list that case.

**Unsupported:**
- `llvm.memmove.*`: "Uninterpreted Call".
- The parser rejects `blockaddress`, `nofpclass`, `nofreeobj`, `dead_on_return`,
  `captures(ret: …)`, `!captures` store metadata, and `!dereferenceable` /
  `!dereferenceable_or_null` load metadata (`dereferenceable` is lexed as a
  keyword).

## Not covered

These LangRef UB clauses have no test, either because no run can observe them
or because Vellvm has no corresponding feature:
- non-termination: `willreturn`, `mustprogress`;
- concurrency: `nosync`, `noalias`/`nofree` across threads;
- `speculatable`;
- the `inrange` gep;
- `inalloca` / `preallocated` / `musttail`;
- Windows EH (`catchret`, `cleanupret`, funclet bundles);
- the global declaration/definition mismatch and section rules;
- `noalias.addrspace` metadata;
- allocations too large for the index type: under the infinite-pointer
  interpreter, `alloca i8, i64 -1` would not terminate;
- call signature mismatches, which the LangRef calls "target-specific".

## Notes for the harness

- The UB string already carries a source span (`[file:L.C-L.C]: msg`), so
  `ASSERT UB <line>` can be checked by testing whether `<line>` falls in that
  span. Checked this way (as `compare.py` does), 93 of the 94 UB cases Vellvm
  currently detects match. The exception is the `alloca` case above. (memcpy
  and memset UB used to be reported inside `libll` shims for the
  opaque-pointer intrinsic names; Vellvm now handles those names directly.)
- Asserting a UB *kind* would need a stable tag. Today the kind is only in
  free-form messages ("Reading from unallocated memory.", "Read from memory with
  invalid provenance", "Division by poison.", …).

## Comparing with llubi and clang

`compare.py` runs every case (every `ASSERT` line) **in a separate process**
under each tool below, and writes `results/compare.md` (a summary plus one
table per file) and `results/compare.json`. Running each case separately means
UB in one case can't mask or change another case: the interpreters stop at the
first UB, and the optimizer may treat a whole UB path as unreachable.

```sh
cd src && make interp
python3 ../tests/ub/compare.py [files...] [--clang PATH] [--llubi PATH] [-j N]
```

| Column | How the case is run |
|---|---|
| Vellvm | The test harness, on a copy of the file with every other assertion commented out (line numbers unchanged). |
| llubi | `llubi --entry-function=ub_case_N file.ll`. llubi reports UB with a line and a reason, which compare.py checks against the marker. |
| llubi-z | The same, with `--undef-behavior=zero`. |
| O0–O3 | `clang -O<n> file.ll`, run as `./a.out N`. The cell shows the printed result, a signal, `no return`, or `timeout`. |
| ASan | `clang -O0 -fsanitize=address`, on a copy whose functions get the `sanitize_address` attribute (clang only adds it when compiling C, and ASan skips functions without it). Run with `detect_stack_use_after_return=1`. |

The Vellvm and llubi cells are marked ✓ (agrees with the assertion), ~ (UB, but
on a different line), or ✗. The native columns are not marked, because they
aren't UB detectors. They show what the UB turns into.

### First run (2026-10-08, macOS arm64, Homebrew clang/llubi 23.1.2)

Out of 195 UB cases and 111 controls:

| | Vellvm | llubi | O0 | O1–O3 | ASan |
|---|---|---|---|---|---|
| UB cases reported as UB | 76 | 144 | – | – | – |
| … on the asserted line | 69 | 138 | – | – | – |
| UB cases that trap or fail an ASan check | – | – | 41 | 33 | 52 |
| controls flagged | 1 (`free(null)`) | 0 | 0 | 0 | 0 |

- **llubi** finds most of what Vellvm misses: alignment, `!noundef` and the
  other load metadata, parameter attributes, `getelementptr` flags, lifetime,
  `assume`, and srem overflow. It misses:
  - `undef` in UB positions (division, `br`, `switch`, `alloca`, `noundef`).
    Vellvm caught these for division in this run; now that it denotes `undef`
    as poison, it also catches `br` and `switch`;
  - the function and pointer-capability attributes (`memory(...)`, `noreturn`,
    `readonly`/`readnone`, `captures`, `nofree`, `noalias`, `initializes`,
    `writable`, `nocreateundeforpoison`);
  - calling-convention mismatches;
  - `dereferenceable` on a freed or dangling pointer.

  It doesn't implement `atomicrmw`/`cmpxchg`. It also checks return-value
  attributes at the caller's `call`, while these tests put the UB at the
  callee's `ret`, following LangRef's "operand of a ret instruction". Those cases
  show as ~.
- **llubi-z never differs from llubi.** The option only affects loads of
  uninitialized memory, not `undef` constants. This column is a candidate for
  removal.
- **O1, O2, and O3 agree on 301 of 306 cases.** The interesting split is O0 vs
  optimized. Native output differs across the levels for 84 UB cases, and only
  for 10 controls, all of which return poison or an address. At O1+, LLVM turns
  many UBs it can see into traps (24 `SIGTRAP`s at O2, e.g. null loads/stores,
  `assume(false)`, `noreturn` returning, cc mismatch). Other UBs disappear: at
  O1+, double free, out-of-bounds memcpy, and stores to constants just return
  0. On arm64 even `-O0` division by zero quietly returns 0.
- **ASan** (52) catches the memory errors with a precise kind:
  stack/global-buffer-overflow, heap-use-after-free, stack-use-after-return,
  double free, bad free, and `memcpy-param-overlap`. It is the only native
  column that names the problem.

