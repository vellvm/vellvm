# Exception tests — `invoke` / `resume` / `landingpad`

These exercise the small slice of LLVM exception handling needed to compile
Rust's `panic = unwind` (Itanium/Linux model): `invoke`, `resume`, and
`cleanup` / catch-all (`catch ptr null`) `landingpad`s, with panics raised by
the `@llvm.vellvm.internal.throw()` intrinsic.

Semantics: **design A** (value-carried unwind). A function either returns a
`dvalue` or unwinds; the unwind crosses the `mrec` call knot as the `inl e`
half of `CallE`'s `exc + dvalue`. A plain `call` re-raises it within its frame
(`raiseLLVM`), and an `invoke` branches on it — parking the opaque payload in
the frame (`stack_raise`) and jumping to the landingpad, which reads it back
(`stack_get_exc`). See `todonotes.md` (§ Exceptions) for why the `mrec`
architecture forces the value channel rather than an abortive-event catch.

Run them with:

```
./vellvm -l libll/rust-intrinsics.ll -test-dir ../tests/exceptions      # assertions
./vellvm -l libll/rust-intrinsics.ll -test-pp-dir ../tests/exceptions   # round-trip
```

## Covered

| File | What it exercises |
|---|---|
| `invoke_resume_landingpad.ll` | Baseline two-frame unwind: throw → `cleanup` landingpad + `resume` → catch-all landingpad stops it. |
| `conditional_catch.ll` | Both invoke successors in one program, chosen by a runtime `i1`: normal `to` edge **and** `unwind` edge. |
| `deep_unwind.ll` | Plain-`call` propagation through 3 frames to a single outer `invoke` (value-carried unwind crossing `mrec` frame by frame). |
| `recover_and_continue.ll` | `catch_unwind` that recovers and returns normally; caller consumes the value via a plain `call` and keeps computing. |
| `invoke_result.ll` | `%v = invoke …` binding a **non-void result** on the normal path, then using it. |
| `locals_across_catch.ll` | A local computed before the invoke, read in the landingpad block (frame-local state survives the catch). |
| `stale_payload.ll` | Negative test (`ASSERT FAILS`): a landingpad reached by a *normal* branch after a catch must error, not deliver the stale payload (`StackGetExc` is consuming). |

## Not covered by the current semantics

The following are *deliberately out of scope* (beyond Rust `panic=unwind`) or
are known limitations of this minimal model. They are written here as the test
cases one would add when extending the semantics; today they would error,
misbehave, or silently do the wrong thing.

### 1. Typed `catch` clauses, `filter`, and the selector value

The landingpad ignores its clauses and delivers an opaque payload; there is no
type-info matching and no `llvm.eh.typeid.for` / selector. Code that *dispatches*
on the caught type is unsupported:

```llvm
caught:
  %lp  = landingpad { ptr, i32 } catch ptr @SomeTypeInfo
  %sel = extractvalue { ptr, i32 } %lp, 1     ; selector
  %tid = call i32 @llvm.eh.typeid.for(ptr @SomeTypeInfo)
  %hit = icmp eq i32 %sel, %tid
  br i1 %hit, label %handle, label %rethrow   ; catch this type, else resume
```

Current behavior: `%lp` is the placeholder payload (`DVALUE_None`), not a
`{ptr,i32}` aggregate, so the `extractvalue` itself fails ("invalid aggregate
data"). Selective catch / `filter` (exception specifications) are likewise
unmodeled — every landingpad catches unconditionally.

### 2. Reading the exception object / payload

The payload is a fixed placeholder, so a handler that inspects the in-flight
exception object gets nothing real:

```llvm
caught:
  %lp  = landingpad { ptr, i64 } cleanup
  %obj = extractvalue { ptr, i64 } %lp, 0     ; exception-object pointer
  %v   = load i64, ptr %obj                   ; read the panic payload
```

Rust's runtime (`__rust_panic_cleanup`) really does read the payload pointer to
recover the panic value, so a faithful `catch_unwind` that returns the panic
value is out of reach until the payload carries a real object.

### 3. Windows funclet-based EH

`catchswitch` / `catchpad` / `cleanuppad` / `catchret` / `cleanupret` (the
MSVC/SEH model, used by `panic=unwind` on `*-pc-windows-msvc`) are entirely
unsupported. Only the Itanium landingpad model is modeled.

```llvm
  %cs = catchswitch within none [label %handler] unwind to caller
handler:
  %cp = catchpad within %cs [ptr null, i32 64, ptr null]
  catchret from %cp to label %resume
```

### 4. Unwinding through an external / declared-only function

External calls (the `None` branch of the call knot) always return normally —
they cannot unwind. Only the internal throw intrinsic raises. So invoking a
merely-`declare`d function that is supposed to unwind (e.g. a real
`@_Unwind_RaiseException` / `@__rust_start_panic`) does not propagate:

```llvm
declare void @may_unwind()              ; no body
  invoke void @may_unwind() to label %ok unwind label %caught  ; never takes the unwind edge
```

### 5. Multiple live exceptions in one frame / a panic during cleanup

Each frame has a single payload slot (`stack_exc`). A landingpad/cleanup block
that itself catches a *new* exception before the outer `resume` would overwrite
the slot, so the resumed payload could be wrong:

```llvm
cleanup:
  %lp = landingpad { ptr, i64 } cleanup
  invoke void @drop_glue() to label %done unwind label %cleanup2   ; a second in-flight exc
done:
  resume { ptr, i64 } %lp                                          ; which payload?
```

(LLVM defines this as a "cleanup that itself raises" → `std::terminate`; we
neither enforce that nor track two payloads.)

### 6. An uncaught panic as a defined program outcome

A panic that escapes the entry function surfaces as an `LLVM Level Exception`
*error* (an uncaught `LLVMExcE` reaching `MCFGbot`), not as a clean,
distinguished "process aborted by panic" result. A test asserting the
abort-on-uncaught-panic behavior has nothing well-defined to assert against yet.
