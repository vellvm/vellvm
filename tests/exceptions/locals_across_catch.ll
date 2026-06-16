; A local (%doubled) computed before the invoke is used in BOTH successors,
; including the landingpad block. Checks that frame-local state survives the
; unwind/catch: in design A the frame is never popped on the caught path, so
; the landingpad sees the same locals.

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %v, i32 %a, i64 %c, i8* %e, i8* %x) {
  ret i64 0
}

define void @maybe_panic(i1 %p) {
entry:
  br i1 %p, label %panic, label %ok
panic:
  call void @llvm.vellvm.internal.throw()
  unreachable
ok:
  ret void
}

define i64 @compute(i1 %p, i64 %base)
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
entry:
  %doubled = add i64 %base, %base
  invoke void @maybe_panic(i1 %p) to label %ok unwind label %caught
ok:
  %r1 = add i64 %doubled, 1
  ret i64 %r1
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  %r2 = add i64 %doubled, 1000
  ret i64 %r2
}

; ASSERT EQ: i64 11 = call i64 @compute(i1 0, i64 5)
; ASSERT EQ: i64 1010 = call i64 @compute(i1 1, i64 5)
