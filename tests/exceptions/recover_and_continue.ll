; catch_unwind that *recovers*: @guarded catches the panic and returns normally,
; so its caller @outer observes an ordinary value (no unwind reaches @outer) and
; keeps computing. Exercises a frame that catches returning via the normal (inr)
; path, and a plain `call` to it consuming that value.

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

; returns 3 on the normal path, 7 if it caught a panic; never unwinds to caller
define i64 @guarded(i1 %p)
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
entry:
  invoke void @maybe_panic(i1 %p) to label %ok unwind label %caught
ok:
  ret i64 3
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  ret i64 7
}

; @guarded never unwinds, so a plain `call` suffices; add 100 to its result
define i64 @outer(i1 %p) {
  %r = call i64 @guarded(i1 %p)
  %s = add i64 %r, 100
  ret i64 %s
}

; ASSERT EQ: i64 103 = call i64 @outer(i1 0)
; ASSERT EQ: i64 107 = call i64 @outer(i1 1)
