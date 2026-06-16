; Plain-`call` propagation across several frames.
; @level3 panics; @level2 and @level1 reach it with an ordinary `call` (no
; landingpad), so the unwind must propagate through them to the single `invoke`
; in @run. Stresses the value-carried unwind crossing the mrec knot frame by
; frame, and frame teardown along the way.

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %v, i32 %a, i64 %c, i8* %e, i8* %x) {
  ret i64 0
}

define void @level3() {
  call void @llvm.vellvm.internal.throw()
  unreachable
}

define void @level2() {
  call void @level3()
  ret void
}

define void @level1() {
  call void @level2()
  ret void
}

define i64 @run()
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
entry:
  invoke void @level1() to label %ok unwind label %caught
ok:
  ret i64 0
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  ret i64 99
}

; ASSERT EQ: i64 99 = call i64 @run()
