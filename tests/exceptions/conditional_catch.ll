; Conditional panic + catch_unwind boundary.
; Exercises BOTH successors of a single invoke, selected by a runtime i1:
;   - %p = 0: callee returns normally -> invoke takes the `to` edge
;   - %p = 1: callee panics          -> invoke takes the `unwind` edge (landingpad)

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %v, i32 %a, i64 %c, i8* %e, i8* %x) {
  ret i64 0
}

; panics iff %p = 1
define void @maybe_panic(i1 %p) {
entry:
  br i1 %p, label %panic, label %ok
panic:
  call void @llvm.vellvm.internal.throw()
  unreachable
ok:
  ret void
}

; returns 0 if the call did not panic, 1 if it panicked and was caught
define i64 @run_catch(i1 %p)
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
entry:
  invoke void @maybe_panic(i1 %p) to label %ok unwind label %caught
ok:
  ret i64 0
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  ret i64 1
}

; ASSERT EQ: i64 0 = call i64 @run_catch(i1 0)
; ASSERT EQ: i64 1 = call i64 @run_catch(i1 1)
