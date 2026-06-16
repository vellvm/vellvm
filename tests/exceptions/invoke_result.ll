; Invoke binding a non-void result on the normal path: %v is *defined by* the
; invoke and used afterwards. Exercises the [inr returned_value => lwrite id]
; branch with a real value, alongside the catch path.

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %v, i32 %a, i64 %c, i8* %e, i8* %x) {
  ret i64 0
}

; returns %x on the normal path, panics iff %p = 1
define i64 @id_or_panic(i1 %p, i64 %x) {
entry:
  br i1 %p, label %panic, label %ok
panic:
  call void @llvm.vellvm.internal.throw()
  unreachable
ok:
  ret i64 %x
}

define i64 @use(i1 %p, i64 %x)
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
entry:
  %v = invoke i64 @id_or_panic(i1 %p, i64 %x) to label %ok unwind label %caught
ok:
  %r = add i64 %v, 1
  ret i64 %r
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  ret i64 999
}

; ASSERT EQ: i64 43 = call i64 @use(i1 0, i64 42)
; ASSERT EQ: i64 999 = call i64 @use(i1 1, i64 42)
