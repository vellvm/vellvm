; TEST-ARGS: -succinct

define i32 @src(i32 %x) {
  ret i32 %x
}

define i32 @tgt(i32 %x) {
  %y = add i32 %x, 0
  ret i32 %y
}

; CHECK: Transformation seems to be correct!
; CHECK-NOT: define i32 @src

; aasdawd ASSERT EQ: i32 -2368 = call i32 @tgt(i32 -2368) 
; ASSERT SRCTGT 200
; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
