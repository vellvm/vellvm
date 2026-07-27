; Examples from the LLVM LangRef's 'br' Instruction section.
; langref: br-instruction sha1=e34d0f89add9d2d9dcbe08c4d14ddde19b05c837
;
; LangRef 24.0.0git gives the following example(s):
;
; Test:
;   %cond = icmp eq i32 %a, %b
;   br i1 %cond, label %IfEqual, label %IfUnequal
; IfEqual:
;   ret i32 1
; IfUnequal:
;   ret i32 0

define i32 @Test(i32 %a, i32 %b) {
Test:
  %cond = icmp eq i32 %a, %b
  br i1 %cond, label %IfEqual, label %IfUnequal
IfEqual:
  ret i32 1
IfUnequal:
  ret i32 0
}

; ASSERT EQ: i32 1 = call i32 @Test(i32 17, i32 17)
; ASSERT EQ: i32 0 = call i32 @Test(i32 17, i32 42)
