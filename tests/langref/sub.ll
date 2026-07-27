; Examples from the LLVM LangRef's 'sub' Instruction section.
; langref: sub-instruction sha1=fbb9957bb1913116c76870f2c2bc1850fce67f0f
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = sub i32 4, %var          ; yields i32:result = 4 - %var
; <result> = sub i32 0, %val          ; yields i32:result = -%var

define i32 @sub_from_4(i32 %var) {
  %r = sub i32 4, %var
  ret i32 %r
}

; The idiomatic negation: sub from zero.
define i32 @negate(i32 %val) {
  %r = sub i32 0, %val
  ret i32 %r
}

; ASSERT EQ: i32 1 = call i32 @sub_from_4(i32 3)
; ASSERT EQ: i32 -6 = call i32 @sub_from_4(i32 10)
; ASSERT EQ: i32 -7 = call i32 @negate(i32 7)
; ASSERT EQ: i32 7 = call i32 @negate(i32 -7)
