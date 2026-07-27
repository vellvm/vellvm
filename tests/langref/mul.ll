; Examples from the LLVM LangRef's 'mul' Instruction section.
; langref: mul-instruction sha1=7aa94baf0285f57c99ea0b8848b16f586646e88a
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = mul i32 4, %var          ; yields i32:result = 4 * %var

define i32 @mul_4(i32 %var) {
  %r = mul i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 24 = call i32 @mul_4(i32 6)
; ASSERT EQ: i32 -8 = call i32 @mul_4(i32 -2)
