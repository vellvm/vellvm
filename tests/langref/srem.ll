; Examples from the LLVM LangRef's 'srem' Instruction section.
; langref: srem-instruction sha1=26edb3c8fc4ea6566ddbba7f9322faa45d06f4fd
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = srem i32 4, %var          ; yields i32:result = 4 % %var

define i32 @srem_4(i32 %var) {
  %r = srem i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 1 = call i32 @srem_4(i32 3)
; The remainder takes the sign of the dividend, not the divisor.
; ASSERT EQ: i32 1 = call i32 @srem_4(i32 -3)
