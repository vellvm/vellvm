; Examples from the LLVM LangRef's 'urem' Instruction section.
; langref: urem-instruction sha1=41966cfb05d018e3cb28ba10a619a096ddc36fcb
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = urem i32 4, %var          ; yields i32:result = 4 % %var

define i32 @urem_4(i32 %var) {
  %r = urem i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 1 = call i32 @urem_4(i32 3)
; ASSERT EQ: i32 0 = call i32 @urem_4(i32 2)
; The divisor is read as unsigned: -1 is 4294967295, so 4 is the remainder.
; ASSERT EQ: i32 4 = call i32 @urem_4(i32 -1)
