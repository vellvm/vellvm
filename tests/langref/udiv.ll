; Examples from the LLVM LangRef's 'udiv' Instruction section.
; langref: udiv-instruction sha1=c03d689587fc5bdd469955ba5223ee23bc78316e
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = udiv i32 4, %var          ; yields i32:result = 4 / %var

define i32 @udiv_4(i32 %var) {
  %r = udiv i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 2 = call i32 @udiv_4(i32 2)
; ASSERT EQ: i32 1 = call i32 @udiv_4(i32 3)
; The divisor is read as unsigned: -1 is 4294967295, so the quotient is 0.
; ASSERT EQ: i32 0 = call i32 @udiv_4(i32 -1)
