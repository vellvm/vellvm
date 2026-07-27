; Examples from the LLVM LangRef's 'sdiv' Instruction section.
; langref: sdiv-instruction sha1=246dfcf060ce9e3c9558f7749e81ce785a619a62
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = sdiv i32 4, %var          ; yields i32:result = 4 / %var

define i32 @sdiv_4(i32 %var) {
  %r = sdiv i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 2 = call i32 @sdiv_4(i32 2)
; Signed division truncates towards zero.
; ASSERT EQ: i32 -1 = call i32 @sdiv_4(i32 -3)
