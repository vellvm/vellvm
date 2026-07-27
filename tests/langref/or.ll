; Examples from the LLVM LangRef's 'or' Instruction section.
; langref: or-instruction sha1=79e03b7f5a9f4760eff0844022be922f83512e70
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = or i32 4, %var         ; yields i32:result = 4 | %var
; <result> = or i32 15, 40          ; yields i32:result = 47
; <result> = or i32 4, 8            ; yields i32:result = 12

define i32 @or_4(i32 %var) {
  %r = or i32 4, %var
  ret i32 %r
}

define i32 @or_15_40() {
  %r = or i32 15, 40
  ret i32 %r
}

define i32 @or_4_8() {
  %r = or i32 4, 8
  ret i32 %r
}

; ASSERT EQ: i32 5 = call i32 @or_4(i32 1)
; ASSERT EQ: i32 47 = call i32 @or_15_40()
; ASSERT EQ: i32 12 = call i32 @or_4_8()
