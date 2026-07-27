; Examples from the LLVM LangRef's 'and' Instruction section.
; langref: and-instruction sha1=09e003b28a736709d69507add31331da1418d85f
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = and i32 4, %var         ; yields i32:result = 4 & %var
; <result> = and i32 15, 40          ; yields i32:result = 8
; <result> = and i32 4, 8            ; yields i32:result = 0

define i32 @and_4(i32 %var) {
  %r = and i32 4, %var
  ret i32 %r
}

define i32 @and_15_40() {
  %r = and i32 15, 40
  ret i32 %r
}

define i32 @and_4_8() {
  %r = and i32 4, 8
  ret i32 %r
}

; ASSERT EQ: i32 4 = call i32 @and_4(i32 -1)
; ASSERT EQ: i32 0 = call i32 @and_4(i32 8)
; ASSERT EQ: i32 8 = call i32 @and_15_40()
; ASSERT EQ: i32 0 = call i32 @and_4_8()
