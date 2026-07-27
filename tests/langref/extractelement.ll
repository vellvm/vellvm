; Examples from the LLVM LangRef's 'extractelement' Instruction section.
; langref: extractelement-instruction sha1=841ba5eacbd438542e08e8d0b82003241c59932c
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = extractelement <4 x i32> %vec, i64 0    ; yields i32

define i32 @extract0(<4 x i32> %vec) {
  %r = extractelement <4 x i32> %vec, i64 0
  ret i32 %r
}

define i32 @extract_at(<4 x i32> %vec, i64 %idx) {
  %r = extractelement <4 x i32> %vec, i64 %idx
  ret i32 %r
}

; ASSERT EQ: i32 10 = call i32 @extract0(<4 x i32> <i32 10, i32 20, i32 30, i32 40>)
; ASSERT EQ: i32 30 = call i32 @extract_at(<4 x i32> <i32 10, i32 20, i32 30, i32 40>, i64 2)
