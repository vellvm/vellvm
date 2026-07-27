; Examples from the LLVM LangRef's 'add' Instruction section.
; langref: add-instruction sha1=f112d762a5b0b1c442d00536b4464de7de8c75f4
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = add i32 4, %var          ; yields i32:result = 4 + %var

define i32 @add_4(i32 %var) {
  %r = add i32 4, %var
  ret i32 %r
}

; ASSERT EQ: i32 42 = call i32 @add_4(i32 38)
; ASSERT EQ: i32 0 = call i32 @add_4(i32 -4)
