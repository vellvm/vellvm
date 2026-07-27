; Examples from the LLVM LangRef's 'ret' Instruction section.
; langref: ret-instruction sha1=22349ce09c69ee52e1653a887b837d01a1cd278a
;
; LangRef 24.0.0git gives the following example(s):
;
; ret i32 5                       ; Return an integer value of 5
; ret void                        ; Return from a void function
; ret { i32, i8 } { i32 4, i8 2 } ; Return a struct of values 4 and 2

define i32 @ret_int() {
  ret i32 5
}

define void @ret_void() {
  ret void
}

define { i32, i8 } @ret_struct() {
  ret { i32, i8 } { i32 4, i8 2 }
}

; ASSERT EQ: i32 5 = call i32 @ret_int()
; ASSERT SUCCEEDS: call void @ret_void()
; ASSERT EQ: { i32, i8 } { i32 4, i8 2 } = call { i32, i8 } @ret_struct()
