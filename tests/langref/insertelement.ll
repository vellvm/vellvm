; Examples from the LLVM LangRef's 'insertelement' Instruction section.
; langref: insertelement-instruction sha1=eccfcb16e4762ddc5ff0f37d7abe34c56bbfeffa
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = insertelement <4 x i32> %vec, i32 1, i64 0    ; yields <4 x i32>

define <4 x i32> @insert0(<4 x i32> %vec) {
  %r = insertelement <4 x i32> %vec, i32 1, i64 0
  ret <4 x i32> %r
}

; ASSERT EQ: <4 x i32> <i32 1, i32 20, i32 30, i32 40> = call <4 x i32> @insert0(<4 x i32> <i32 10, i32 20, i32 30, i32 40>)
