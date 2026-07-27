; Examples from the LLVM LangRef's 'shl' Instruction section.
; langref: shl-instruction sha1=479bf35965a9e1d9f8a59bc39d0d455fabb5e8db
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = shl i32 4, %var   ; yields i32: 4 << %var
; <result> = shl i32 4, 2      ; yields i32: 16
; <result> = shl i32 1, 10     ; yields i32: 1024
; <result> = shl i32 1, 32     ; undefined
; <result> = shl <2 x i32> < i32 1, i32 1>, < i32 1, i32 2>   ; yields: result=<2 x i32> < i32 2, i32 4>

define i32 @shl_4(i32 %var) {
  %r = shl i32 4, %var
  ret i32 %r
}

define i32 @shl_4_2() {
  %r = shl i32 4, 2
  ret i32 %r
}

define i32 @shl_1_10() {
  %r = shl i32 1, 10
  ret i32 %r
}

; LangRef calls a shift amount >= the bit width "undefined"; it produces poison.
define i32 @shl_1_32() {
  %r = shl i32 1, 32
  ret i32 %r
}

define <2 x i32> @shl_vec() {
  %r = shl <2 x i32> <i32 1, i32 1>, <i32 1, i32 2>
  ret <2 x i32> %r
}

; ASSERT EQ: i32 8 = call i32 @shl_4(i32 1)
; ASSERT EQ: i32 16 = call i32 @shl_4_2()
; ASSERT EQ: i32 1024 = call i32 @shl_1_10()
; ASSERT EQ: i32 poison = call i32 @shl_1_32()
; ASSERT EQ: <2 x i32> <i32 2, i32 4> = call <2 x i32> @shl_vec()
