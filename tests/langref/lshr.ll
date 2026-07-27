; Examples from the LLVM LangRef's 'lshr' Instruction section.
; langref: lshr-instruction sha1=c264c15747507b02cd5d78dd51a915934146947f
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = lshr i32 4, 1   ; yields i32:result = 2
; <result> = lshr i32 4, 2   ; yields i32:result = 1
; <result> = lshr i8  4, 3   ; yields i8:result = 0
; <result> = lshr i8 -2, 1   ; yields i8:result = 0x7F
; <result> = lshr i32 1, 32  ; undefined
; <result> = lshr <2 x i32> < i32 -2, i32 4>, < i32 1, i32 2>   ; yields: result=<2 x i32> < i32 0x7FFFFFFF, i32 1>

define i32 @lshr_4_1() {
  %r = lshr i32 4, 1
  ret i32 %r
}

define i32 @lshr_4_2() {
  %r = lshr i32 4, 2
  ret i32 %r
}

define i8 @lshr_i8_4_3() {
  %r = lshr i8 4, 3
  ret i8 %r
}

; Logical shift feeds in zeros, so -2 (0xFE) becomes 0x7F.
define i8 @lshr_i8_m2_1() {
  %r = lshr i8 -2, 1
  ret i8 %r
}

; LangRef calls a shift amount >= the bit width "undefined"; it produces poison.
define i32 @lshr_1_32() {
  %r = lshr i32 1, 32
  ret i32 %r
}

define <2 x i32> @lshr_vec() {
  %r = lshr <2 x i32> <i32 -2, i32 4>, <i32 1, i32 2>
  ret <2 x i32> %r
}

; ASSERT EQ: i32 2 = call i32 @lshr_4_1()
; ASSERT EQ: i32 1 = call i32 @lshr_4_2()
; ASSERT EQ: i8 0 = call i8 @lshr_i8_4_3()
; ASSERT EQ: i8 127 = call i8 @lshr_i8_m2_1()
; ASSERT EQ: i32 poison = call i32 @lshr_1_32()
; ASSERT EQ: <2 x i32> <i32 2147483647, i32 1> = call <2 x i32> @lshr_vec()
