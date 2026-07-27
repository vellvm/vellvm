; Examples from the LLVM LangRef's 'ashr' Instruction section.
; langref: ashr-instruction sha1=0b9e9cd8f004a5605e1411cdddac59907c7f2b96
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = ashr i32 4, 1   ; yields i32:result = 2
; <result> = ashr i32 4, 2   ; yields i32:result = 1
; <result> = ashr i8  4, 3   ; yields i8:result = 0
; <result> = ashr i8 -2, 1   ; yields i8:result = -1
; <result> = ashr i32 1, 32  ; undefined
; <result> = ashr <2 x i32> < i32 -2, i32 4>, < i32 1, i32 3>   ; yields: result=<2 x i32> < i32 -1, i32 0>

define i32 @ashr_4_1() {
  %r = ashr i32 4, 1
  ret i32 %r
}

define i32 @ashr_4_2() {
  %r = ashr i32 4, 2
  ret i32 %r
}

define i8 @ashr_i8_4_3() {
  %r = ashr i8 4, 3
  ret i8 %r
}

; Arithmetic shift replicates the sign bit, so -2 stays negative.
define i8 @ashr_i8_m2_1() {
  %r = ashr i8 -2, 1
  ret i8 %r
}

; LangRef calls a shift amount >= the bit width "undefined"; it produces poison.
define i32 @ashr_1_32() {
  %r = ashr i32 1, 32
  ret i32 %r
}

define <2 x i32> @ashr_vec() {
  %r = ashr <2 x i32> <i32 -2, i32 4>, <i32 1, i32 3>
  ret <2 x i32> %r
}

; ASSERT EQ: i32 2 = call i32 @ashr_4_1()
; ASSERT EQ: i32 1 = call i32 @ashr_4_2()
; ASSERT EQ: i8 0 = call i8 @ashr_i8_4_3()
; ASSERT EQ: i8 -1 = call i8 @ashr_i8_m2_1()
; ASSERT EQ: i32 poison = call i32 @ashr_1_32()
; ASSERT EQ: <2 x i32> <i32 -1, i32 0> = call <2 x i32> @ashr_vec()
