; The non-integral arguments are spelled in hex because a decimal literal at
; type float must be exactly representable as an f32 -- llvm-as rejects
; `float 123.1` outright. Each hex constant below is the double encoding of
; the f32 these assertions used to name in decimal, i.e. exactly what clang
; emits, so the values under test are unchanged. 0x7FF0000000000000 is +inf,
; which is what the old `float 1.0E+300` overflowed to anyway.

define i8 @to_i8(float %f) {
  %ans = fptoui float %f to i8
  ret i8 %ans
}   

; ASSERT EQ: i8 poison = call i8 @to_i8(float 0x7FF0000000000000)
; ASSERT EQ: i8 poison = call i8 @to_i8(float 0x437717B720000000)
; ASSERT EQ: i8 123 = call i8 @to_i8(float 123.0)
; ASSERT EQ: i8 123 = call i8 @to_i8(float 0x405EC66660000000)
; ASSERT EQ: i8 122 = call i8 @to_i8(float 0x405EB999A0000000)


define i1 @to_i1(float %f) {
  %Z = fptoui float %f to i1 
  ret i1 %Z
}

; ASSERT EQ: i1 poison = call i1 @to_i1(float 0x7FF0000000000000)
; ASSERT EQ: i1 poison = call i1 @to_i1(float 0x437717B720000000)
; ASSERT EQ: i1 0 = call i1 @to_i1(float 0.0)
; ASSERT EQ: i1 0 = call i1 @to_i1(float 0.75)
; ASSERT EQ: i1 1 = call i1 @to_i1(float 1.0)
