; LANGREF: llvm.fabs is not a "floating-point math operation" -- it "acts
; directly on the underlying bit representation and never changes anything
; except possibly for the sign bit".  So on a NaN input the result is fully
; determined: quiet bit and payload preserved, sign cleared.
;
; Discriminates the old implementation, which used Flocq's b64_abs/b32_abs
; (whose unop_nan_pl returns the NaN unchanged, sign included) and so returned
; a *negative* NaN here.  The results are bitcast to integers because a
; comparison on the float values themselves cannot see a sign bit on a NaN.

declare double @llvm.fabs.f64(double)
declare float @llvm.fabs.f32(float)

; -qNaN with a non-zero payload: sign cleared, payload kept.
define i64 @fabs_neg_qnan() {
  %a = call double @llvm.fabs.f64(double 0xFFF8000000000123)
  %b = bitcast double %a to i64
  ret i64 %b
}

; Already positive: unchanged.
define i64 @fabs_pos_qnan() {
  %a = call double @llvm.fabs.f64(double 0x7FF8000000000123)
  %b = bitcast double %a to i64
  ret i64 %b
}

; -sNaN: the quiet bit must not be set either -- fabs is not a math operation,
; so it may not quiet its argument.
define i64 @fabs_neg_snan() {
  %a = call double @llvm.fabs.f64(double 0xFFF0000000000123)
  %b = bitcast double %a to i64
  ret i64 %b
}

; Ordinary negative value, for contrast.
define double @fabs_neg_number() {
  %a = call double @llvm.fabs.f64(double -2.5)
  ret double %a
}

; Same story at single precision.  Here we look at the sign bit directly rather
; than at the whole word, so the test does not depend on how the frontend
; narrows the (double-encoded) NaN literal to a float.
define i32 @fabs_neg_qnan_f32_sign() {
  %a = call float @llvm.fabs.f32(float 0xFFF8024600000000)
  %b = bitcast float %a to i32
  %s = lshr i32 %b, 31
  ret i32 %s
}

; ASSERT EQ: i64 9221120237041090851 = call i64 @fabs_neg_qnan()
; ASSERT EQ: i64 9221120237041090851 = call i64 @fabs_pos_qnan()
; ASSERT EQ: i64 9218868437227405603 = call i64 @fabs_neg_snan()
; ASSERT EQ: double 2.5 = call double @fabs_neg_number()
; ASSERT EQ: i32 0 = call i32 @fabs_neg_qnan_f32_sign()
