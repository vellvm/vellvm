; LANGREF: the [float 0x<16 hex digits>] literal form is *not* a floating-point
; math operation, so none of the NaN non-determinism applies to it.  The 16
; digits are a double bit pattern which the assembler requires to be exactly
; representable as a float, and the value is the plain bit-level reshaping of
; that pattern: sign kept, 52-bit mantissa field shifted right by 29, quiet bit
; taken from the input rather than forced.  Every expected value below was read
; off `clang -O2` constant-folding the same bitcast.
;
; Discriminates the old implementation, whose double->float narrowing
; (float_to_float32, Numeric/Floats.v) passed Bconv a conv_nan that DISCARDED
; its argument and returned the constant B754_nan 24 128 false 1 -- so every
; NaN literal, whatever its sign, payload or quiet bit, came out as
; 0x7F800001.  Note also that the right fix is not Float.to_single: its
; to_single_nan quiets, which @snan_payload below would catch.

; Quiet NaN, zero payload -- the common case.  Old code: 0x7F800001.
define i32 @qnan() {
  %a = bitcast float 0x7FF8000000000000 to i32
  ret i32 %a
}

; The sign must survive.  Old code dropped it (conv_nan hardcoded sign=false).
define i32 @neg_qnan() {
  %a = bitcast float 0xFFF8000000000000 to i32
  ret i32 %a
}

; A *signaling* NaN whose payload (2^29) survives the 29-bit truncation, so
; LLVM accepts it.  The result stays signaling: 0x7F800001, not 0x7FC00001.
; This is the case that pins "no quieting" and rules out Float.to_single.
define i32 @snan_payload() {
  %a = bitcast float 0x7FF0000020000000 to i32
  ret i32 %a
}

; Widest payload that survives the shift: every mantissa bit above the low 29.
define i32 @max_payload() {
  %a = bitcast float 0x7FFFFFFFE0000000 to i32
  ret i32 %a
}

; Negative signaling NaN: sign kept, quiet bit still clear.
define i32 @neg_snan() {
  %a = bitcast float 0xFFF4000000000000 to i32
  ret i32 %a
}

; For contrast: the double path never narrows, so the pattern is verbatim.
; This one was already correct (Float.of_bits, no conversion involved).
define i64 @qnan_double() {
  %a = bitcast double 0x7FF8000000000000 to i64
  ret i64 %a
}

; An ordinary finite literal that is exactly representable, to check the fix did
; not disturb the non-NaN path.  0x3FF4CCCCC0000000 is 1.3f widened to double.
define i32 @finite_exact() {
  %a = bitcast float 0x3FF4CCCCC0000000 to i32
  ret i32 %a
}

; Payload bit 0 does not survive the 29-bit truncation, so this literal is not
; exactly representable and must be rejected -- clang: "floating point constant
; invalid for type".  The old representability check exempted NaNs outright and
; silently produced 0x7F800001 here.
define i32 @snan_payload_lost() {
  %a = bitcast float 0x7FF0000000000001 to i32
  ret i32 %a
}

; The same rule on a finite value: the true double 1.3 is not an f32.
define i32 @finite_inexact() {
  %a = bitcast float 0x3FF4CCCCCCCCCCCD to i32
  ret i32 %a
}

; ASSERT EQ: i32 2143289344 = call i32 @qnan()
; ASSERT EQ: i32 4290772992 = call i32 @neg_qnan()
; ASSERT EQ: i32 2139095041 = call i32 @snan_payload()
; ASSERT EQ: i32 2147483647 = call i32 @max_payload()
; ASSERT EQ: i32 4288675840 = call i32 @neg_snan()
; ASSERT EQ: i64 9221120237041090560 = call i64 @qnan_double()
; ASSERT EQ: i32 1067869798 = call i32 @finite_exact()
; ASSERT FAILS: call i32 @snan_payload_lost()
; ASSERT FAILS: call i32 @finite_inexact()
