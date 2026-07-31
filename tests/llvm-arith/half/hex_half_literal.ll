; The [half 0xH....] literal form: four hex digits carrying a raw binary16 bit
; pattern.  Like the [float 0x<16 digits>] form, this is not a floating-point
; math operation, so none of the NaN non-determinism applies -- the value is the
; bit pattern itself, sign, payload and quiet bit taken verbatim from the input.
;
; The lexer (llvm_lexer.mll:590) has produced [FS_hex FH_H] for these since
; before there was any binary16 in the semantics; every arm was [=> None], so
; each of these used to fail as "bad float literal".
;
; Every expected value below was read off `clang -O2` constant-folding the same
; bitcast.

define i16 @inf() {
  %a = bitcast half 0xH7C00 to i16
  ret i16 %a
}

define i16 @neg_inf() {
  %a = bitcast half 0xHFC00 to i16
  ret i16 %a
}

define i16 @one() {
  %a = bitcast half 0xH3C00 to i16
  ret i16 %a
}

define i16 @zero() {
  %a = bitcast half 0xH0000 to i16
  ret i16 %a
}

; Negative zero must not collapse to +0.0.
define i16 @neg_zero() {
  %a = bitcast half 0xH8000 to i16
  ret i16 %a
}

; The smallest subnormal, 2^-24.  Subnormals are where a width-generic
; representability check is easiest to get wrong.
define i16 @min_subnormal() {
  %a = bitcast half 0xH0001 to i16
  ret i16 %a
}

; The largest finite half, 65504.
define i16 @max_normal() {
  %a = bitcast half 0xH7BFF to i16
  ret i16 %a
}

; A quiet NaN: payload 0x200, i.e. only the quiet bit (2^9) set.
define i16 @qnan() {
  %a = bitcast half 0xH7E00 to i16
  ret i16 %a
}

; A *signaling* NaN.  It must stay signaling: 0xH7C01, not 0xH7E01.  This is the
; case that pins "no quieting" for the literal form, and rules out implementing
; it as a [Bconv] with a quieting conv_nan.
define i16 @snan() {
  %a = bitcast half 0xH7C01 to i16
  ret i16 %a
}

; The sign of a NaN must survive too.
define i16 @neg_qnan() {
  %a = bitcast half 0xHFE00 to i16
  ret i16 %a
}

; LLVM also accepts the 16-digit double-pattern form at type half, subject to
; the same exact-representability rule.  0x3FF0000000000000 is 1.0.
define i16 @hex_double_form() {
  %a = bitcast half 0x3FF0000000000000 to i16
  ret i16 %a
}

; ... including for NaNs, where the double payload is narrowed by 42 bits.
; The double quiet NaN 0x7FF8000000000000 has payload 2^51, which survives, and
; the result is the half quiet NaN 0xH7E00.
define i16 @hex_double_form_nan() {
  %a = bitcast half 0x7FF8000000000000 to i16
  ret i16 %a
}

; ASSERT EQ: i16 31744 = call i16 @inf()
; ASSERT EQ: i16 64512 = call i16 @neg_inf()
; ASSERT EQ: i16 15360 = call i16 @one()
; ASSERT EQ: i16 0 = call i16 @zero()
; ASSERT EQ: i16 32768 = call i16 @neg_zero()
; ASSERT EQ: i16 1 = call i16 @min_subnormal()
; ASSERT EQ: i16 31743 = call i16 @max_normal()
; ASSERT EQ: i16 32256 = call i16 @qnan()
; ASSERT EQ: i16 31745 = call i16 @snan()
; ASSERT EQ: i16 65024 = call i16 @neg_qnan()
; ASSERT EQ: i16 15360 = call i16 @hex_double_form()
; ASSERT EQ: i16 32256 = call i16 @hex_double_form_nan()
