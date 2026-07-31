; Decimal literals at type half.
;
; LangRef documents the exactness requirement only for the hex form ("bfloat,
; half and float values must, however, be exactly representable"), and its
; "Simple Constants" prose about decimals is blanket and does not match the
; implementation.  What clang actually does -- established by probing, and what
; is implemented here -- is: parse the literal as a *double*, then require the
; double->half narrowing to be lossless.  So decimal and hex end up governed by
; the same rule, and clang prints an accepted decimal half back in the 0xH form.
;
; Routing through the double also gets LLVM's *rounding*: computing a binary16
; straight from the decimal rounds once, whereas LLVM rounds
; decimal -> binary64 -> binary16.  Among accepted literals that is moot, since
; they are exact; it only matters for the ones rejected here.
;
; Every accepted/rejected verdict below was checked against
; `clang -x ir -S`, and every value against `clang -O2`.

define i16 @exact_half() {
  %a = bitcast half 1.5 to i16
  ret i16 %a
}

define i16 @exact_int() {
  %a = bitcast half 3.0 to i16
  ret i16 %a
}

define i16 @exact_negative() {
  %a = bitcast half -2.0 to i16
  ret i16 %a
}

; 65504 is the largest finite half and is exactly representable.
define i16 @exact_max() {
  %a = bitcast half 65504.0 to i16
  ret i16 %a
}

; Overflow is *accepted*: 1.0e400 already overflows to an infinity as a double,
; and an infinity narrows exactly.  Same as [float 1.0e400].
define i16 @overflow_to_inf() {
  %a = bitcast half 1.0e400 to i16
  ret i16 %a
}

; Underflow likewise: 1.0e-400 is zero as a double, and zero narrows exactly.
define i16 @underflow_to_zero() {
  %a = bitcast half 1.0e-400 to i16
  ret i16 %a
}

; 2^-24, the smallest subnormal, spelled in decimal.
define i16 @exact_min_subnormal() {
  %a = bitcast half 0.000000059604644775390625 to i16
  ret i16 %a
}

; --- rejections: "floating point constant invalid for type" ---

; 1.3 is a repeating binary fraction.
define i16 @inexact_repeating() {
  %a = bitcast half 1.3 to i16
  ret i16 %a
}

define i16 @inexact_tenth() {
  %a = bitcast half 0.1 to i16
  ret i16 %a
}

; 65520 sits exactly halfway between 65504 (max half) and 65536, so it is not
; representable -- unlike 1.0e400, it does not *already* overflow as a double.
; This is the boundary that a wrong exponent bound in the representability check
; would let through.
define i16 @inexact_just_over_max() {
  %a = bitcast half 65520.0 to i16
  ret i16 %a
}

define i16 @inexact_over_max() {
  %a = bitcast half 65536.0 to i16
  ret i16 %a
}

; 2^-25: one binade below the smallest subnormal.
define i16 @inexact_too_small() {
  %a = bitcast half 0.0000000298023223876953125 to i16
  ret i16 %a
}

; ASSERT EQ: i16 15872 = call i16 @exact_half()
; ASSERT EQ: i16 16896 = call i16 @exact_int()
; ASSERT EQ: i16 49152 = call i16 @exact_negative()
; ASSERT EQ: i16 31743 = call i16 @exact_max()
; ASSERT EQ: i16 31744 = call i16 @overflow_to_inf()
; ASSERT EQ: i16 0 = call i16 @underflow_to_zero()
; ASSERT EQ: i16 1 = call i16 @exact_min_subnormal()
; ASSERT FAILS: call i16 @inexact_repeating()
; ASSERT FAILS: call i16 @inexact_tenth()
; ASSERT FAILS: call i16 @inexact_just_over_max()
; ASSERT FAILS: call i16 @inexact_over_max()
; ASSERT FAILS: call i16 @inexact_too_small()
