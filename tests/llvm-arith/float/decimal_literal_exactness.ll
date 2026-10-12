; LLVM parses every decimal floating-point literal as a *double*, and then, at
; type [float], additionally requires that double -> float be lossless.  So the
; decimal and hexadecimal spellings are governed by exactly the same exactness
; rule; clang even prints an accepted decimal float back as the double-encoded
; hex form.  A literal that would need rounding is not a rounded constant, it is
; an error: "floating point constant invalid for type".
;
; Discriminates the previous implementation, which rounded the decimal straight
; to binary32 (Float32.from_parsed) with no exactness gate at all, and so
; accepted every literal below including the ones clang refuses.  Expected
; values read off `clang -O2` folding the same bitcast.
;
; Note tests/memory/loadAndStore.ll:61-64 had already commented out its inexact
; decimal float assertions (0.33, 255.294, 25500.798, 255.12345) with ';;;;'.
; Those are exactly the cases this rule rejects.

; --- Accepted: exactly representable ---------------------------------------

define i32 @exact_half() {
  %a = bitcast float 1.5 to i32
  ret i32 %a
}

define i32 @exact_quarter() {
  %a = bitcast float 0.25 to i32
  ret i32 %a
}

; Exponent form, still exact.
define i32 @exact_exp() {
  %a = bitcast float 1.0e10 to i32
  ret i32 %a
}

; The literal float_literal.ll uses; its long decimal is exactly an f32.
define i32 @exact_long_decimal() {
  %a = bitcast float 125.31999969482421875 to i32
  ret i32 %a
}

define i32 @exact_zero() {
  %a = bitcast float 0.0 to i32
  ret i32 %a
}

; Signed zero must keep its sign through the narrowing.
define i32 @exact_neg_zero() {
  %a = bitcast float -0.0 to i32
  ret i32 %a
}

; Overflows to an infinity already as a double, and infinity narrows exactly,
; so this is accepted rather than rejected.
define i32 @overflow_to_inf() {
  %a = bitcast float 1.0e400 to i32
  ret i32 %a
}

define i32 @overflow_to_neg_inf() {
  %a = bitcast float -1.0e400 to i32
  ret i32 %a
}

; Symmetrically, underflows to zero as a double, and zero narrows exactly.
define i32 @underflow_to_zero() {
  %a = bitcast float 1.0e-400 to i32
  ret i32 %a
}

; --- Rejected: would need rounding ------------------------------------------

; The classic case: 1.3 is a repeating binary fraction.
define i32 @inexact_simple() {
  %a = bitcast float 1.3 to i32
  ret i32 %a
}

define i32 @inexact_tenth() {
  %a = bitcast float 0.1 to i32
  ret i32 %a
}

; Finite and comfortably inside the f32 range, but not on an f32 grid point.
define i32 @inexact_in_range() {
  %a = bitcast float 3.0e38 to i32
  ret i32 %a
}

; 2^24 + 1 -- needs 25 significand bits, one more than f32 has.
define i32 @inexact_integer() {
  %a = bitcast float 16777217.0 to i32
  ret i32 %a
}

; Would land in the f32 subnormal range, where the double has more precision
; than the target can hold.
define i32 @inexact_subnormal() {
  %a = bitcast float 1.0e-45 to i32
  ret i32 %a
}

; ASSERT EQ: i32 1069547520 = call i32 @exact_half()
; ASSERT EQ: i32 1048576000 = call i32 @exact_quarter()
; ASSERT EQ: i32 1343554297 = call i32 @exact_exp()
; ASSERT EQ: i32 1123722199 = call i32 @exact_long_decimal()
; ASSERT EQ: i32 0 = call i32 @exact_zero()
; ASSERT EQ: i32 2147483648 = call i32 @exact_neg_zero()
; ASSERT EQ: i32 2139095040 = call i32 @overflow_to_inf()
; ASSERT EQ: i32 4286578688 = call i32 @overflow_to_neg_inf()
; ASSERT EQ: i32 0 = call i32 @underflow_to_zero()
; ASSERT FAILS: call i32 @inexact_simple()
; ASSERT FAILS: call i32 @inexact_tenth()
; ASSERT FAILS: call i32 @inexact_in_range()
; ASSERT FAILS: call i32 @inexact_integer()
; ASSERT FAILS: call i32 @inexact_subnormal()
