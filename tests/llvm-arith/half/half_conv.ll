; Conversions into and out of half.
;
; Before binary16 existed in the semantics, double->float was the only narrowing
; [dvalue_base] could express, so the LangRef's own second [fptrunc] example
; ("fptrunc double 1.0E+300 to half -- yields half:+infinity") was out of reach.
; @trunc_double_overflow below is that example.
;
; NaN payload handling follows LangRef: widening copies the payload into the
; high order bits and zeroes the rest (a left shift by the mantissa-width
; difference: 13 bits to float, 42 to double), narrowing discards the low order
; bits that do not fit.
;
; bitcast needs no half-specific code at all: it goes through serialization, so
; i16 <-> half falls out of [dvalue_base_extract_byte] and
; [memory_bytes_to_dvalue] once those know about halves.
;
; Every expected value below was read off `clang -O2`.

; --- fpext ---

define i32 @ext_to_float() {
  %r = fpext half 0xH3C00 to float
  %a = bitcast float %r to i32
  ret i32 %a
}

; The smallest half subnormal is an ordinary normal number as a double.
define i64 @ext_to_double() {
  %r = fpext half 0xH0001 to double
  %a = bitcast double %r to i64
  ret i64 %a
}

; Widening a quiet NaN: payload 0x200 shifts left by 13 to 2^22, giving
; 0x7FC00000.  A conv_nan that flattened the payload to a constant would be
; legal per LangRef but would not match clang here.
define i32 @ext_qnan() {
  %r = fpext half 0xH7E00 to float
  %a = bitcast float %r to i32
  ret i32 %a
}

; --- fptrunc ---

define i16 @trunc_float() {
  %r = fptrunc float 1.5 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

; The LangRef example.
define i16 @trunc_double_overflow() {
  %r = fptrunc double 1.0E+300 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

; Genuine rounding: 0x3FF3333333333333 is just under 1.2, which is not a half.
define i16 @trunc_double_rounds() {
  %r = fptrunc double 0x3FF3333333333333 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @trunc_double_nan() {
  %r = fptrunc double 0x7FF8000000000000 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

; --- float <-> int ---

define i32 @half_to_sint() {
  %r = fptosi half 0xH4200 to i32
  ret i32 %r
}

define i32 @half_to_sint_neg() {
  %r = fptosi half 0xHC200 to i32
  ret i32 %r
}

define i32 @half_to_uint() {
  %r = fptoui half 0xH4200 to i32
  ret i32 %r
}

define i16 @sint_to_half() {
  %r = sitofp i32 -3 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

; 100000 is beyond the half range, so it rounds to +infinity.
define i16 @uint_to_half_overflow() {
  %r = uitofp i32 100000 to half
  %a = bitcast half %r to i16
  ret i16 %a
}

; --- bitcast, both directions ---

define i16 @bitcast_round_trip() {
  %i = bitcast half 0xH7BFF to i16
  %h = bitcast i16 %i to half
  %a = bitcast half %h to i16
  ret i16 %a
}

; ASSERT EQ: i32 1065353216 = call i32 @ext_to_float()
; ASSERT EQ: i64 4499096027743125504 = call i64 @ext_to_double()
; ASSERT EQ: i32 2143289344 = call i32 @ext_qnan()
; ASSERT EQ: i16 15872 = call i16 @trunc_float()
; ASSERT EQ: i16 31744 = call i16 @trunc_double_overflow()
; ASSERT EQ: i16 15565 = call i16 @trunc_double_rounds()
; ASSERT EQ: i16 32256 = call i16 @trunc_double_nan()
; ASSERT EQ: i32 3 = call i32 @half_to_sint()
; ASSERT EQ: i32 -3 = call i32 @half_to_sint_neg()
; ASSERT EQ: i32 3 = call i32 @half_to_uint()
; ASSERT EQ: i16 49664 = call i16 @sint_to_half()
; ASSERT EQ: i16 31744 = call i16 @uint_to_half_overflow()
; ASSERT EQ: i16 31743 = call i16 @bitcast_round_trip()
