; LANGREF: on fpext, "if a NaN payload is propagated from the input [...] it is
; copied to the high order bits of the resulting payload, and the remaining low
; order bits are zero".  On fptrunc, "the low order bits of the NaN payload
; which cannot fit in the resulting type are discarded".
;
; Discriminates the old float_to_double / double_to_float, which rolled their
; own conv_nan returning a constant, and so flattened every NaN to the default
; one -- legal (the "Preferred NaN" case is always an option) but lossy, and
; inconsistent with the binops, which propagate.
;
; float has a 23-bit significand and double a 52-bit one, so the payload shift
; is by 29 bits in both directions.

; A float qNaN whose payload is 1 (bit 0 set) widens to a double qNaN whose
; payload is 1 << 29.
define i64 @fpext_payload() {
  %f = bitcast i32 2143289345 to float          ; 0x7FC00001, qNaN payload 1
  %d = fpext float %f to double
  %b = bitcast double %d to i64
  ret i64 %b
}

; The reverse trip narrows it back.
define i32 @fptrunc_payload() {
  %d = bitcast i64 9221120237577961472 to double ; 0x7FF8000020000000
  %f = fptrunc double %d to float
  %b = bitcast float %f to i32
  ret i32 %b
}

; Payload bits that do not fit are discarded, not rounded: the low 29 bits go.
define i32 @fptrunc_discards_low_bits() {
  %d = bitcast i64 9221120237577961473 to double ; 0x7FF8000020000001
  %f = fptrunc double %d to float
  %b = bitcast float %f to i32
  ret i32 %b
}

; When every payload bit falls off the bottom, the result is the preferred
; quiet NaN rather than an infinity -- the LangRef calls this case out.
define i32 @fptrunc_payload_vanishes() {
  %d = bitcast i64 9221120237041090851 to double ; 0x7FF8000000000123
  %f = fptrunc double %d to float
  %b = bitcast float %f to i32
  ret i32 %b
}

; ASSERT EQ: i64 9221120237577961472 = call i64 @fpext_payload()
; ASSERT EQ: i32 2143289345 = call i32 @fptrunc_payload()
; ASSERT EQ: i32 2143289345 = call i32 @fptrunc_discards_low_bits()
; ASSERT EQ: i32 2143289344 = call i32 @fptrunc_payload_vanishes()
