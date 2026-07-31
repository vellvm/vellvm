; Arithmetic at type half.
;
; The binops go through Flocq's [b16_*], defined in Numeric/Floats.v by
; mirroring Flocq's [B32_Bits] section, so that half uses the same NaN
; convention as float and double already do: propagate the *first* NaN operand,
; unchanged and NOT quieted.  Picking CompCert's [Float32.add]-style
; [Archi.choose_nan_*] convention here instead would have given half a third,
; inconsistent policy.
;
; Every expected value below was read off `clang -O2` constant-folding the same
; expression.

define i16 @add() {
  %r = fadd half 0xH3C00, 0xH3C00
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @sub() {
  %r = fsub half 0xH4000, 0xH3C00
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @mul() {
  %r = fmul half 0xH4000, 0xHC000
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @div() {
  %r = fdiv half 0xH3C00, 0xH4000
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @div_by_zero() {
  %r = fdiv half 0xH3C00, 0xH0000
  %a = bitcast half %r to i16
  ret i16 %a
}

; Overflow: 65504 + 65504 rounds up out of range, to +infinity.
define i16 @overflow() {
  %r = fadd half 0xH7BFF, 0xH7BFF
  %a = bitcast half %r to i16
  ret i16 %a
}

; Underflow through the subnormal range down to zero: 2^-23 * 2^-10.
define i16 @underflow() {
  %r = fmul half 0xH0002, 0xH1000
  %a = bitcast half %r to i16
  ret i16 %a
}

; Rounding: adding a value below half an ulp of 1.0 must round back to 1.0
; (round-to-nearest, ties to even -- the default FP environment).  A binop
; implemented at the wrong precision would produce something else here.
define i16 @round_to_nearest() {
  %r = fadd half 0xH3C00, 0xH0801
  %a = bitcast half %r to i16
  ret i16 %a
}

define i16 @fneg() {
  %r = fneg half 0xH3C00
  %a = bitcast half %r to i16
  ret i16 %a
}

; fneg flips the sign bit of a NaN without disturbing the payload, and without
; quieting it -- the operand here is signaling.
define i16 @fneg_snan() {
  %r = fneg half 0xH7C01
  %a = bitcast half %r to i16
  ret i16 %a
}

; Vectors of half need no half-specific code: [eval_fop] already lifts
; [eval_fop_base] elementwise over [DVALUE_Array true].  Checking anyway, since
; that is only true as long as the new dvalue constructor is reached through the
; base dispatch and not special-cased anywhere on the vector path.
define i16 @vector_add() {
  %r = fadd <2 x half> <half 0xH3C00, half 0xH4000>, <half 0xH3C00, half 0xH4000>
  %e = extractelement <2 x half> %r, i32 1
  %a = bitcast half %e to i16
  ret i16 %a
}

define i16 @vector_mul() {
  %r = fmul <2 x half> <half 0xH4000, half 0xH4200>, <half 0xHC000, half 0xH3C00>
  %e = extractelement <2 x half> %r, i32 0
  %a = bitcast half %e to i16
  ret i16 %a
}

; ASSERT EQ: i16 16384 = call i16 @add()
; ASSERT EQ: i16 15360 = call i16 @sub()
; ASSERT EQ: i16 50176 = call i16 @mul()
; ASSERT EQ: i16 14336 = call i16 @div()
; ASSERT EQ: i16 31744 = call i16 @div_by_zero()
; ASSERT EQ: i16 31744 = call i16 @overflow()
; ASSERT EQ: i16 0 = call i16 @underflow()
; ASSERT EQ: i16 15360 = call i16 @round_to_nearest()
; ASSERT EQ: i16 48128 = call i16 @fneg()
; ASSERT EQ: i16 64513 = call i16 @fneg_snan()
; ASSERT EQ: i16 17408 = call i16 @vector_add()
; ASSERT EQ: i16 50176 = call i16 @vector_mul()
