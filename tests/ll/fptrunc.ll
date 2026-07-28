; Examples from the LLVM LangRef's 'fptrunc .. to' Instruction section.
; langref: fptrunc-to-instruction sha1=d1b341ea44c338cd913afd5cf077e4911db0d717
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = fptrunc double 16777217.0 to float    ; yields float:16777216.0
; %Y = fptrunc double 1.0E+300 to half       ; yields half:+infinity

; 16777217 is not representable as a float; round-to-nearest-ties-to-even
; brings it down to 16777216.
define float @fptrunc_roundoff() {
  %X = fptrunc double 16777217.0 to float
  ret float %X
}

; The LangRef's second example targets half, which Vellvm does not model.
; double -> float overflows in the same way: 1.0E+300 is beyond float's range,
; so it rounds to +infinity.
define float @fptrunc_overflow() {
  %Y = fptrunc double 1.0E+300 to float
  ret float %Y
}

; Exactly representable values are unchanged.
define float @fptrunc_exact() {
  %Z = fptrunc double 2.5 to float
  ret float %Z
}

; Rounding happens on the way down, not truncation towards zero: the double
; halfway between two floats goes to the one with the even significand.
define float @fptrunc_ties_to_even() {
  %W = fptrunc double 16777219.0 to float
  ret float %W
}

; ASSERT EQ: float 16777216.0 = call float @fptrunc_roundoff()
; ASSERT EQ: float 0x7FF0000000000000 = call float @fptrunc_overflow()
; ASSERT EQ: float 2.5 = call float @fptrunc_exact()
; ASSERT EQ: float 16777220.0 = call float @fptrunc_ties_to_even()
