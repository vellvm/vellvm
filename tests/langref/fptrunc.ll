; Examples from the LLVM LangRef's 'fptrunc .. to' Instruction section.
; langref: fptrunc-to-instruction sha1=d1b341ea44c338cd913afd5cf077e4911db0d717
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = fptrunc double 16777217.0 to float    ; yields float:16777216.0
; %Y = fptrunc double 1.0E+300 to half       ; yields half:+infinity

; 16777217 is not representable as a float; it rounds to 16777216.
define float @fptrunc_roundoff() {
  %X = fptrunc double 16777217.0 to float
  ret float %X
}

; VELLVM GAP: fptrunc is not implemented -- Conversion.v:227 raises
; "TODO: unimplemented numeric conversion" for the whole Fptrunc case.
; Re-enable by restoring the leading single ';' once it is:
;; ASSERT EQ: float 16777216.0 = call float @fptrunc_roundoff()
