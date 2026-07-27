; Examples from the LLVM LangRef's 'fsub' Instruction section.
; langref: fsub-instruction sha1=aff0eaecf42b94633303022657df5905a37f76d6
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fsub float 4.0, %var           ; yields float:result = 4.0 - %var
; <result> = fsub float -0.0, %val          ; yields float:result = -%var

define float @fsub_from_4(float %var) {
  %r = fsub float 4.0, %var
  ret float %r
}

; Negation via subtraction from -0.0.
define float @negate(float %val) {
  %r = fsub float -0.0, %val
  ret float %r
}

; ASSERT EQ: float 1.5 = call float @fsub_from_4(float 2.5)
; ASSERT EQ: float -3.5 = call float @negate(float 3.5)
