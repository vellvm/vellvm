; Examples from the LLVM LangRef's 'fneg' Instruction section.
; langref: fneg-instruction sha1=f24e6b79497e4d57f6002a13037b5fc31680265f
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fneg float %val          ; yields float:result = -%var

define float @fneg_f(float %val) {
  %r = fneg float %val
  ret float %r
}

; ASSERT EQ: float -3.5 = call float @fneg_f(float 3.5)
; ASSERT EQ: float 3.5 = call float @fneg_f(float -3.5)
