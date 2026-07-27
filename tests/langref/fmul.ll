; Examples from the LLVM LangRef's 'fmul' Instruction section.
; langref: fmul-instruction sha1=e6a653e318c628cb1c2396fd312505943f14ac5c
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fmul float 4.0, %var          ; yields float:result = 4.0 * %var

define float @fmul_4(float %var) {
  %r = fmul float 4.0, %var
  ret float %r
}

; ASSERT EQ: float 10.0 = call float @fmul_4(float 2.5)
; ASSERT EQ: float -2.0 = call float @fmul_4(float -0.5)
