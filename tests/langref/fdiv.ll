; Examples from the LLVM LangRef's 'fdiv' Instruction section.
; langref: fdiv-instruction sha1=2aeb80e50f33ed40199b2262eafe22ed986afe5c
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fdiv float 4.0, %var          ; yields float:result = 4.0 / %var

define float @fdiv_4(float %var) {
  %r = fdiv float 4.0, %var
  ret float %r
}

; ASSERT EQ: float 2.0 = call float @fdiv_4(float 2.0)
; ASSERT EQ: float 8.0 = call float @fdiv_4(float 0.5)
