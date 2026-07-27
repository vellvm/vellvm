; Examples from the LLVM LangRef's 'fadd' Instruction section.
; langref: fadd-instruction sha1=d206883b04778f9fa180bed6f72fb91d4a974514
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fadd float 4.0, %var          ; yields float:result = 4.0 + %var

define float @fadd_4(float %var) {
  %r = fadd float 4.0, %var
  ret float %r
}

; ASSERT EQ: float 6.5 = call float @fadd_4(float 2.5)
; ASSERT EQ: float 0.0 = call float @fadd_4(float -4.0)
