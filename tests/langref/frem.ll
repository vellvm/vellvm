; Examples from the LLVM LangRef's 'frem' Instruction section.
; langref: frem-instruction sha1=72d12e16f6ca130b0bd5e4a6c425de0a4fdd2666
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = frem float 4.0, %var          ; yields float:result = 4.0 % %var

define float @frem_4(float %var) {
  %r = frem float 4.0, %var
  ret float %r
}

; VELLVM GAP: frem is not implemented -- DynamicValues.v:722 raises
; "unimplemented float operation". Re-enable by restoring the leading
; single ';' once it is:
;; ASSERT EQ: float 1.0 = call float @frem_4(float 3.0)
;; ASSERT EQ: float 0.0 = call float @frem_4(float 2.0)
