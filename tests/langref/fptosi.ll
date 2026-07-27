; Examples from the LLVM LangRef's 'fptosi .. to' Instruction section.
; langref: fptosi-to-instruction sha1=93328e8c6b26daaf0d12975563be1e7fff51e672
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = fptosi double -123.0 to i32      ; yields i32:-123
; %Y = fptosi float 1.0E-247 to i1      ; yields undefined:1
; %Z = fptosi float 1.04E+17 to i8      ; yields undefined:1

define i32 @fptosi_m123() {
  %X = fptosi double -123.0 to i32
  ret i32 %X
}

; ASSERT EQ: i32 -123 = call i32 @fptosi_m123()
