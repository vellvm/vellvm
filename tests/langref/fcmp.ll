; Examples from the LLVM LangRef's 'fcmp' Instruction section.
; langref: fcmp-instruction sha1=c24252bebc73c7d6ae25a3831eed03b9e9754e03
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = fcmp oeq float 4.0, 5.0    ; yields: result=false
; <result> = fcmp one float 4.0, 5.0    ; yields: result=true
; <result> = fcmp olt float 4.0, 5.0    ; yields: result=true
; <result> = fcmp ueq double 1.0, 2.0   ; yields: result=false

define i1 @fcmp_oeq() {
  %r = fcmp oeq float 4.0, 5.0
  ret i1 %r
}

define i1 @fcmp_one() {
  %r = fcmp one float 4.0, 5.0
  ret i1 %r
}

define i1 @fcmp_olt() {
  %r = fcmp olt float 4.0, 5.0
  ret i1 %r
}

define i1 @fcmp_ueq() {
  %r = fcmp ueq double 1.0, 2.0
  ret i1 %r
}

; ASSERT EQ: i1 0 = call i1 @fcmp_oeq()
; ASSERT EQ: i1 1 = call i1 @fcmp_one()
; ASSERT EQ: i1 1 = call i1 @fcmp_olt()
; ASSERT EQ: i1 0 = call i1 @fcmp_ueq()
