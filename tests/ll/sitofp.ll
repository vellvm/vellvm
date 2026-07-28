; Examples from the LLVM LangRef's 'sitofp .. to' Instruction section.
; langref: sitofp-to-instruction sha1=7fb41389fde4e615a63deee678782d846a72c74d
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = sitofp i32 257 to float         ; yields float:257.0
; %Y = sitofp i8 -1 to double          ; yields double:-1.0

define float @sitofp_257() {
  %X = sitofp i32 257 to float
  ret float %X
}

; The source is read as signed: i8 -1 is -1.
define double @sitofp_m1() {
  %Y = sitofp i8 -1 to double
  ret double %Y
}

; ASSERT EQ: float 257.0 = call float @sitofp_257()
; ASSERT EQ: double -1.0 = call double @sitofp_m1()
