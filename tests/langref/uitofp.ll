; Examples from the LLVM LangRef's 'uitofp .. to' Instruction section.
; langref: uitofp-to-instruction sha1=594d3a2915251cf747a172122081a04e16976193
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = uitofp i32 257 to float         ; yields float:257.0
; %Y = uitofp i8 -1 to double          ; yields double:255.0
;
; %a = uitofp nneg i32 256 to float    ; yields float:256.0
; %b = uitofp nneg i32 -256 to float   ; yields float poison

define float @uitofp_257() {
  %X = uitofp i32 257 to float
  ret float %X
}

; The source is read as unsigned: i8 -1 is 255.
define double @uitofp_m1() {
  %Y = uitofp i8 -1 to double
  ret double %Y
}

; ASSERT EQ: float 257.0 = call float @uitofp_257()
; ASSERT EQ: double 255.0 = call double @uitofp_m1()
