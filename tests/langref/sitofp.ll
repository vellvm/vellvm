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
;
; VELLVM GAP: sitofp is wrong for every negative input. Conversion.v:154-164
; takes the correct signed value but converts it with the *unsigned* CompCert
; primitives (Float32.of_intu / Float.of_longu applied to `repr (signed i1)`),
; so i8 -1 comes back as 2^64 rather than -1.0. The signed counterparts
; Float32.of_int / Float.of_long sit right beside them in Numeric/Floats.v.
; Re-enable by restoring the leading single ';' once that is fixed:
;; ASSERT EQ: double -1.0 = call double @sitofp_m1()
