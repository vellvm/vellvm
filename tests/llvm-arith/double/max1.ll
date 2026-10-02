declare double @llvm.maxnum.f64(double, double) #0

; 1st argument is qNaN.  LANGREF: "If one operand is qNaN and another
; operand is a number, returns the number."  This file previously asserted the
; qNaN, pinning down a bug in Float_maxnum.
define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.maxnum.f64(double 0x7FF8000000000000, double 2.0)
  ret double %1
}

; ASSERT EQ: double 2.0 = call double @main(i64 0, i8** null)

