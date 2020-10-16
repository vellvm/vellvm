declare double @llvm.maxnum.f64(double, double) #0

; both arguments is sNaN
define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.maxnum.f64(double 0x7FF0000000000001, double 0x7FF0000000000001)
  ret double %1
}

; ASSERT EQ: double 0x7FF0000000000001 = call double @main(i64 0, i8** null)

