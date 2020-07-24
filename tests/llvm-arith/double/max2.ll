declare double @llvm.maxnum.f64(double, double) #0

; 2nd argument is qNaN
define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.maxnum.f64(double 1.0, double 0x7FF8000000000000)
  ret double %1
}
