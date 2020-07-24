declare double @llvm.minimum.f64(double, double) #0

; 2nd argument is sNaN
define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.minimum.f64(double 1.0, double 0x7FF0000000000001)
  ret double %1
}
