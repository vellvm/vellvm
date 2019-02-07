declare double @llvm.fabs.f64(double)

define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.fabs.f64(double -1.0)
  ret double %1
}
