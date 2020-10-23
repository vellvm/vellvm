declare double @llvm.minimum.f64(double, double) #0

define double @main(i8 %argc, i8** %arcv) {
  %1 = call double @llvm.minimum.f64(double 1.0, double 2.0)
  ret double %1
}

; ASSERT EQ: double 1.0  = call double @main(i64 0, i8** null)

