define double @main(i8 %argc, i8** %arcv) {
  %1 = uitofp i8 -1 to double
  ret double %1
}

; ASSERT EQ: double 255.0 = call double @main(i64 0, i8** null)

