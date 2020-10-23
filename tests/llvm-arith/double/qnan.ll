define double @main(i8 %argc, i8** %arcv) {
  %1 = fadd double 0x7FF8000000000000, 3.14
  ret double %1
}

; ASSERT EQ: double 0x7FF0000000000001 = call double @main(i64 0, i8** null)

