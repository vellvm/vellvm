define float @main(i8 %argc, i8** %arcv) {
  %1 = uitofp i8 10 to float
  ret float %1
}

; ASSERT EQ: float 10.0 = call float @main(i64 0, i8** null)

