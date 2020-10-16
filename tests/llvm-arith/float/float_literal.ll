define float @main(i8 %argc, i8** %arcv) {
  ret float 125.31999969482421875
}

; ASSERT EQ: float 125.31999969482421875 = call float @main(i64 0, i8** null)

