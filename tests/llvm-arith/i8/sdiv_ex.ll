define i8 @main(i8 %argc, i8** %arcv) {
  %1 = sdiv exact i8 -5, 2
  ret i8 %1
}
; ASSERT EQ i8 poison = call i8 @main(i8 1, i8** null)
