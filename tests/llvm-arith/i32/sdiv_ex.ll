define i32 @main(i32 %argc, i8** %arcv) {
  %1 = sdiv exact i32 -5, 2
  ret i32 %1
}
; ASSERT POISON: call i1 @main(i32 1, i8** null)
