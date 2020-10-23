define i8 @main(i8 %argc, i8** %arcv) {
  %1 = shl nuw i8 4, 7
  ret i8 %1
}

; ASSERT POISON: call i1 @main(i8 1, i8** null)
