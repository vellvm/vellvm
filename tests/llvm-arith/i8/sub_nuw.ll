define i8 @main(i8 %argc, i8** %arcv) {
  %1 = sub nuw i8 0, 1
  ret i8 %1
}

; ASSERT POISON: call i1 @main(i8 1, i8** null)
