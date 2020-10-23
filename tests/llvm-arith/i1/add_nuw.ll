define i1 @main(i1 %argc, i8** %arcv) {
  %1 = add nuw i1 1, 1
  ret i1 %1
}

; ASSERT POISON: call i1 @main(i1 1, i8** null)