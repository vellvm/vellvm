define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add nuw i64 -1, 2
  ret i64 %1
}

; ASSERT POISON: call i64 @main(i64 1, i8** null)
