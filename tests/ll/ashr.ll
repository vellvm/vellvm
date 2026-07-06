define i64 @main(i64 %argc, i8** %arcv) {
  %1 = ashr i64 42, 3
  ret i64 %1
}

; ASSERT EQ: i64 5 = call i64 @main(i64 0, i8** null)
