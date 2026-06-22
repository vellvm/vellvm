define i64 @main(i64 %argc, i8** %arcv) {
  %1 = shl i64 42, 2
  ret i64 %1
}

; ASSERT EQ: i64 168 = call i64 @main(i64 0, i8** null)
