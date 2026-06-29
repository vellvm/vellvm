define i64 @main(i64 %argc, i8** %arcv) {
  %1 = sub i64 10, 9
  ret i64 %1
}

; ASSERT EQ: i64 1 = call i64 @main(i64 0, i8** null)
