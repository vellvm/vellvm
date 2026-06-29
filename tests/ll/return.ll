define i64 @main(i64 %argc, i8** %arcv) {
  ret i64 0
}

; ASSERT EQ: i64 0 = call i64 @main(i64 0, i8** null)
