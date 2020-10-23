define i64 @main(i64 %argc, i8** %arcv) {
  %1 = xor i64 0, 0
  ret i64 %1
}

; ASSERT EQ: i64 0 = call i64 @main(i64 1, i8** null)