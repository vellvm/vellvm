define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 0, i64* %1
  ret i64 42
}

; ASSERT EQ: i64 42 = call i64 @main(i64 0, i8** null)
