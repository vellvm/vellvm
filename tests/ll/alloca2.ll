define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 17, i64* %1
  %2 = alloca i64*
  store i64* %1, i64** %2
  %3 = load i64*, i64** %2
  %4 = load i64, i64* %3
  ret i64 %4
}

; ASSERT EQ: i64 17 = call i64 @main(i64 0, i8** null)
