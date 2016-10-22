define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 17, i64* %1
  %2 = load i64, i64* %1
  ret i64 %2
}
