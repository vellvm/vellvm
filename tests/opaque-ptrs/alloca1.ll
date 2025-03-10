define i64 @main(i64 %argc, ptr %arcv) {
  %1 = alloca i64
  store i64 17, ptr %1
  %2 = load i64, ptr %1
  ret i64 %2
}
