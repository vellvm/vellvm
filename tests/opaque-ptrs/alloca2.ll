define i64 @main(i64 %argc, ptr %arcv) {
  %1 = alloca i64
  store i64 17, ptr %1
  %2 = alloca ptr
  store ptr %1, ptr %2
  %3 = load ptr, ptr %2
  %4 = load i64, ptr %3
  ret i64 %4
}
