define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca {i32, {i32, i64}}
  %2 = getelementptr {i32, {i32, i64}}, {i32, {i32, i64}}* %1, i32 0, i32 1, i32 1
  store i64 5, i64* %2
  %3 = getelementptr {i32, {i32, i64}}, {i32, {i32, i64}}* %1, i32 0, i32 1, i32 1
  %4 = load i64, i64* %3
  ret i64 %4
}
