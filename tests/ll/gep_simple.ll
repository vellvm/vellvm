define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca {i32, {i32, i64}}
  %2 = getelementptr {i32, {i32, i64}}, {i32, {i32, i64}}* %1, i32 0, i32 1, i32 1
  store i32 5, i32* %2
  %3 = getelementptr {i32, {i32, i64}}, {i32, {i32, i64}}* %1, i32 0, i32 1, i32 1
  %4 = load i32, i32* %3
  ret i32 %4
}