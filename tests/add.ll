define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca [2 x i64]
  store [2 x i64] [ i64 1, i64 2 ], [2 x i64]* %1
  %2 = and undef, 1
  %3 = getelementptr [2 x i64] [2 x i64]* %1, i32 0, i32 %2
  %4 = load i64* %3
  ret i64 %4
}
