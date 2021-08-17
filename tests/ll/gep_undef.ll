define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca [5 x i64]
  %2 = alloca i32
  %3 = load i32, i32* %2
  %4 = getelementptr [5 x i64], [5 x i64]* %1, i32 0, i32 %3
  %5 = load i64, i64* %4
  %6 = icmp eq i64 %5, 0
  %7 = select i1 %6, i64 1, i64 %5
  %8 = sdiv i64 10, %7
  ret i64 0
}
