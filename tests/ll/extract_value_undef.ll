define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca [5 x i64]
  %2 = load [5 x i64], [5 x i64]* %1
  %3 = extractvalue [5 x i64] %2, 0
  %4 = icmp eq i64 %3, 0
  %5 = select i1 %4, i64 1, i64 %3
  %6 = sdiv i64 10, %5
  ret i64 0
}
