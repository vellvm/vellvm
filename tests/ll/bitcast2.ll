define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca double
  %2 = load double, double* %1
  %3 = bitcast double %2 to i64
  %4 = icmp eq i64 %3, 0
  %5 = select i1 %4, i64 1, i64 %3
  %6 = sdiv i64 10, %5
  ret i64 0
}
