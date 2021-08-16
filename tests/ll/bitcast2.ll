define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca double
  %2 = load double, i64* %1
  %3 = bitcast double %2 to i64
  %4 = sdiv i64 10, %3
  ret i64 %4
}
