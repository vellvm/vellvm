define i64 @one_iteration(i64 %n) {
  %1 = shl i64 %n, 1
  %2 = xor i64 %n, %1
  %3 = shl i64 %1, 2
  %4 = xor i64 %2, %3
  %5 = shl i64 %3, 1
  %6 = xor i64 %4, %5
  %7 = lshr i64 %6, 63
  %8 = and i64 %7, 1
  %9 = or i64 %6, %8
  ret i64 %9
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ctr = alloca i64
  store i64 1, i64* %ctr
  %1   = add i64 12, 0
  br i1 1, label %loop, label %loop

loop:
  %2   = load i64, i64* %ctr
  %3   = add i64 %2, 1
  store i64 %3, i64* %ctr
  %4   = call i64 @one_iteration(i64 %2)
  %cmp = icmp eq i64 %3, 5
  br i1 %cmp, label %end, label %loop

end:
  ret i64 %4
}
