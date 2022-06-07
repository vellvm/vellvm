define i64 @fibonacci(i64 %x) {
  %1 = icmp sle i64 %x, 1
  br i1 %1, label %base_case, label %recurse
base_case:
  ret i64 %x
recurse:
  %2 = sub i64 %x, 1
  %3 = sub i64 %x, 2
  %4 = call i64 @fibonacci(i64 %2)
  %5 = call i64 @fibonacci(i64 %3)
  %6 = add i64 %4, %5
  ret i64 %6
}

define i64 @main(i64 %argc, i8** %argv) {
  %result = call i64 @fibonacci(i64 6)
  ret i64 %result
}


