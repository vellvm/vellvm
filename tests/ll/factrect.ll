define i64 @factorial(i64 %n) {
  %cmp = icmp eq i64 %n, 0
  br i1 %cmp, label %ret1, label %recurse

ret1:
  ret i64 1

recurse:
  %1 = sub i64 %n, 1
  %2 = call i64 @factorial(i64 %1)
  %3 = mul i64 %n, %2
  ret i64 %3
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @factorial(i64 5)
  ret i64 %1
}

