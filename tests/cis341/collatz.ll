define i64 @collatz(i64 %n) {
  %cmp = icmp sgt i64 %n, 1
  br i1 %cmp, label %then, label %ret0
then:
  %4 = shl i64 %n, 63
  %5 = ashr i64 %4, 63
  %6 = icmp eq i64 %5, 0
  br i1 %6, label %even, label %odd
ret0:
  ret i64 0
even:
  %7 = ashr i64 %n, 1
  %8 = call i64 @collatz(i64 %7)
  %9 = add i64 %8, 1
  ret i64 %9
odd:
  %7 = mul i64 3, %n
  %8 = add i64 1, %7 
  %9 = call i64 @collatz(i64 %8)
  %10 = add i64 1, %9
  ret i64 %10
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @collatz(i64 7426)
  ret i64 %1
}