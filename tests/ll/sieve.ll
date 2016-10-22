declare i64* @ll_malloc(i64, i64)

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @is_prime (i64 347)
  ret i64 %1
}

define i64 @is_prime(i64 %n) {
  %sieve = call i64* @ll_malloc(i64 8, i64 10000)
  %1 = getelementptr i64, i64* %sieve, i64 0
  store i64 0, i64* %1
  %2 = getelementptr i64, i64* %sieve, i64 1
  store i64 0, i64* %2
  br label %start1

start1:
  %i = alloca i64
  store i64 2, i64* %i
  br label %cmp1

cmp1:
  %3 = load i64, i64* %i
  %4 = icmp slt i64 %3, 10000
  br i1 %4, label %loop1, label %end1
  
loop1:
  %5 = load i64, i64* %i
  %6 = getelementptr i64, i64* %sieve, i64 %5 
  store i64 1, i64* %6
  %7 = add i64 %5, 1
  store i64 %7, i64* %i
  br label %cmp1
  
end1:
  br label %start2

start2:
  store i64 2, i64* %i
  br label %cmp2

cmp2:
  %8 = load i64, i64* %i
  %9 = icmp slt i64 %8, 10000
  br i1 %9, label %loop2, label %end2
  
loop2:
  %10 = load i64, i64* %i
  %11 = getelementptr i64, i64* %sieve, i64 %10
  %12 = load i64, i64* %11
  %13 = icmp eq i64 %12, 1
  br i1 %13, label %then1, label %else1

then1:
  %j = alloca i64
  %14 = add i64 %10, %10
  store i64 %14, i64* %j
  br label %cmp3
cmp3:
  %15 = load i64, i64* %j
  %16 = icmp slt i64 %15, 10000
  br i1 %16, label %loop3, label %end3
loop3:
  %17 = getelementptr i64, i64* %sieve, i64 %15
  store i64 0, i64* %17
  %18 = add i64 %15, %10
  store i64 %18, i64* %j
  br label %cmp3

end3:
  br label %else1

else1:
  %19 = load i64, i64* %i
  %20 = add i64 %19, 1
  store i64 %20, i64* %i
  br label %cmp2

end2:
  %ptr = getelementptr i64, i64* %sieve, i64 %n
  %r = load i64, i64* %ptr
  ret i64 %r 
}
