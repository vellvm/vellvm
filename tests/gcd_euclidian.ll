define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  %2 = alloca i64
  store i64 8, i64* %1
  store i64 10, i64* %2
  br label %gcd

gcd:
  %3 = load i64, i64* %1
  %4 = icmp eq i64 0, %3
  br i1 %4, label %ret_b, label %loop

loop:
  %5 = load i64, i64* %2
  %6 = icmp eq i64 0, %5
  br i1 %6, label %ret_a, label %continue_loop

continue_loop:
  %7 = load i64, i64* %1
  %8 = icmp sgt i64 %7, %5
  br i1 %8, label %if, label %else
  
if:
  %9 = sub i64 %7, %5
  store i64 %9, i64* %1
  br label %loop ; SHOULD BE "LOOP"

else:
  %10 = sub i64 %5, %7
  store i64 %10, i64* %2
  br label %loop ; SHOULD BE LOOP 

ret_a:
  %11 = load i64, i64* %1
  ret i64 %11

ret_b:
  %12 = load i64, i64* %2
  ret i64 %12
}
