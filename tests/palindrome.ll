@racecar = global [ 8  x i8 ] c"racecar\00"
@compile = global [ 8  x i8 ] c"compile\00"

define i64 @is_palindrome([8 x i8]* %str) {
  %1 = getelementptr [8 x i8], [8 x i8]* %str, i32 0, i32 0
  %2 = alloca i64
  %3 = alloca i64
  store i64 0, i64* %2
  store i64 6, i64* %3
  br label %loop

loop:
  %4 = load i64, i64* %2
  %5 = getelementptr [8 x i8], [8 x i8]* %str, i32 0, i64 %4
  %6 = load i8, i8* %5
  %7 = load i64, i64* %3
  %8 = getelementptr [8 x i8], [8 x i8]* %str, i32 0, i64 %7
  %9 = load i8, i8* %8
  %10 = icmp eq i8 %6, %9
  br i1 %10, label %move, label %reject

move:
  %11 = add i64 %4, 1
  store i64 %11, i64* %2
  %12 = sub i64 %7, 1
  store i64 %12, i64* %3
  %13 = icmp slt i64 %11, %12
  br i1 %13, label %loop, label %accept

reject:
  ret i64 0

accept:
  ret i64 1
}

define i64 @main(i64 %argc, [8 x i8]* %arcv) {
  %1 = call i64 @is_palindrome([8 x i8]* @racecar)
  %2 = call i64 @is_palindrome([8 x i8]* @compile)
  %3 = shl i64 %2, 4
  %4 = add i64 %1, %3
  ret i64 %1
}
