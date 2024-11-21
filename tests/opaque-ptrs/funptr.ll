define i64 @factorial(i64 %n) {
  %1 = alloca i64
  %acc = alloca i64
  store i64 %n, ptr %1
  store i64 1, ptr %acc
  br label %start

start:
  %2 = load i64, ptr %1
  %3 = icmp sgt i64 %2, 0
  br i1 %3, label %then, label %end

then:
  %4 = load i64, ptr %acc
  %5 = load i64, ptr %1
  %6 = mul i64 %4, %5
  store i64 %6, ptr %acc
  %7 = load i64, ptr %1
  %8 = sub i64 %7, 1
  store i64 %8, ptr %1
  br label %start

end:
  %9 = load i64, ptr %acc
  ret i64 %9
}

define i64 @callFun(ptr %f) {
  %ans = call i64 %f(i64 5)
  ret i64 %ans
}


define i64 @main(i64 %argc, ptr %arcv) {
  %1 = alloca i64
  store i64 0, ptr %1
  %2 = call i64 @callFun(ptr@factorial)
  ret i64 %2
}

