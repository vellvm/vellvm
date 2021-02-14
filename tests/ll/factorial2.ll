define i64 @factorial(i64 %n) {
  %acc = alloca i64
  store i64 1, i64* %acc
  br label %start

start:
  %n1 = phi i64 [%n, %0], [%n2, %then]
  %c = icmp sgt i64 %n1, 0
  br i1 %c, label %then, label %end

then:
  %x1 = load i64, i64* %acc
  %x2 = mul i64 %x1, %n1
  store i64 %x2, i64* %acc
  %n2 = sub i64 %n1, 1
  br label %start

end:
  %ans = load i64, i64* %acc
  ret i64 %ans
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 0, i64* %1
  %2 = call i64 @factorial(i64 5)
  ret i64 %2
}

