define i64 @loop() {
  %1 = alloca i64
  store i64 100, i64* %1
  br label %start

start:
  %2 = load i64, i64* %1
  %3 = icmp eq i64 %2, 0
  br i1 %3, label %end, label %then

then:
  %4 = load i64, i64* %1
  %5 = sub i64 %4, 1
  store i64 %5, i64* %1
  br label %start

end:
  ret i64 0
}

define i32 @main(i32 %argc, i8** %argv) {
  %ans = call i64 @loop()
  ret i32 0
}  


; ASSERT EQ: i64 0 = call i64 @loop()
