define i64 @foo() {
  ret i64 42
}

define i64 @bar() {
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  %y = alloca i64
  store i64 0, i64* %1
  store i64 100, i64* %y
  %2 = load i64, i64* %y
  %3 = icmp ne i64 %2, 0
  br i1 %3, label %then, label %else

then:
  %4 = call i64 @foo()
  store i64 %4, i64* %1
  br label %end

else:
  %5 = call i64 @bar()
  store i64 %5, i64* %1
  br label %end

end:
  %6 = load i64, i64* %1
  ret i64 %6
}
