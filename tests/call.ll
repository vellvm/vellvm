define i64 @foo() {
  ret i64 42
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo()
  ret i64 %1
}
