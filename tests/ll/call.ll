define i64 @foo() {
  ret i64 42
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo()
  ret i64 %1
}

; ASSERT EQ: i64 42 = call i64 @main(i64 0, i8** null)
