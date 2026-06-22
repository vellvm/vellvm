define i64 @foo(i64 %x) {
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 17)
  ret i64 %1
}

; ASSERT EQ: i64 17 = call i64 @main(i64 0, i8** null)
