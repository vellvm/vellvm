define i64 @foo(i64 %x) {
  %1 = add i64 %x, %x
  ret i64 %1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 17)
  ret i64 %1
}
