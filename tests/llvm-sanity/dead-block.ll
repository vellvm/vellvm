define i64 @main(i64 %argc, i8** %arcv) {
entry:
  %w = icmp eq i64 2, %argc
  %u = add i64 30, 40
  br label %foo

foo:
  %x = phi i64 [100, %entry], [%x, %dead]
  ret i64 %x

dead:
  %y = add i64 10, 20
  br label %foo

}
