define void @foo(i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f, i64 %g) {
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 9999999, i64* %1
  br label %loop_condition
loop_condition:
  %2 = load i64, i64* %1
  %3 = icmp sgt i64 %2, 0
  br i1 %3, label %loop_body, label %post_loop
loop_body:
  call void @foo(i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0)
  %5 = sub i64 %2, 1
  store i64 %5, i64* %1
  br label %loop_condition
post_loop:
  ret i64 0
}
