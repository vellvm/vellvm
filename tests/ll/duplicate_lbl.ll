define i64 @f1(i64 %a) {
  br label %start
start:
  %b = icmp sgt i64 %a, 10
  br i1 %b, label %then, label %end
then:
  ret i64 1
end:
  ret i64 0
}

define i64 @f2(i64 %a) {
  br label %start
start:
  %b = icmp sgt i64 %a, 10
  br i1 %b, label %then, label %end
then:
  ret i64 1
end:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %a = call i64 @f1(i64 0)
  %b = call i64 @f2(i64 15)
  %c = add i64 %a, %b
  ret i64 %c
}
