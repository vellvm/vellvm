
define label @foo(label %lbl) {
  return %lbl
}



define i64 @main(i64 %argc, i8** %arcv) {
  %tst = icmp eq i64 %argc, 0
  br i1 %tst, label %then, label %else

then:
  %v = call label @foo(label %else)
  br label %v

else:
  ret i64 %z
}
