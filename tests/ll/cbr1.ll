define i64 @main(i64 %argc, i8** %arcv) {
  %cmp = icmp sgt i64 3, 0
  br i1 %cmp, label %then, label %else

then:
  ret i64 7

else:
  ret i64 9
}

; ASSERT EQ: i64 7 = call i64 @main(i64 0, i8** null)
