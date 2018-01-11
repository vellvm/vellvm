define i64 @main(i64 %argc, i8** %arcv) {
  %b = icmp sgt i64 5, 10
  %w = add i64 0, 17
  br i1 %b, label %then, label %else

then:
  %w1 = add i64 %w, 145
  br label %merge

else:
  %w2 = add i64 %w, 23
  br label %merge

merge:
  %x = phi i64 [%w1, %then], [%w2, %else]
  %u = add i64 %w, %x
  ret i64 %x
}  
