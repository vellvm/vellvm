define i64 @main(i64 %argc, i8** %arcv) {
  %b = icmp sgt i64 5, 10
  br i1 %b, label %then, label %else

then:
  br label %merge

else:
  br label %merge

merge:
  %x = phi i64 [add (i64 3, i64 4), %then], [1, %else]
  %z = phi i64 [3, %then], [2, %else]
  %ans = add i64 %x, %z
  ret i64 %ans
}  
