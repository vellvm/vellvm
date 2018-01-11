define i64 @main(i64 %argc, i8** %arcv) {
  %b = icmp sgt i64 5, 10
  br i1 %b, label %then, label %else

then:
  br label %merge

else:
  br label %merge

merge:
  %x = phi i64 [0, %then], [1, %else]
  ret i64 %x
}  
