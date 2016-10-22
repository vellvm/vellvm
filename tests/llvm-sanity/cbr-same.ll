define i64 @main(i64 %argc, i8** %arcv) {
  %1 = icmp ult i64 %argc, 2
  br i1 %1, label %left, label %right

left:
  br label %merge

right:
  %2 = icmp eq i64 2, %argc
  br i1 %1, label %merge, label %merge

merge:
  %z = phi i64 [ 50, %left], [ 200, %right ]
  ret i64 %z
}

