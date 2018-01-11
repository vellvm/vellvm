define i64 @main(i64 %argc, i8** %arcv) {
entry: 
  %cnt0 = add i64 10, 0
  br label %loop_top

loop_top:
  %cnt1 = phi i64 [%cnt0, %entry], [%cnt2, %loop_top]
  %cnt2 = sub i64 %cnt1, 1
  %b = icmp eq i64 %cnt2, 0
  br i1 %b, label %exit, label %loop_top

exit:
  ret i64 %cnt2
}  
