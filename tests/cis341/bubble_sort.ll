@glist = global [6 x i64] [ i64 5, i64 2, i64 4, i64 1, i64 3, i64 0 ]

define void @sort([6 x i64]* %list) {
  %i = alloca i64
  store i64 0, i64* %i
  %j = alloca i64
  br label %loop_cnd_i
loop_cnd_i:
  store i64 0, i64* %j
  %ival = load i64, i64* %i
  %cmp1 = icmp eq i64 %ival, 6
  br i1 %cmp1, label %exit_i, label %loop_body_i
loop_body_i:
  %jval = load i64, i64* %j
  %bound = sub i64 6, %ival
  %cmp2 = icmp eq i64 %jval, %bound
  br i1 %cmp2, label %exit_j, label %loop_body_j
loop_body_j:
  %left_indx = load i64, i64* %j
  %right_indx = add i64 %left_indx, 1
  %left = getelementptr [6 x i64], [6 x i64]* %list, i64 0, i64 %left_indx
  %right = getelementptr [6 x i64], [6 x i64]* %list, i64 0, i64 %right_indx
  %left_el = load i64, i64* %left
  %right_el = load i64, i64* %right
  %cmp3 = icmp sgt i64 %left_el, %right_el
  br i1 %cmp3, label %swap, label %no_swap
swap:
  store i64 %right_el, i64* %left
  store i64 %left_el, i64* %right
  br label %no_swap
no_swap:
  %j_next = add i64 %jval, 1
  store i64 %j_next, i64* %j
  br label %loop_body_i
exit_j:
  %i_next = add i64 %ival, 1
  store i64 %i_next, i64* %i
  br label %loop_cnd_i
exit_i:
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  call void @sort([6 x i64]* @glist)
  %r = getelementptr [6 x i64], [6 x i64]* @glist, i64 0, i64 0
  %1 = load i64, i64* %r
  ret i64 %1
}