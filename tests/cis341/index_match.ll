@glist = global [7 x i64] [ i64 -1, i64 1, i64 4, i64 5, i64 6, i64 10, i64 11 ]

define i64 @indexmatch(i64 %lo, i64 %hi, [7 x i64]* %list) {
  %cmp1 = icmp eq i64 %lo, %hi
  br i1 %cmp1, label %base_case, label %check
base_case:
  %a_lo_addr = getelementptr [7 x i64], [7 x i64]* %list, i32 0, i64 %lo
  %a_lo = load i64, i64* %a_lo_addr
  %cmp2 = icmp eq i64 %lo, %a_lo
  br i1 %cmp2, label %true, label %false
true:
  ret i64 1
false:
  ret i64 0
check:
  %m2 = add i64 %lo, %hi
  %m = ashr i64 %m2, 1
  %a_m_addr = getelementptr [7 x i64], [7 x i64]* %list, i32 0, i64 %m
  %a_m = load i64, i64* %a_m_addr
  %cmp3 = icmp eq i64 %m, %a_m
  br i1 %cmp3, label %true, label %recurse
recurse:
  %cmp4 = icmp slt i64 %m, %a_m
  br i1 %cmp4, label %recurse_left, label %recurse_right
recurse_left:
  %new_hi = sub i64 %m, 1
  %left_ans = call i64 @indexmatch(i64 %lo, i64 %new_hi, [7 x i64]* %list)
  ret i64 %left_ans
recurse_right:
  %new_lo = add i64 %m, 1
  %right_ans = call i64 @indexmatch(i64 %new_lo, i64 %hi, [7 x i64]* %list)
  ret i64 %right_ans
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ans = call i64 @indexmatch(i64 0, i64 6, [7 x i64]* @glist)
  ret i64 %ans
}