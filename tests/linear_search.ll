@glist = global [5 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5]

define i64 @search(i64 %x, [5 x i64]* %list) {
  %i = alloca i64
  store i64 0, i64* %i
  br label %loop

loop:
  %count = load i64, i64* %i
  %cmp1 = icmp eq i64 %count, 5
  br i1 %cmp1, label %false, label %check

check:
  %ptr = getelementptr [5 x i64], [5 x i64]* %list, i64 0, i64 %count 
  %val = load i64, i64* %ptr
  %cmp2 = icmp eq i64 %x, %val
  %a = add i64 1, %count
  store i64 %a, i64* %i
  br i1 %cmp2, label %true, label %loop

true:
  ret i64 1

false:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %r = call i64 @search(i64 3, [5 x i64]* @glist)
  ret i64 %r
}
