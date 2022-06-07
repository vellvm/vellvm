@glist = global [10 x i64] [i64 20, i64 17, i64 13, i64 14, i64 6, i64 5, i64 4, i64 3, i64 2, i64 1]

define void @sort ([10 x i64]* %list) {
  %i = alloca i64
  store i64 1, i64* %i
  br label %loop
loop:
  %count = load i64, i64* %i
  %cmp1 = icmp slt i64 %count, 9
  br i1 %cmp1, label %body, label %done
body:
  %p1 = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %count
  %v1 = load i64, i64* %p1
  %cb = add i64 %count, 1
  %p2 = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %cb
  %v2 = load i64, i64* %p2
  %cmp2 = icmp slt i64 %v1, %v2
  br i1 %cmp2, label %bumpc, label %swap
bumpc:
  %a = add i64 1, %count
  store i64 %a, i64* %i
  br label %loop
swap:
  store i64 %v1, i64* %p2
  store i64 %v2, i64* %p1
  %cmp2 = icmp sgt i64 %count, 0
  br i1 %cmp2, label %decc, label %loop
decc:
  store i64 %v1, i64* %p2
  store i64 %v2, i64* %p1
  %a = sub i64 %count, 1
  store i64 %a, i64* %i
  br label %loop
done:
  %max_ptr = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 9
  %max = load i64, i64* %max_ptr
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  %index1 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 0
  %index2 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 1
  %index3 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 2
  %index4 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 3
  %index5 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 4
  %index6 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 5
  %index7 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 6
  %index8 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 7
  %index9 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 8
  %index10 = getelementptr [10 x i64], [10 x i64]* @glist, i32 0, i64 9

  %r = call void @sort([10 x i64]* @glist)

  %i1 = load i64, i64* %index1
  %i2 = load i64, i64* %index2
  %i3 = load i64, i64* %index3
  %i4 = load i64, i64* %index4
  %i5 = load i64, i64* %index5
  %i6 = load i64, i64* %index6
  %i7 = load i64, i64* %index7
  %i8 = load i64, i64* %index8
  %i9 = load i64, i64* %index9
  %i10 = load i64, i64* %index10

  %first_two = add i64 %i1, %i2
  %last_one = add i64 %first_two, %i10
  %minus_second_last = sub i64 %last_one, %i9

  ret i64 %minus_second_last
}
