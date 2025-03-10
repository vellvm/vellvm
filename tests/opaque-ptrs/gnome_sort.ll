@glist = global [10 x i64] [i64 20, i64 17, i64 13, i64 14, i64 6, i64 5, i64 4, i64 3, i64 2, i64 1]

define void @sort (ptr %list) {
  %i = alloca i64
  store i64 1, ptr %i
  br label %loop
loop:
  %count = load i64, ptr %i
  %cmp1 = icmp slt i64 %count, 9
  br i1 %cmp1, label %body, label %done
body:
  %p1 = getelementptr [10 x i64], ptr %list, i32 0, i64 %count
  %v1 = load i64, ptr %p1
  %cb = add i64 %count, 1
  %p2 = getelementptr [10 x i64], ptr %list, i32 0, i64 %cb
  %v2 = load i64, ptr %p2
  %cmp2 = icmp slt i64 %v1, %v2
  br i1 %cmp2, label %bumpc, label %swap
bumpc:
  %a = add i64 1, %count
  store i64 %a, ptr %i
  br label %loop
swap:
  store i64 %v1, ptr %p2
  store i64 %v2, ptr %p1
  %cmp3 = icmp sgt i64 %count, 0
  br i1 %cmp3, label %decc, label %loop
decc:
  store i64 %v1, ptr %p2
  store i64 %v2, ptr %p1
  %b = sub i64 %count, 1
  store i64 %b, ptr %i
  br label %loop
done:
  %max_ptr = getelementptr [10 x i64], ptr %list, i32 0, i64 9
  %max = load i64, ptr %max_ptr
  ret void
}

define i64 @main(i64 %argc, ptr %arcv) {
  %index1 = getelementptr [10 x i64], ptr @glist, i32 0, i64 0
  %index2 = getelementptr [10 x i64], ptr @glist, i32 0, i64 1
  %index3 = getelementptr [10 x i64], ptr @glist, i32 0, i64 2
  %index4 = getelementptr [10 x i64], ptr @glist, i32 0, i64 3
  %index5 = getelementptr [10 x i64], ptr @glist, i32 0, i64 4
  %index6 = getelementptr [10 x i64], ptr @glist, i32 0, i64 5
  %index7 = getelementptr [10 x i64], ptr @glist, i32 0, i64 6
  %index8 = getelementptr [10 x i64], ptr @glist, i32 0, i64 7
  %index9 = getelementptr [10 x i64], ptr @glist, i32 0, i64 8
  %index10 = getelementptr [10 x i64], ptr @glist, i32 0, i64 9

  call void @sort(ptr @glist)

  %i1 = load i64, ptr %index1
  %i2 = load i64, ptr %index2
  %i3 = load i64, ptr %index3
  %i4 = load i64, ptr %index4
  %i5 = load i64, ptr %index5
  %i6 = load i64, ptr %index6
  %i7 = load i64, ptr %index7
  %i8 = load i64, ptr %index8
  %i9 = load i64, ptr %index9
  %i10 = load i64, ptr %index10

  %first_two = add i64 %i1, %i2
  %last_one = add i64 %first_two, %i10
  %minus_second_last = sub i64 %last_one, %i9

  ret i64 %minus_second_last
}

; ASSERT EQ: i64 6 = call i64 @main(i64 0, ptr null)
