declare void @printf(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)

@str = global [162 x i8] c"Sum of first element of each list before sorting: %lld; sum after: %lld; elements of arr2 after sort: %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld\00"

@arr1 = global [12 x i64] [i64 10, i64 9, i64 8, i64 7, i64 6, i64 5, i64 4, i64 3, i64 2, i64 1, i64 0, i64 -1]
@arr1_length = global i64 12

@arr2 = global [12 x i64] [i64 5, i64 5, i64 10, i64 1, i64 6, i64 7, i64 -5, i64 49, i64 4512, i64 4851, i64 741, i64 84]

define void @swap(ptr %arr, i64 %i, i64 %j) {
  %1 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %i
  %2 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %j

  %i_val = load i64, ptr %1
  %j_val = load i64, ptr %2

  store i64 %j_val, ptr %1
  store i64 %i_val, ptr %2

  ret void
}

define void @heapify(ptr %arr, i64 %arr_length, i64 %i) {
  %largest = alloca i64
  store i64 %i, ptr %largest

  %1 = mul i64 %i, 2
  %left = add i64 %1, 1
  %right = add i64 %1, 2
  br label %if1_cond1

if1_cond1:
  %2 = icmp slt i64 %left, %arr_length
  br i1 %2, label %if1_cond2, label %if2_cond1

if1_cond2:
  %3 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %left
  %4 = load i64, ptr %largest
  %5 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %4
  %arr_left = load i64, ptr %3
  %arr_largest = load i64, ptr %5
  %6 = icmp sgt i64 %arr_left, %arr_largest
  br i1 %6, label %if1, label %if2_cond1

if1:
  store i64 %left, ptr %largest
  br label %if2_cond1

if2_cond1:
  %7 = icmp slt i64 %right, %arr_length
  br i1 %7, label %if2_cond2, label %if3_cond

if2_cond2:
  %8 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %right
  %9 = load i64, ptr %largest
  %10 = getelementptr [12 x i64], ptr %arr, i64 0, i64 %9
  %arr_right = load i64, ptr %8
  %arr_largest2 = load i64, ptr %10
  %11 = icmp sgt i64 %arr_right, %arr_largest2
  br i1 %11, label %if2, label %if3_cond

if2:
  store i64 %right, ptr %largest
  br label %if3_cond

if3_cond:
  %12 = load i64, ptr %largest
  %13 = icmp ne i64 %12, %i
  br i1 %13, label %if3, label %end

if3:
  %14 = load i64, ptr %largest
  call void @swap(ptr %arr, i64 %i, i64 %14)
  call void @heapify(ptr %arr, i64 %arr_length, i64 %14)
  br label %end

end:
  ret void
}

define void @heapsort(ptr %arr, ptr %arr_length_p) {
  %arr_length = load i64, ptr %arr_length_p

  %1 = lshr i64 %arr_length, 1
  %2 = sub i64 %1, 1

  %i1 = alloca i64
  store i64 %2, ptr %i1
  br label %for1_cond

for1_cond:
  %3 = load i64, ptr %i1
  %4 = icmp sge i64 %3, 0
  br i1 %4, label %for1, label %for2_setup

for1:
  %5 = load i64, ptr %i1
  call void @heapify(ptr %arr, i64 %arr_length, i64 %5)
  %6 = sub i64 %5, 1
  store i64 %6, ptr %i1
  br label %for1_cond

for2_setup:
  %7 = sub i64 %arr_length, 1
  %i2 = alloca i64
  store i64 %7, ptr %i2
  br label %for2_cond

for2_cond:
  %8 = load i64, ptr %i2
  %9 = icmp sge i64 %8, 0
  br i1 %9, label %for2, label %end

for2:
  %10 = load i64, ptr %i2
  call void @swap(ptr %arr, i64 0, i64 %10)
  call void @heapify(ptr %arr, i64 %10, i64 0)

  %11 = load i64, ptr %i2
  %12 = sub i64 %11, 1
  store i64 %12, ptr %i2
  br label %for2_cond

end:
  ret void
}

define i64 @main(i64 %argc, ptr %argv) {
  %1 = getelementptr [12 x i64], ptr @arr1, i64 0, i64 0
  %2 = load i64, ptr %1
  %3 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 0
  %4 = load i64, ptr %3
  %5 = add i64 %2, %4

  call void @heapsort(ptr @arr1, ptr @arr1_length)
  %6 = getelementptr [12 x i64], ptr @arr1, i64 0, i64 0
  %7 = load i64, ptr %6

  %arr2_length = alloca i64
  store i64 12, ptr %arr2_length
  call void @heapsort(ptr @arr2, ptr %arr2_length)
  %8 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 0
  %9 = load i64, ptr %8

  %10 = add i64 %7, %9

  %11 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 0
  %12 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 1
  %13 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 2
  %14 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 3
  %15 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 4
  %16 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 5
  %17 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 6
  %18 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 7
  %19 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 8
  %20 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 9
  %21 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 10
  %22 = getelementptr [12 x i64], ptr @arr2, i64 0, i64 11

  %23 = load i64, ptr %11
  %24 = load i64, ptr %12
  %25 = load i64, ptr %13
  %26 = load i64, ptr %14
  %27 = load i64, ptr %15
  %28 = load i64, ptr %16
  %29 = load i64, ptr %17
  %30 = load i64, ptr %18
  %31 = load i64, ptr %19
  %32 = load i64, ptr %20
  %33 = load i64, ptr %21
  %34 = load i64, ptr %22

  %35 = getelementptr [162 x i8], ptr @str, i32 0, i32 0

  ret i64 0
}

; ASSERT EQ: i64 0 = call i64 @main(i64 0, ptr null)
