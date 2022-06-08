%arr = type [10 x i64]

@input = global %arr [i64 10, i64 5, i64 134, i64 9, i64 11, i64 7, i64 200, i64 65, i64 74, i64 2]
@length = global i64 10

define void @insertionSort() {
  %i = alloca i64
  %j = alloca i64
  %len = load i64, i64* @length
  store i64 1, i64* %i
  br label %while_cond_1
while_cond_1:
  ; while i < length(A)
  %1 = load i64, i64* %i ; i
  %2 = icmp slt i64 %1, %len
  br i1 %2, label %while_body_1, label %while_end_1
while_body_1:
  ; j = i
  %3 = load i64, i64* %i
  store i64 %3, i64* %j
  br label %while_cond_2
while_cond_2:
  ; while j > 0 and A[j-1] > A[j]
  %4 = load i64, i64* %j ; j
  %5 = icmp sgt i64 %4, 0 ; j>0
  %6 = sub i64 %4, 1 ; j-1
  %a_j0_ptr = getelementptr [10 x i64], [10 x i64]* @input, i32 0, i64 %6
  %a_j0 = load i64, i64* %a_j0_ptr; A[j-1]
  %a_j1_ptr = getelementptr [10 x i64], [10 x i64]* @input, i32 0, i64 %4
  %a_j1 = load i64, i64* %a_j1_ptr; A[j]
  %7 = icmp sgt i64 %a_j0, %a_j1
  ; (j > 0) and (A[j-1] > A[j])
  %8 = and i1 %5, %7
  br i1 %8, label %while_body_2, label %while_end_2
while_body_2:
  %9 = load i64, i64* %j ; j
  %10 = sub i64 %9, 1 ; j-1
  %tmp_ptr0 = getelementptr [10 x i64], [10 x i64]* @input, i32 0, i64 %9
  %tmp0 = load i64, i64* %tmp_ptr0 ; A[j]
  %tmp_ptr1 = getelementptr [10 x i64], [10 x i64]* @input, i32 0, i64 %10
  %tmp1 = load i64, i64* %tmp_ptr1 ; A[j-1]
  store i64 %tmp0, i64* %tmp_ptr1
  store i64 %tmp1, i64* %tmp_ptr0 
  %11 = sub i64 %9, 1 
  store i64 %11, i64* %j 
  br label %while_cond_2 
while_end_2:
  ; i = i + 1
  %12 = load i64, i64* %i
  %13 = add i64 %12, 1
  store i64 %13, i64* %i
  br label %while_cond_1
while_end_1:
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  call void @insertionSort() 
  %1 = getelementptr [10 x i64], [10 x i64]* @input, i32 0, i32 5
  %2 = load i64, i64* %1
  ret i64 %2
}