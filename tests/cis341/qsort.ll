@array1 = global [10 x i64] [i64 4, i64 9, i64 9, i64 9, i64 -1, i64 3, i64 3, i64 5, i64 8, i64 1]


define i64 @is_sorted([0 x i64]* %arr, i64 %index, i64 %prev, i64 %n) {

    %1 = icmp slt i64 %index, %n
    br i1 %1, label %check, label %exit_t
check:
    %addr = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %index
    %value = load i64, i64*%addr
    %2 = icmp sge i64 %value, %prev
    br i1 %2, label %recurse, label %exit_f
recurse: 
    %next = add i64 1, %index
    %rec = call i64 @is_sorted([0 x i64]* %arr, i64 %next, i64 %value, i64 %n)
    ret i64 %rec
exit_t:
    ret i64 1
exit_f:
    ret i64 0
}

define i64 @partition([0 x i64]* %arr, i64 %left, i64 %right) {

    %l_mut = alloca i64
    %r_mut = alloca i64
    store i64 %left, i64* %l_mut
    store i64 %right, i64* %r_mut

    %sum = add i64 %left, %right
    %pivot_i = ashr i64 %sum, 1
    %pivot_addr =  getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %pivot_i
    %pivot = load i64, i64* %pivot_addr

    br label %body
body:
    br label %check_l
incr_l:
    %l_i = load i64, i64* %l_mut
    %next = add i64 %l_i, 1
    store i64 %next, i64* %l_mut
    br label %check_l
check_l:
    %l_index = load i64, i64* %l_mut
    %l_arr_ptr = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %l_index
    %l_val = load i64, i64* %l_arr_ptr
    %l_cmp = icmp slt i64 %l_val, %pivot
    br i1 %l_cmp, label %incr_l, label %check_r
incr_r:
    %r_i = load i64, i64* %r_mut
    %next_r = add i64 %r_i, -1
    store i64 %next_r, i64* %r_mut
    br label %check_r
check_r:
    %r_index = load i64, i64* %r_mut
    %r_arr_ptr = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %r_index
    %r_val = load i64, i64* %r_arr_ptr
    %r_cmp = icmp sgt i64 %r_val, %pivot
    br i1 %r_cmp, label %incr_r, label %check_body
check_body:
    %index_l = load i64, i64* %l_mut
    %index_r = load i64, i64* %r_mut
    %cmp_l_r = icmp sge i64 %index_l, %index_r
    br i1 %cmp_l_r, label %exit, label %swap
exit:
    %r_index1 = load i64, i64* %r_mut
    ret i64 %r_index1

swap:
    %l_arr_ptr1 = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %index_l
    %r_arr_ptr1 = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %index_r
    %l_val1 = load i64, i64* %l_arr_ptr1
    %r_val1 = load i64, i64* %r_arr_ptr1

    store i64 %r_val1, i64* %l_arr_ptr1
    store i64 %l_val1, i64* %r_arr_ptr1

    %l_i1 = load i64, i64* %l_mut
    %next1 = add i64 %l_i1, 1
    store i64 %next1, i64* %l_mut
    
    %r_i1 = load i64, i64* %r_mut
    %next_r1 = add i64 %r_i1, -1
    store i64 %next_r1, i64* %r_mut

    br label %body
}

define void @quicksort([0 x i64]* %arr, i64 %left, i64 %right) {
    %1 = icmp sge i64 %left, 0
    %2 = icmp sge i64 %right, 0
    %3 = icmp slt i64 %left, %right
    %4 = and i1 %1, %2
    %5 = and i1 %3, %4
    br i1 %5, label %body, label %exit
body:

    %p = call i64 @partition([0 x i64]* %arr, i64 %left, i64 %right)
    call void @quicksort([0 x i64]* %arr, i64 %left, i64 %p)
    %6 = add i64 %p, 1
    call void @quicksort([0 x i64]* %arr, i64 %6, i64 %right)
    ret void
exit:
    ret void
}

define i64 @main() {
    %a = bitcast [10 x i64]* @array1 to [0 x i64]*
    call void @quicksort([0 x i64]* %a, i64 0, i64 9)
    
    %1 = call i64 @is_sorted([0 x i64]* %a, i64 0, i64 -5, i64 10)
    ret i64 %1
}