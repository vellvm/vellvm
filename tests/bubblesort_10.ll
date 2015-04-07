%arr = type [10 x i64]

@tmp = global %arr [i64 69, i64 7, i64 4, i64 199, i64 14, i64 5, i64 200, i64 254, i64 1, i64 96]
@swap = global i64 0



define void @compare_at_index_i(i64 %i) {
  %1_ptr = getelementptr %arr* @tmp, i64 0, i64 %i
  %j = add i64 1, %i
  %2_ptr = getelementptr %arr* @tmp, i64 0, i64 %j
  %x1 = load i64* %1_ptr
  %x2 = load i64* %2_ptr
  %perform_swap = icmp sgt i64 %x1, %x2
  br i1 %perform_swap, label %perform, label %do_not_perform
  
  
perform:
  %swap_ptr_in_caii = getelementptr i64* @swap, i32 0
  store i64 1, i64* %swap_ptr_in_caii
  store i64 %x1, i64* %2_ptr
  store i64 %x2, i64* %1_ptr
  ret void
  
  
do_not_perform:
  ret void
}



define i64 @main(i64 %argc, i8** %argv) {
  br label %run_bubble_sort


run_bubble_sort:
  %swap_ptr = getelementptr i64* @swap, i32 0
  store i64 0, i64* %swap_ptr
  
  call void @compare_at_index_i(i64 0)
  call void @compare_at_index_i(i64 1)
  call void @compare_at_index_i(i64 2)
  call void @compare_at_index_i(i64 3)
  call void @compare_at_index_i(i64 4)
  call void @compare_at_index_i(i64 5)
  call void @compare_at_index_i(i64 6)
  call void @compare_at_index_i(i64 7)
  call void @compare_at_index_i(i64 8)
  
  %swap_res = load i64* %swap_ptr
  %result = icmp ne i64 %swap_res, 0
  br i1 %result, label %run_bubble_sort, label %exit
  
  
exit:
  %1temp = getelementptr %arr* @tmp, i32 0, i32 0
  %1ans = load i64* %1temp
  %1fin = icmp eq i64 %1ans, 1
  
  %2temp = getelementptr %arr* @tmp, i32 0, i32 1
  %2ans = load i64* %2temp
  %2fin = icmp eq i64 %2ans, 4
  
  %3temp = getelementptr %arr* @tmp, i32 0, i32 2
  %3ans = load i64* %3temp
  %3fin = icmp eq i64 %3ans, 5
  
  %4temp = getelementptr %arr* @tmp, i32 0, i32 3
  %4ans = load i64* %4temp
  %4fin = icmp eq i64 %4ans, 7
  
  %5temp = getelementptr %arr* @tmp, i32 0, i32 4
  %5ans = load i64* %5temp
  %5fin = icmp eq i64 %5ans, 14
  
  %6temp = getelementptr %arr* @tmp, i32 0, i32 5
  %6ans = load i64* %6temp
  %6fin = icmp eq i64 %6ans, 69
  
  %7temp = getelementptr %arr* @tmp, i32 0, i32 6
  %7ans = load i64* %7temp
  %7fin = icmp eq i64 %7ans, 96 
  
  %8temp = getelementptr %arr* @tmp, i32 0, i32 7
  %8ans = load i64* %8temp
  %8fin = icmp eq i64 %8ans, 199
  
  %9temp = getelementptr %arr* @tmp, i32 0, i32 8
  %9ans = load i64* %9temp
  %9fin = icmp eq i64 %9ans, 200
  
  %10temp = getelementptr %arr* @tmp, i32 0, i32 9
  %10ans = load i64* %10temp
  %10fin = icmp eq i64 %10ans, 254
  
  %11 = and i64 %1fin, %2fin
  %12 = and i64 %11, %3fin
  %13 = and i64 %12, %4fin
  %14 = and i64 %13, %5fin
  %15 = and i64 %14, %6fin
  %16 = and i64 %15, %7fin
  %17 = and i64 %16, %8fin
  %18 = and i64 %17, %9fin
  %19 = and i64 %18, %10fin
  
  ret i64 %19
}

