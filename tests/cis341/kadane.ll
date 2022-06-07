@gbl = global [9 x i64] [ i64 -2, i64 1, i64 -3, i64 4, i64 -1, i64 2, i64 1, i64 -5, i64 4 ]
define i64 @kadane([0 x i64]* %arr, i64 %max_so_far, i64 %max_here, i64 %size, i64 %i) {
  %done = icmp slt i64 %i, %size
  br i1 %done, label %start_iter, label %exit
start_iter:
    %addr = getelementptr [0 x i64], [0 x i64]* %arr, i64 0, i64 %i
    %new_i = add i64 1, %i
    %v = load i64, i64* %addr
    %curr = add i64 %max_here, %v
    br label %check_positive
check_positive:
    %is_pos = icmp sge i64 %curr, 0
    br i1 %is_pos, label %pos, label %not_pos
pos:
    %is_max = icmp sge i64 %curr, %max_so_far
    br i1 %is_max, label %max, label %no_max
max:
    %rec_max = call i64 @kadane([0 x i64]* %arr, i64 %curr, i64 %curr, i64 %size, i64 %new_i)
    ret i64 %rec_max
no_max:
    %rec_no_max = call i64 @kadane([0 x i64]* %arr, i64 %max_so_far, i64 %curr, i64 %size, i64 %new_i)
    ret i64 %rec_no_max
not_pos:
    %rec_no_pos = call i64 @kadane([0 x i64]* %arr, i64 %max_so_far, i64 0, i64 %size, i64 %new_i)
    ret i64 %rec_no_pos
exit:
    ret i64 %max_so_far
}
define i64 @main(i64 %argc, i8** %arcv) {
  %out = call i64 @kadane([0 x i64]* @gbl, i64 0, i64 0, i64 9, i64 0)
  ret i64 %out
}