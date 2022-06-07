%vec1 = type [5 x i64]
%vec2 = type [7 x i64]
%vecresult = type [12 x i64]

@g_vec1_n = global i64 5
@g_vec2_n = global i64 7
@g_vec1 = global %vec1 [i64 0, i64 2, i64 3, i64 3, i64 10]
@g_vec2 = global %vec2 [i64 2, i64 3, i64 8, i64 9, i64 9, i64 10, i64 15]
@g_vecresult = global %vecresult [i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0]

define void @merge(%vec1* %vec_1, %vec2* %vec_2, %vecresult* %vec_result, i64 %i, i64 %j, i64 %k) {

    %vec1_n = load i64, i64* @g_vec1_n
    %vec2_n = load i64, i64* @g_vec2_n

    %vec1_remaining = icmp slt i64 %i, %vec1_n
    %vec2_remaining = icmp slt i64 %j, %vec2_n

    %vec1_and_vec2_remaining = and i1 %vec1_remaining, %vec2_remaining
    %vec1_or_vec2_remaining = or i1 %vec1_remaining, %vec2_remaining

    br i1 %vec1_or_vec2_remaining, label %non_base_case, label %base_case
base_case:
    ret void
non_base_case:
    %vec_result_elem_addr = getelementptr %vecresult, %vecresult* %vec_result, i32 0, i64 %k
    br i1 %vec1_and_vec2_remaining, label %both_remaining, label %one_remaining
both_remaining:
    %vec1_elem_addr = getelementptr %vec1, %vec1* %vec_1, i32 0, i64 %i
    %vec2_elem_addr = getelementptr %vec2, %vec2* %vec_2, i32 0, i64 %j
    %vec1_elem = load i64, i64* %vec1_elem_addr
    %vec2_elem = load i64, i64* %vec2_elem_addr
    %vec1_lt_vec2 = icmp slt i64 %vec1_elem, %vec2_elem
    br i1 %vec1_lt_vec2, label %push_vec1, label %push_vec2
one_remaining:
    br i1 %vec1_remaining, label %get_vec1_elem, label %get_vec2_elem
get_vec1_elem:
    %vec1_elem_addr = getelementptr %vec1, %vec1* %vec_1, i32 0, i64 %i
    %vec1_elem = load i64, i64* %vec1_elem_addr
    br label %push_vec1
get_vec2_elem:
    %vec2_elem_addr = getelementptr %vec2, %vec2* %vec_2, i32 0, i64 %j
    %vec2_elem = load i64, i64* %vec2_elem_addr
    br label %push_vec2
push_vec1:
    store i64 %vec1_elem, i64* %vec_result_elem_addr
    %i_new = add i64 %i, 1
    %j_new = add i64 %j, 0
    br label %recurse
push_vec2:
    store i64 %vec2_elem, i64* %vec_result_elem_addr
    %i_new = add i64 %i, 0
    %j_new = add i64 %j, 1
    br label %recurse
recurse:
    %k_new = add i64 %k, 1
    call void @merge(%vec1* @g_vec1, %vec2* @g_vec2, %vecresult* @g_vecresult, i64 %i_new, i64 %j_new, i64 %k_new)
    ret void
}

define i1 @isSorted(%vecresult* %vec_result) {
    %vec1_n = load i64, i64* @g_vec1_n
    %vec2_n = load i64, i64* @g_vec2_n
    %vec_result_n = add i64 %vec1_n, %vec2_n

    %i_addr = alloca i64
    store i64 0, i64* %i_addr
    br label %begin_is_sorted

begin_is_sorted:
    %i_val = load i64, i64* %i_addr
    %i_incr_val = add i64 %i_val, 1

    %done = icmp sge i64 %i_incr_val, %vec_result_n
    br i1 %done, label %exit_true, label %examine_next

examine_next:
    %elem_i_addr = getelementptr %vecresult, %vecresult* %vec_result, i32 0, i64 %i_val
    %elem_i_incr_addr = getelementptr %vecresult, %vecresult* %vec_result, i32 0, i64 %i_incr_val
    %elem_i = load i64, i64* %elem_i_addr
    %elem_i_incr = load i64, i64* %elem_i_incr_addr

    store i64 %i_incr_val, i64* %i_addr

    %in_order = icmp sle i64 %elem_i, %elem_i_incr
    br i1 %in_order, label %begin_is_sorted, label %exit_false

exit_false:
    ret i1 0
exit_true:
    ret i1 1
}


define i64 @main(i64 %argc, i8** %arcv) {
    call void @merge(%vec1* @g_vec1, %vec2* @g_vec2, %vecresult* @g_vecresult, i64 0, i64 0, i64 0)
    %is_sorted = call i1 @isSorted(%vecresult* @g_vecresult)
    ret i1 %is_sorted
}