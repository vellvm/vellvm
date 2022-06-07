@gbl_values = global [9 x i64] [ i64 12, i64 1, i64 33, i64 4, i64 1, i64 2, i64 1, i64 59, i64 4 ]
@gbl_weights = global [9 x i64] [ i64 2, i64 10, i64 34, i64 9, i64 20, i64 26, i64 14, i64 5, i64 4 ]

define i64 @max(i64 %item1, i64 %item2) {
    %one_bigger = icmp sge i64 %item1, %item2
    br i1 %one_bigger, label %ret_item_one, label %ret_item_two

ret_item_one:
    ret i64 %item1

ret_item_two:
    ret i64 %item2

}

define i64 @knapsack([9 x i64]* %value_arr, [9 x i64]* %weight_arr, i64 %current_item_index, i64 %remaining_weight) {
  %full = icmp eq i64 0, %remaining_weight
  %no_items = icmp slt i64 %current_item_index, 0 
  %full_or_no_items = or i1 %full, %no_items

  br i1 %full_or_no_items, label %no_more_space, label %check_weight_neg


check_weight_neg:
  %done = icmp slt i64 %remaining_weight, 0
  br i1 %done, label %no_more_weight, label %continue

no_more_space:
    ret i64 0

no_more_weight:
    ret i64 -99999999

continue:
    %new_index = add i64 -1, %current_item_index

    %value_array_i_ptr = getelementptr [9 x i64], [9 x i64]* %value_arr, i32 0, i64 %current_item_index
    %value_array_i_value = load i64, i64* %value_array_i_ptr

    %weight_array_i_ptr = getelementptr [9 x i64], [9 x i64]* %weight_arr, i32 0, i64 %current_item_index
    %weight_array_i_value = load i64, i64* %weight_array_i_ptr

    %sub_ready_weight_value = mul i64 -1, %weight_array_i_value
    %inlcude_weight_limit = add i64 %sub_ready_weight_value, %remaining_weight

    %include_item_rec_subsolution = call i64 @knapsack([9 x i64]* %value_arr, [9 x i64]* %weight_arr, i64 %new_index, i64 %inlcude_weight_limit)
    %include_item_solution = add i64 %value_array_i_value, %include_item_rec_subsolution

    %exclude_item_solution = call i64 @knapsack([9 x i64]* %value_arr, [9 x i64]* %weight_arr, i64 %new_index, i64 %remaining_weight)

    %best_option = call i64 @max(i64 %include_item_solution, i64 %exclude_item_solution)
    ret i64 %best_option

}

define i64 @main(i64 %argc, i8** %arcv) {
   %out = call i64 @knapsack([9 x i64]* @gbl_values, [9 x i64]* @gbl_weights, i64 8, i64 30)
  ret i64 %out
}