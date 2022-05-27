@blah = global [5 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5]

define i64 @main() #0 {
  %sum_ptr = alloca i64, align 4
  %i = alloca i64, align 8

  ; Load and store array...
  %array = load [5 x i64], [5 x i64]* @blah
  store [5 x i64] %array, [5 x i64]* @blah

  store i64 0, i64* %sum_ptr, align 4
  store i64 0, i64* %i, align 8
  br label %sum_loop_cond

sum_loop_cond:
  %xv = load i64, i64* %i, align 8
  %cmp = icmp ult i64 %xv, 5
  br i1 %cmp, label %sum_loop_body, label %exit

sum_loop_body:
  %iv = load i64, i64* %i, align 8
  %elem_ptr = getelementptr inbounds [5 x i64], [5 x i64]* @blah, i64 0, i64 %iv
  %elem = load i64, i64* %elem_ptr, align 4
  %sum = load i64, i64* %sum_ptr, align 4
  %new_sum = add nsw i64 %sum, %elem
  store i64 %new_sum, i64* %sum_ptr, align 4

  %next_i = add i64 %iv, 1
  store i64 %next_i, i64* %i, align 8
  br label %sum_loop_cond

exit:
  %rv = load i64, i64* %sum_ptr, align 4
  ret i64 %rv
}

; ASSERT EQ: i64 15 = call i64 @main()
