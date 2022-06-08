declare void @printf(i8*, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)

@output_str = global [170 x i8] c"Initial array: %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld; Sorted array: %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld\00"


%arr = type [14 x i64]
@input = global %arr [i64 4, i64 1, i64 50, i64 50, i64 7, i64 0, i64 5, i64 10, i64 9, i64 11, i64 0, i64 100, i64 3, i64 8]

; linear time and in place partition, given the lo and hi boundaries (chooses last element as in CLRS)
define i64 @partition(%arr* %nums, i64 %lo, i64 %hi) {

	; get pivot element
	%pivot_ptr = getelementptr %arr, %arr* %nums, i32 0, i64 %hi
	%pivot = load i64, i64* %pivot_ptr

	; j is index through array 
	%j_ptr = alloca i64
	store i64 %lo, i64* %j_ptr

	; i is border of smaller elemenets
	%i_ptr = alloca i64
	store i64 %lo, i64* %i_ptr

	br label %loop_condition

	loop_condition:

		; while j <= hi
		%j = load i64, i64* %j_ptr
		%1 = icmp sle i64 %j, %hi
		br i1 %1, label %loop_body, label %loop_exit

		loop_body:

			;if A[j] < pivot
			%p = load i64, i64* %j_ptr
			%a_j_ptr = getelementptr %arr, %arr* %nums, i32 0, i64 %p
			%a_j = load i64, i64* %a_j_ptr
			%2 = icmp slt i64 %a_j, %pivot
			br i1 %2, label %if_body, label %if_end

			if_body:

				%i = load i64, i64* %i_ptr

				;swap A[i] and A[j]
				call void @swap(%arr* %nums, i64 %i, i64 %p)

				;i++
				%3 = add i64 %i, 1
				store i64 %3, i64* %i_ptr

				br label %if_end

			if_end:

				;incremennt j and go back to loop
				%4 = add i64 %j, 1
				store i64 %4, i64* %j_ptr
				br label %loop_condition

		loop_exit: 

			;swap A[i] and A[hi]
			%q = load i64, i64* %i_ptr
			call void @swap(%arr* %nums, i64 %q, i64 %hi)

			ret i64 %q




}

;swap nums[fst] and nums[snd]
define void @swap(%arr* %nums, i64 %fst, i64 %snd) {

	%fst_element_ptr = getelementptr %arr, %arr* %nums, i32 0, i64 %fst
	%snd_element_ptr = getelementptr %arr, %arr* %nums, i32 0, i64 %snd

	%fst_element = load i64, i64* %fst_element_ptr
	%snd_element = load i64, i64* %snd_element_ptr

	store i64 %fst_element, i64* %snd_element_ptr
	store i64 %snd_element, i64* %fst_element_ptr 

	ret void

}

;quicksort
define void @quicksort(%arr* %nums, i64 %lo, i64 %hi) {
	;if lo < hi
	%1 = icmp slt i64 %lo, %hi
	br i1 %1, label %sort_case, label %trivial

	sort_case:

		%p = call i64 @partition(%arr* %nums, i64 %lo, i64 %hi)
		%2 = sub i64 %p, 1
		%3 = add i64 %p, 1

		call void @quicksort(%arr* %nums, i64 %lo, i64 %2)
		call void @quicksort(%arr* %nums, i64 %3, i64 %hi)

		ret void

	trivial:

		ret void
}


define i64 @main(i64 %argc, i8** %arcv) {

	;pointers for array elements
	%in0 = getelementptr %arr, %arr* @input, i32 0, i32 0
	%in1 = getelementptr %arr, %arr* @input, i32 0, i32 1
	%in2 = getelementptr %arr, %arr* @input, i32 0, i32 2
	%in3 = getelementptr %arr, %arr* @input, i32 0, i32 3
	%in4 = getelementptr %arr, %arr* @input, i32 0, i32 4
	%in5 = getelementptr %arr, %arr* @input, i32 0, i32 5
	%in6 = getelementptr %arr, %arr* @input, i32 0, i32 6
	%in7 = getelementptr %arr, %arr* @input, i32 0, i32 7
	%in8 = getelementptr %arr, %arr* @input, i32 0, i32 8
	%in9 = getelementptr %arr, %arr* @input, i32 0, i32 9
	%in10 = getelementptr %arr, %arr* @input, i32 0, i32 10
	%in11 = getelementptr %arr, %arr* @input, i32 0, i32 11
	%in12 = getelementptr %arr, %arr* @input, i32 0, i32 12
	%in13 = getelementptr %arr, %arr* @input, i32 0, i32 13

	;initial elements
	%a0 = load i64, i64* %in0
	%a1 = load i64, i64* %in1
	%a2 = load i64, i64* %in2
	%a3 = load i64, i64* %in3
	%a4 = load i64, i64* %in4
	%a5 = load i64, i64* %in5
	%a6 = load i64, i64* %in6
	%a7 = load i64, i64* %in7
	%a8 = load i64, i64* %in8
	%a9 = load i64, i64* %in9
	%a10 = load i64, i64* %in10
	%a11 = load i64, i64* %in11
	%a12 = load i64, i64* %in12
	%a13 = load i64, i64* %in13

	;sort
	call void @quicksort(%arr* @input, i64 0, i64 13)

	;get sorted array
	%b0 = load i64, i64* %in0
	%b1 = load i64, i64* %in1
	%b2 = load i64, i64* %in2
	%b3 = load i64, i64* %in3
	%b4 = load i64, i64* %in4
	%b5 = load i64, i64* %in5
	%b6 = load i64, i64* %in6
	%b7 = load i64, i64* %in7
	%b8 = load i64, i64* %in8
	%b9 = load i64, i64* %in9
	%b10 = load i64, i64* %in10
	%b11 = load i64, i64* %in11
	%b12 = load i64, i64* %in12
	%b13 = load i64, i64* %in13

	%s = getelementptr [170 x i8], [170 x i8]* @output_str, i32 0, i32 0

	call void @printf(i8* %s, i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 %a7, i64 %a8, i64 %a9, i64 %a10, i64 %a11, i64 %a12, i64 %a13, i64 %b0, i64 %b1, i64 %b2, i64 %b3, i64 %b4, i64 %b5, i64 %b6, i64 %b7, i64 %b8, i64 %b9, i64 %b10, i64 %b11, i64 %b12, i64 %b13)

	ret i64 1


}