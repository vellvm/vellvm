%arr = type [3 x i64]

@value = global %arr [ i64 3, i64 7, i64 1]

define i64 @cube(i64 %n) {
    %1 = mul i64 %n, %n
    %2 = mul i64 %1, %n
    ret i64 %2
}

define i64 @value_lookup(i64 %i) {
    %ptr = getelementptr %arr, %arr* @value, i64 0, i64 %i
    %ret = load i64, i64* %ptr
    ret i64 %ret
}

define i64 @sum_three(i64 %0, i64 %1, i64 %2) {
    %add1 = add i64 %0, %1
    %add2 = add i64 %add1, %2
    ret i64 %add2
}

define i64 @number_from_digits(i64 %0, i64 %1, i64 %2) {
    %hundreds = mul i64 %0, 100
    %tens = mul i64 %1, 10
    %ones = mul i64 %2, 1
    %res = call i64 @sum_three(i64 %ones, i64 %tens, i64 %hundreds)
    ret i64 %res
}

define i64 @main(i64 %argc, i8** %arcv) {
    %a = call i64 @value_lookup(i64 0)
    %b = call i64 @value_lookup(i64 1)
    %c = call i64 @value_lookup(i64 2)
    %v = call i64 @number_from_digits(i64 %a, i64 %b, i64 %c)

    %a_cubed = call i64 @cube(i64 %a)
    %b_cubed = call i64 @cube(i64 %b)
    %c_cubed = call i64 @cube(i64 %c)
    %sum_cubed = call i64 @sum_three(i64 %a_cubed, i64 %b_cubed, i64 %c_cubed)

    %cmp = icmp eq i64 %v, %sum_cubed
    br i1 %cmp, label %ret_true, label %ret_false
ret_true:
    ret i64 1
ret_false:
    ret i64 0
}