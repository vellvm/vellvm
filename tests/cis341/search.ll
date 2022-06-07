@unsorted = global [7 x i64] [i64 74, i64 3, i64 5, i64 8, i64 2, i64 50, i64 9]

define i64 @search(i64 %lo, i64 %hi, i64 %target, [7 x i64]* %list) {
    %cmp1 = icmp eq i64 %lo, %hi
    br i1 %cmp1, label %base_case, label %check 
base_case: 
    %lo_addr = getelementptr [7 x i64], [7 x i64]* %list, i32 0, i64 %lo
    %lo_val = load i64, i64* %lo_addr
    %cmp2 = icmp eq i64 %target, %lo_val
    br i1 %cmp2, label %true, label %false
true: 
    ret i64 1
false:
    ret i64 0
check:
    %lo_addr_check = getelementptr [7 x i64], [7 x i64]* %list, i32 0, i64 %lo
    %lo_val_check = load i64, i64* %lo_addr_check
    %cmp3 = icmp eq i64 %target, %lo_val_check
    br i1 %cmp3, label %true, label %recurse
recurse: 
    %new_lo = add i64 %lo, 1
    %ans_rec = call i64 @search(i64 %new_lo, i64 %hi, i64 %target, [7 x i64]* %list)
    ret i64 %ans_rec
}

define i64 @main(i64 %argc, i8** %arcv) {
    %ans = call i64 @search(i64 0, i64 6, i64 54, [7 x i64]* @unsorted)
    ret i64 %ans
}