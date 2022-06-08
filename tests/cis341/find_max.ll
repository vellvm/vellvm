%arr = type [8 x i64]

@input = global %arr [i64 50, i64 60, i64 40, i64 70, i64 30, i64 80, i64 20, i64 80]
@length = global i64 8

define i64 @find_max (){
    %max = alloca i64
    %ctr_addr = alloca i64
    store i64 0, i64* %ctr_addr           ; initialize counter to 0
    %1 = getelementptr %arr, %arr* @input, i32 0, i64 0
    %l = load i64, i64* %1
    store i64 %l, i64* %max              ; %max <- first element in array
    br label %loop

    loop:
    %ctr = load i64, i64* %ctr_addr ; retrieve counter value
    %addr_of_current = getelementptr [8 x i64], [8 x i64]* @input, i32 0, i64 %ctr
    %current = load i64, i64* %addr_of_current      ; retrieve current value
    %t = load i64, i64* %max
    %flag = icmp slt i64 %t, %current
    br i1 %flag, label %update_max, label %move_on

    update_max:
    store i64 %current, i64* %max
    br label %move_on

    move_on:
    %g = load i64, i64* %ctr_addr
    %2 = add i64 1, %g
    store i64 %2, i64* %ctr_addr
    %flag2 = icmp eq i64 %2, 8
    br i1 %flag2, label %end, label %loop

    end:
    ret i64 %t
}

define i64 @main(i64 %argc, i8** %argv) {
    %1 = call i64 @find_max()
    ret i64 %1
}