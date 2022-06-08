define i64 @alloca_in_loop(i64 %n) {
    %ctr_ptr = alloca i64
    store i64 %n, i64* %ctr_ptr
    br label %loop_start

loop_start:
    %ctr = load i64, i64* %ctr_ptr
    %is_base = icmp sle i64 %ctr, 0
    br i1 %is_base, label %loop_exit, label %loop_continue

loop_exit:
    ret i64 1

loop_continue:
    %foo = alloca i64
    %ctr_decr = sub i64 %ctr, 1
    store i64 %ctr_decr, i64* %ctr_ptr
    br label %loop_start
}

define i64 @fib(i64 %n) {
    %foo = call i64 @alloca_in_loop(i64 %n)
    %is_base = icmp sle i64 %n, 2
    br i1 %is_base, label %base, label %recurse

base:
    ret i64 1

recurse:
    %n1 = sub i64 %n, 1
    %n2 = sub i64 %n, 2
    %fib1 = call i64 @fib(i64 %n1)
    %fib2 = call i64 @fib(i64 %n2)
    %sum = add i64 %fib1, %fib2
    ret i64 %sum
}

define i64 @main(i64 %argc, i8** %argv) {
    %result = call i64 @fib(i64 7)
    %is_correct = icmp eq i64 %result, 13
    br i1 %is_correct, label %correct, label %incorrect

correct:
    %foo = call i64 @alloca_in_loop(i64 100)
    ret i64 1

incorrect:
    ret i64 0
}