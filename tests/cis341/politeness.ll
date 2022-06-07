define i64 @politeness(i64 %n) {
    %i = alloca i64
    %counter = alloca i64
    store i64 0, i64* %i
    store i64 0, i64* %counter
    br label %start

start:
    %1 = load i64, i64* %i
    %t = add i64 %1, 1
    store i64 %t, i64* %i
    %2 = icmp slt i64 %t, %n
    br i1 %2, label %outer, label %end
outer:
    %sum = alloca i64 ; sum of inner loop
    store i64 0, i64* %sum
    
    %j = alloca i64; inner loop
    %3 = load i64, i64* %i
    store i64 %3, i64* %j
    br label %inner
inner:
    %4 = load i64, i64* %j ; j
    %5 = load i64, i64* %sum ; sum
    %6 = add i64 %4, %5 ; j + sum
    store i64 %6, i64* %sum ; sum = j + sum
    %7 = add i64 %4, 1 ; j + 1
    store i64 %7, i64* %j ; j = j + 1
    %8 = icmp eq i64 %6, %n ;  sum = n
    br i1 %8, label %increment, label %next
increment:
    %9 = load i64, i64* %counter
    %10 = add i64 %9, 1
    store i64 %10, i64* %counter ; counter = counter + 1
    br label %start 
next:
    %11 = load i64, i64* %sum ; sum
    %12 = icmp sgt i64 %11, %n ; sum > n
    br i1 %12, label %start, label %inner

end:
    %13 = load i64, i64* %counter
    ret i64 %13 ; return counter
}

define i64 @main(i64 %argc, i8** %arcv) {
    %1 = call i64 @politeness(i64 15)
    ret i64 %1
}