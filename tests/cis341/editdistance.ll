%mat = type [7 x [12 x i64]]

@arr1 = global [6 x i64] [i64 107, i64 105, i64 116, i64 116, i64 101, i64 110] 
@arr2 = global [11 x i64] [i64 98, i64 97, i64 98, i64 121, i64 115, i64 105, i64 116, i64 116, i64 105, i64 110, i64 103]
@arr1len = global i64 6
@arr2len = global i64 11


@dp = global %mat [
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0],
    [12 x i64] [i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0,i64 0]]

define void @writedp(i64 %i, i64 %j, i64 %val) {
    %ptr = getelementptr %mat, %mat* @dp, i64 0, i64 %i, i64 %j
    store i64 %val, i64* %ptr
    ret void
}

define i64 @getdp(i64 %i, i64 %j) {
    %ptr = getelementptr %mat, %mat* @dp, i64 0, i64 %i, i64 %j
    %1 = load i64, i64* %ptr
    ret i64 %1
}

define i64 @getval(i64* %ptr) {
    %1 = load i64, i64* %ptr
    ret i64 %1
}

define i64 @min2(i64 %a, i64 %b) {
    %cmp = icmp sgt i64 %a, %b
    br i1 %cmp, label %agt, label %bgt
agt:
    ret i64 %b
bgt:
    ret i64 %a
}

define i64 @min3(i64 %a, i64 %b, i64 %c) {
    %1 = call i64 @min2(i64 %a, i64 %b)
    %2 = call i64 @min2(i64 %1, i64 %c)
    ret i64 %2
}

define void @compute_cost(i64 %row, i64 %col) {
    %1 = sub i64 %row, 1
    %2 = getelementptr [6 x i64], [6 x i64]* @arr1, i64 0, i64 %1
    %3 = load i64, i64* %2
    %4 = sub i64 %col, 1
    %5 = getelementptr [11 x i64], [11 x i64]* @arr2, i64 0, i64 %4
    %6 = load i64, i64* %5
    %7 = alloca i64
    %8 = icmp eq i64 %3, %6
    br i1 %8, label %ifeq, label %ifnoteq
ifeq:
    store i64 0, i64* %7
    br label %cont
ifnoteq:
    store i64 1, i64* %7
    br label %cont
cont:
    %9 = call i64 @getdp(i64 %1, i64 %col)
    %10 = call i64 @getdp(i64 %row, i64 %4)
    %11 = call i64 @getdp(i64 %1, i64 %4)
    %12 = load i64, i64* %7
    %13 = add i64 %9, 1
    %14 = add i64 %10, 1
    %15 = add i64 %11, %12  
    %16 = call i64 @min3(i64 %13, i64 %14, i64 %15)
    call void @writedp(i64 %row, i64 %col, i64 %16)
    ret void
}

define i64 @levenshtein() {
    %1 = alloca i64
    store i64 0, i64* %1
    %2 = alloca i64
    store i64 0, i64* %2
    br label %init1
init1:
    %3 = load i64, i64* %1
    call void @writedp(i64 %3, i64 0, i64 %3)
    %4 = add i64 %3, 1
    store i64 %4, i64* %1
    %5 = call i64 @getval(i64* @arr1len)
    %6 = icmp sge i64 %4, %5
    br i1 %6, label %init2, label %init1
init2:
    %7 = load i64, i64* %2
    call void @writedp(i64 0, i64 %7, i64 %7)
    %8 = add i64 %7, 1
    store i64 %8, i64* %2
    %9 = call i64 @getval(i64* @arr2len)
    %10 = icmp sge i64 %8, %9
    br i1 %10, label %proc, label %init2
proc:
    store i64 1, i64* %1
    store i64 1, i64* %2
    br label %iterrow
iterrow:
    %row = load i64, i64* %1
    %col = load i64, i64* %2
    call void @compute_cost(i64 %row, i64 %col)
    %11 = add i64 %col, 1
    store i64 %11, i64* %2
    %12 = call i64 @getval(i64* @arr2len)
    %13 = icmp sge i64 %11, %12
    br i1 %13, label %newrow, label %iterrow 
newrow:
    %14 = add i64 %row, 1
    store i64 %14, i64* %1
    store i64 1, i64* %2
    %15 = call i64 @getval(i64* @arr1len)
    %16 = icmp sge i64 %14, %15
    br i1 %16, label %term, label %iterrow 
term:
    %17 = call i64 @getval(i64* @arr1len)
    %18 = sub i64 %17, 1
    %19 = call i64 @getval(i64* @arr2len)
    %20 = sub i64 %19, 1
    %21 = call i64 @getdp(i64 %18, i64 %20)
    ret i64 %21
}

define i64 @main(i64 %argc, i8** %arcv) {
    %1 = call i64 @levenshtein()
    ret i64 %1
}