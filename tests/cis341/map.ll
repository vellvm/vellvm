@gbl1 = global [3 x i64] [i64 1, i64 2, i64 3]
@gbl2 = global [3 x i64] [i64 1, i64 2, i64 3]

define i64 @square(i64 %x1) {
%1 = mul i64 %x1, %x1
ret i64 %1
}

define i64 @cube(i64 %x1) {
%1 = mul i64 %x1, %x1
%2 = mul i64 %1, %x1
ret i64 %2
}

define void @map(i64(i64)* %fn, i64* %ptr, i64 %size) {
%1 = icmp eq i64 %size, 0
br i1 %1, label %then, label %else
then:
ret void
else:
%2 = getelementptr i64, i64* %ptr, i64 0
%3 = load i64, i64* %2
%4 = call i64 %fn(i64 %3)
store i64 %4, i64* %2
%5 = sub i64 %size, 1
%6 = getelementptr i64, i64* %ptr, i64 1
%7 = sub i64 %size, 1
call void @map(i64(i64)* %fn, i64* %6, i64 %7)
ret void
}

define i64 @main(i64 %argc, i8** %argv) {
%1 = getelementptr [3 x i64], [3 x i64]* @gbl1, i64 0, i64 0
%2 = getelementptr [3 x i64], [3 x i64]* @gbl1, i64 0, i64 1
%3 = getelementptr [3 x i64], [3 x i64]* @gbl1, i64 0, i64 2
call void @map(i64(i64)* @square, i64* %1, i64 3)
%4 = load i64, i64* %1
%5 = load i64, i64* %2
%6 = load i64, i64* %3
%7 = add i64 %4, %5
%8 = add i64 %7, %6

%9 = getelementptr [3 x i64], [3 x i64]* @gbl2, i64 0, i64 0
%10 = getelementptr [3 x i64], [3 x i64]* @gbl2, i64 0, i64 1
%11 = getelementptr [3 x i64], [3 x i64]* @gbl2, i64 0, i64 2
call void @map(i64(i64)* @cube, i64* %9, i64 3)
%12 = load i64, i64* %9
%13 = load i64, i64* %10
%14 = load i64, i64* %11
%15 = add i64 %12, %13
%16 = add i64 %15, %14
%17 = add i64 %8, %16
ret i64 %17
}