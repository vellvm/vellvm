declare i32 @puts(i8* %str)

define i32 @main(i32 %argc, i8** %argv) {
    %str = alloca [13 x i8]
    %p0 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 0
    store i8 72, i8* %p0
    %p1 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 1
    store i8 101, i8* %p1
    %p2 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 2
    store i8 108, i8* %p2
    %p3 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 3
    store i8 108, i8* %p3
    %p4 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 4
    store i8 111, i8* %p4
    %p5 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 5
    store i8 32, i8* %p5
    %p6 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 6
    store i8 119, i8* %p6
    %p7 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 7
    store i8 111, i8* %p7
    %p8 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 8
    store i8 114, i8* %p8
    %p9 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 9
    store i8 108, i8* %p9
    %p10 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 10
    store i8 100, i8* %p10
    %p11 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 11
    store i8 33, i8* %p11
    %p12 = getelementptr [13 x i8], [13 x i8]* %str, i64 0, i64 12
    store i8 0, i8* %p12
    %p = bitcast [13 x i8]* %str to i8*
    %ans = call i32 @puts(i8* %p)
    ret i32 %ans
}
