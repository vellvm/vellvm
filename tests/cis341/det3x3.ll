@row1 = global [3 x i64] [i64 4, i64 3, i64 6]
@row2 = global [3 x i64] [i64 5, i64 1, i64 2]
@row3 = global [3 x i64] [i64 6, i64 1, i64 1]


define i64 @calc_det() {
    %1 = getelementptr [3 x i64], [3 x i64]* @row1, i64 0, i64 0
    %2 = getelementptr [3 x i64], [3 x i64]* @row1, i64 0, i64 1
    %3 = getelementptr [3 x i64], [3 x i64]* @row1, i64 0, i64 2
    %4 = getelementptr [3 x i64], [3 x i64]* @row2, i64 0, i64 0
    %5 = getelementptr [3 x i64], [3 x i64]* @row2, i64 0, i64 1
    %6 = getelementptr [3 x i64], [3 x i64]* @row2, i64 0, i64 2
    %7 = getelementptr [3 x i64], [3 x i64]* @row3, i64 0, i64 0
    %8 = getelementptr [3 x i64], [3 x i64]* @row3, i64 0, i64 1
    %9 = getelementptr [3 x i64], [3 x i64]* @row3, i64 0, i64 2
    
    %10 = load i64, i64* %1
    %11 = load i64, i64* %2
    %12 = load i64, i64* %3
    %13 = load i64, i64* %4
    %14 = load i64, i64* %5
    %15 = load i64, i64* %6
    %16 = load i64, i64* %7
    %17 = load i64, i64* %8
    %18 = load i64, i64* %9

    %19 = mul i64 %14, %18
    %20 = mul i64 %17, %15
    %21 = mul i64 %13, %18
    %22 = mul i64 %16, %15
    %23 = mul i64 %13, %17
    %24 = mul i64 %14, %16

    %25 = sub i64 %19, %20
    %26 = sub i64 %22, %21
    %27 = sub i64 %23, %24

    %28 = mul i64 %10, %25
    %29 = mul i64 %11, %26
    %30 = mul i64 %12, %27

    %31 = add i64 %28, %29
    %32 = add i64 %30, %31

    %33 = sub i64 %10, %12
    ret i64 %32

}





define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @calc_det()
  ret i64 %1
}

