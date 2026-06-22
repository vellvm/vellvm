define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca i64
  store i64 3, i64* %1
  %2 = bitcast i64* %1 to [10 x i64]*
  %3 = bitcast [10 x i64]* %2 to i64*
  %4 = load i64, i64* %3
  ret i64 %4
}


; ASSERT EQ: i64 3 = call i64 @main(i64 0, i8** null)
