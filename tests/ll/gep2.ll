@tmp = global [5 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5]

define i64 @main(i32 %i) {
  %1 = alloca i64
  %2 = getelementptr [5 x i64], [5 x i64]* @tmp, i32 0, i32 %i
  %3 = load i64, i64* %2
  ret i64 %3
}

; ASSERT EQ: i64 4 = call i64 @main(i32 3)
; ASSERT EQ: i64 5 = call i64 @main(i32 4)
