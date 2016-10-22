%struct = type { i64, [5 x i64], i64}

@gbl = global %struct {i64 1, [5 x i64] [i64 2, i64 3, i64 4, i64 5, i64 6], i64 7}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = getelementptr %struct, %struct* @gbl, i32 0, i32 1, i32 2
  %2 = load i64, i64* %1
  ret i64 %2
}
