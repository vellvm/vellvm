declare i64 @ll_weighted_sum(i64, i64, i64, i64, i64, i64, i64, i64)

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @ll_weighted_sum (i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8)
  ret i64 %1
}
