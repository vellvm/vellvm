declare i64 @ll_external(i64)
declare i64 @ll_external2(i64)

define i64 @main(i64 %argc, i8** %argv) {
  %v = call i64 @ll_external (i64 0)
  %w = call i64 @ll_external2 (i64 0)  
  ret i64 %v
}

