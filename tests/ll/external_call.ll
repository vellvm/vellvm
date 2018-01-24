declare i64 @ll_external(i64)

define i64 @main(i64 %argc, i8** %argv) {
  %v = call i64 @ll_external (i64 0)
  ret i64 %v
}

