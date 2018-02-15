@G1 = global i64 17
@F1 = global i64 (i64)* @fun

define i64 @fun (i64 %arg) {
  %x = load i64, i64* @G1
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ans = call i64 @fun(i64 0)
  ret i64 %ans
}



