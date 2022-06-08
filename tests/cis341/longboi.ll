define i64 @longboi(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8) {
  %1 = sub i64 %x7, %x8
  ret i64 %1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @longboi(i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 9, i64 5)
  ret i64 %1
}