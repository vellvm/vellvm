@gbl = global i64 12

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = load i64, i64* @gbl
  ret i64 %1
}
