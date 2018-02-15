@G1 = global i64 17
@G2 = global i64* @G1

define i64 @main(i64 %argc, i8** %arcv) {
  %x = load i64*, i64** @G2
  %y = load i64, i64* %x
  ret i64 %y
}



