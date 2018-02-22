define i64 @main(i64 %argc, i8** %arcv) {
  %1 = sub nsw i64 9223372036854775807, -8 
  ret i64 %1
}
