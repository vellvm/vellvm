define i32 @main(i32 %argc, i8** %arcv) {
  %1 = add i8 5, 9
  %2 = add i8 %1, 15
  %3 = zext i8 %2 to i32
  ret i32 %3
}
