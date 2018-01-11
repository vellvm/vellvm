define i32 @main(i32 %argc, i8** %argv) {
  %x = add i8 1234, 5678
  %y = zext i8 %x to i32
  ret i32 %y
}
