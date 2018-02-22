define i32 @main(i32 %argc, i8** %arcv) {
  %1 = add nsw i32 -2147483648, -1
  ret i32 %1
}
