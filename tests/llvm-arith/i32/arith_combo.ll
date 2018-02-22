define i32 @main(i32 %argc, i8** %arcv) {
  %1 = add i32 5, 9
  %2 = mul i32 3, 6
  %3 = sub i32 %2, %1
  ret i32 %3
}
