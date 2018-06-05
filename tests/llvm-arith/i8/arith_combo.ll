define i8 @main(i8 %argc, i8** %arcv) {
  %1 = add i8 5, 9
  %2 = mul i8 3, 6
  %3 = sub i8 %2, %1
  ret i8 %3
}
