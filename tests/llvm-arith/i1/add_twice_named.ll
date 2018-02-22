define i1 @main(i32 %argc, i8** %arcv) {
  %x = add i1 0, 1
  %y = add i1 %x, 0
  ret i1 %y
}

