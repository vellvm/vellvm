define i1 @main(i32 %argc, i8** %arcv) {
  %x = add i1 0, 1
  %y = add i1 %x, 0
  ret i1 %y
}


; ASSERT EQ: i1 1 = call i1 @main(i64 0, i8** null)

