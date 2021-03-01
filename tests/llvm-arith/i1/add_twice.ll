define i1 @main(i32 %argc, i8** %arcv) {
  %1 = add i1 0, 0
  %2 = add i1 %1, 1
  ret i1 %2
}


; ASSERT EQ: i1 1 = call i1 @main(i64 0, i8** null)

