define i8 @main(i8 %argc, i8** %arcv) {
  %1 = sub nuw i8 0, 1
  ret i8 %1
}

; ASSERT EQ i8 poison = call i8 @main(i8 1, i8** null)
