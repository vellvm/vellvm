define i32 @main(i32 %argc, i8** %arcv) {
  %1 = sub nsw i32 2147483647, -1 
  ret i32 %1
}
; ASSERT EQ i32 poison = call i32 @main(i32 1, i8** null)
