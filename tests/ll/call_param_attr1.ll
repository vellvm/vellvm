define i8 @foo(i8 signext %arg) {
  ret i8 %arg
}

define i32 @main(i32 %argc, i8** %arcv) {
  %ans = call i8 @foo(i8 signext 5)
  ret i8 %ans
}   

