define i32 @main(i32 %argc, i8** %arcv) {
  %x = alloca { i32, i32 }
  %y = add i32 0, 2
  store { i32, i32 } { i32 %y, i32 %y }, { i32, i32 }* %x
  %z = getelementptr { i32, i32 }, { i32, i32 }* %x, i32 0, i32 0
  %w = load i32, i32* %z
  ret i32 %w
}
