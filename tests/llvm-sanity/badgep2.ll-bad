define i32 @main(i32 %argc, i8** %arcv) {
  %1 = alloca { i32, i32 }
  store { i32, i32 } { i32 1, i32 2 }, { i32, i32 }* %1
  %4 = getelementptr { i32, i32 }, { i32, i32 }* %1, i32 0, i32 undef
  %5 = load i32, i32* %4
  ret i32 %5
}
