define i32 @main(i32 %argc, i8** %arcv) {
  %1 = alloca [2 x i32]
  store [2 x i32] [ i32 1, i32 2 ], [2 x i32]* %1
  %2 = and i32 undef, 1
  %3 = or i32 %2, 1
  %4 = getelementptr [2 x i32], [2 x i32]* %1, i32 0, i32 %3
  %5 = load i32, i32* %4
  ret i32 %5
}
