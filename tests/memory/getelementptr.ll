define i32 @testGetXth(i32 %choice) {
  %ptr = alloca [4 x i32]
  store [4 x i32] [i32 15, i32 100, i32 2, i32 33], [4 x i32]* %ptr
  %address = getelementptr [4 x i32], [4 x i32]* %ptr, i32 0, i32 %choice
  %val = load i32, i32* %address
  ret i32 %val
}

; ASSERT EQ: i32 15 = call i32 @testGetXth(i32 0)
; ASSERT EQ: i32 100 = call i32 @testGetXth(i32 1)
; ASSERT EQ: i32 2 = call i32 @testGetXth(i32 2)
; ASSERT EQ: i32 33 = call i32 @testGetXth(i32 3)
