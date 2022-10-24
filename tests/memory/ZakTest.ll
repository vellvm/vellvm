define i32 @test() {
  %x = add i32 8, 0
  %y = mul i32 %x, 1
  ret i32 %y
}

; ASSERT EQ: i32 8 = call i32 @test() 


