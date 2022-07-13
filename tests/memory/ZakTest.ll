define i32 @test() {
  %x = 8
  %y = %x
  ret %y
}

; ASSERT EQ 8, call i32 @test() 


