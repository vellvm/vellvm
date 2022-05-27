define i64 @test() {
  %x = inttoptr i64 255 to i32*
  %ans = ptrtoint i32* %x to i64
  ret i64 %ans
}


; ASSERT EQ: i64 255 = call i64 @test()
