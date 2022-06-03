define i64 @test64to32() {
  %x = inttoptr i64 113 to i32*
  %ans = ptrtoint i32* %x to i64
  ret i64 %ans
}


define i64 @test64to32two() {
  %x = inttoptr i64 0 to i32*
  %ans = ptrtoint i32* %x to i64
  ret i64 %ans
}

define i64 @test32to64() {
  %x = inttoptr i32 0 to i32*
  %ans = ptrtoint i32* %x to i64
  ret i64 %ans
}

; ASSERT EQ: i64 113 = call i64 @test64to32()
; ASSERT EQ: i64 0 = call i64 @test64to32two()
; ASSERT EQ: i64 0 = call i64 @test32to64()
