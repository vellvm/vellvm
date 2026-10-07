define i32 @shl_test(i32 %x, i32 %amt) {
  %1 = shl i32 %x, %amt
  ret i32 %1
}
; ASSERT EQ: i32 3 = call i32 @shl_test(i32 3, i32 0)
; ASSERT EQ: i32 6 = call i32 @shl_test(i32 3, i32 1)
; ASSERT EQ: i32 12 = call i32 @shl_test(i32 3, i32 2)
; ASSERT EQ: i32 24 = call i32 @shl_test(i32 3, i32 3)
