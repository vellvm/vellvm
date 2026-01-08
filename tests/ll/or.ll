define i32 @or_i32(i32 %x, i32 %y) {
  %ans = or i32 %x, %y
  ret i32 %ans
}

; ASSERT EQ: i32 0  = call i32 @or_i32(i32 0, i32 0)
; ASSERT EQ: i32 17 = call i32 @or_i32(i32 0, i32 17)
; ASSERT EQ: i32 23 = call i32 @or_i32(i32 7, i32 17)

define i32 @or_disjoint(i32 %x, i32 %y) {
  %ans = or disjoint i32 %x, %y
  ret i32 %ans
}

; ASSERT EQ: i32 0  = call i32 @or_disjoint(i32 0, i32 0)
; ASSERT EQ: i32 17 = call i32 @or_disjoint(i32 0, i32 17)
; ASSERT POISON: call i32 @or_disjoint(i32 7, i32 17)


define i64 @main(i64 %argc, i8** %arcv) {
  %1 = or i64 1, 0
  ret i64 %1
}
