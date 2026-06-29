define i1 @icmp_eq(i32 %x, i32 %y) {
  %ans = icmp eq i32 %x, %y
  ret i1 %ans
}

; ASSERT EQ: i1 1 = call i1 @icmp_eq(i32 0, i32 0)
; ASSERT EQ: i1 0 = call i1 @icmp_eq(i32 0, i32 17)

define i1 @icmp_ult(i32 %x, i32 %y) {
  %ans = icmp ult i32 %x, %y
  ret i1 %ans
}

; ASSERT EQ: i1 0 = call i1 @icmp_ult(i32 0, i32 0)
; ASSERT EQ: i1 1 = call i1 @icmp_ult(i32 0, i32 17)


define i1 @icmp_slt(i32 %x, i32 %y) {
  %ans = icmp slt i32 %x, %y
  ret i1 %ans
}

; ASSERT EQ: i1 0 = call i1 @icmp_slt(i32 0, i32 0)
; ASSERT EQ: i1 1 = call i1 @icmp_slt(i32 0, i32 17)
; ASSERT EQ: i1 1 = call i1 @icmp_slt(i32 -1, i32 17)
; ASSERT EQ: i1 1 = call i1 @icmp_slt(i32 -25, i32 -17)


define i1 @icmp_samesign_eq(i32 %x, i32 %y) {
  %ans = icmp samesign eq i32 %x, %y
  ret i1 %ans
}

; ASSERT EQ: i1 1 = call i1 @icmp_samesign_eq(i32 0, i32 0)
; ASSERT EQ: i1 0 = call i1 @icmp_samesign_eq(i32 0, i32 17)
; ASSERT EQ i1 poison = call i1 @icmp_samesign_eq(i32 -1, i32 17)
; ASSERT EQ: i1 0 = call i1 @icmp_samesign_eq(i32 -25, i32 -17)
; ASSERT EQ i1 poison = call i1 @icmp_samesign_eq(i32 -25, i32 17)





