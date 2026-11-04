; Regression test: shifting by an amount >= the bitwidth must produce
; poison without first computing the (unbounded) shifted value.
; `shl i64 1, -1` would otherwise build a 2^64-bit number.
define i64 @shl_huge(i64 %a, i64 %b) {
  %r = shl i64 %a, %b
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @shl_huge(i64 1, i64 -1)
