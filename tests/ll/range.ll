; The range parameter attribute.
;
; LangRef: an argument outside its range(lo, hi) is poison.  On its own
; that is all that happens (@in_range).  Together with noundef, the poison
; argument is immediate undefined behavior (@in_range_noundef).

define i64 @in_range(i64 range(i64 1, 50) %x) {
  ret i64 %x
}

define i64 @in_range_noundef(i64 noundef range(i64 1, 50) %x) {
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @in_range_noundef(i64 noundef range(i64 1, 10) 8)
  ret i64 %1
}

; ASSERT EQ: i64 6 = call i64 @in_range(i64 6)
; ASSERT EQ: i64 1 = call i64 @in_range(i64 1)
; ASSERT EQ: i64 49 = call i64 @in_range(i64 49)
; ASSERT EQ: i64 poison = call i64 @in_range(i64 0)
; ASSERT EQ: i64 poison = call i64 @in_range(i64 50)
; ASSERT EQ: i64 poison = call i64 @in_range(i64 500)

; ASSERT EQ: i64 6 = call i64 @in_range_noundef(i64 6)
; ASSERT UB 12: call i64 @in_range_noundef(i64 0)
; ASSERT UB 12: call i64 @in_range_noundef(i64 50)
; ASSERT UB 12: call i64 @in_range_noundef(i64 500)

; ASSERT EQ: i64 8 = call i64 @main(i64 1, i8** null)
