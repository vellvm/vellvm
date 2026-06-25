define i64 @foo(i64 noundef range(i64 1, 50) %x) {
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 noundef range(i64 1, 10) 8)
  ret i64 %1
}

; ASSERT EQ: i64 6 = call i64 @foo(i64 6)
; ASSERT EQ i64 poison = call i64 @foo(i64 0)
; ASSERT EQ i64 poison = call i64 @foo(i64 500)
