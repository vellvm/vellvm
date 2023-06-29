define i32 @main() #0 {
  %a = alloca float
  store float 2.0, float* %a
  %b = load i32, i32* %a
  ret i32 %b
}

; ASSERT EQ: i32 2 = call i32 @foo()
; ASSERT POISON: call i32 @foo()