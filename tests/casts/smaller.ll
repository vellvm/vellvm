define i8 @foo() #0 {
  %a = alloca i32, align 4
  store i32 2, i32* %a, align 4
  %b = load i8, i8* %a, align 4
  ret i8 %b
}

; ASSERT POISON: call i8 @foo()