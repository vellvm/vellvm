define i32 @foo() #0 {
  %a = alloca i8
  store i8 2, i8* %a
  %b = load i32, i32* %a
  ret i32 %b
}

; ASSERT EQ: i32 2 = call i32 @foo()