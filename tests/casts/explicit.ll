define i32 @main() #0 {
  %a = alloca i8, align 4
  store i8 2, i8* %a, align 4
  %b = load i8, i8* %a, align 4
  %c = zext i8 %b to i32
  ret i32 %c
}

; ASSERT EQ: i32 3 = call i32 @foo()