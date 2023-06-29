define i8 @foo(float noundef %0) #0 {

  %a = alloca i8, align 4
  store i8 2, i8* %a, align 4
  %b = load i32, i32* %a, align 4

  %d = alloca i32, align 4
  store i32 %b, i32* %d, align 4
  %e = load i8, i8* %d
  ret i8 %e
}

; ASSERT EQ: i8 2 = call i8 @foo()