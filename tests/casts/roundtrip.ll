define float @main(float noundef %0) #0 {

  %a = alloca float, align 4
  store float 2.0, float* %a, align 4
  %b = load i32, i32* %a, align 4

  %d = alloca i32, align 4
  store i32 %b, i32* %d, align 4
  %e = load float, float* %d
  ret float %e
}

; ASSERT EQ: float 2.0 = call i8 @foo()