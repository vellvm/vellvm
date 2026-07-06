define <4 x float> @vec_add() {
   %p1 = alloca < 4 x float >
   %p2 = alloca < 4 x float >
   %v1 = load < 4 x float >, ptr %p1
   %v2 = load < 4 x float >, ptr %p2   
   %x1 = insertelement <4 x float> %v1, float 1.0, i32 0
   %x2 = insertelement <4 x float> %x1, float 2.0, i32 1
   %x3 = insertelement <4 x float> %x2, float 4.0, i32 2
   %x4 = insertelement <4 x float> %x3, float 8.0, i32 3		
   %y1 = insertelement <4 x float> %v2, float 0.0, i32 0
   %y2 = insertelement <4 x float> %y1, float 1.0, i32 1
   %y3 = insertelement <4 x float> %y2, float 2.0, i32 2
   %y4 = insertelement <4 x float> %y3, float 3.0, i32 3		
   %ans = fadd <4 x float> %x4, %y4
   ret <4 x float> %ans
}

define <4 x float> @vec_mul() {
   %p1 = alloca < 4 x float >
   %p2 = alloca < 4 x float >
   %v1 = load < 4 x float >, ptr %p1
   %v2 = load < 4 x float >, ptr %p2   
   %x1 = insertelement <4 x float> %v1, float 1.0, i32 0
   %x2 = insertelement <4 x float> %x1, float 2.0, i32 1
   %x3 = insertelement <4 x float> %x2, float 4.0, i32 2
   %x4 = insertelement <4 x float> %x3, float 8.0, i32 3		
   %y1 = insertelement <4 x float> %v2, float 0.0, i32 0
   %y2 = insertelement <4 x float> %y1, float 1.0, i32 1
   %y3 = insertelement <4 x float> %y2, float 2.0, i32 2
   %y4 = insertelement <4 x float> %y3, float 3.0, i32 3		
   %ans = fmul <4 x float> %x4, %y4
   ret <4 x float> %ans
}

define <4 x float> @vec_sub() {
   %p1 = alloca < 4 x float >
   %p2 = alloca < 4 x float >
   %v1 = load < 4 x float >, ptr %p1
   %v2 = load < 4 x float >, ptr %p2   
   %x1 = insertelement <4 x float> %v1, float 1.0, i32 0
   %x2 = insertelement <4 x float> %x1, float 2.0, i32 1
   %x3 = insertelement <4 x float> %x2, float 4.0, i32 2
   %x4 = insertelement <4 x float> %x3, float 8.0, i32 3		
   %y1 = insertelement <4 x float> %v2, float 0.0, i32 0
   %y2 = insertelement <4 x float> %y1, float 1.0, i32 1
   %y3 = insertelement <4 x float> %y2, float 2.0, i32 2
   %y4 = insertelement <4 x float> %y3, float 3.0, i32 3		
   %ans = fsub <4 x float> %x4, %y4
   ret <4 x float> %ans
}


define <4 x float> @vec_div() {
   %p1 = alloca < 4 x float >
   %p2 = alloca < 4 x float >
   %v1 = load < 4 x float >, ptr %p1
   %v2 = load < 4 x float >, ptr %p2   
   %x1 = insertelement <4 x float> %v1, float 1.0, i32 0
   %x2 = insertelement <4 x float> %x1, float 2.0, i32 1
   %x3 = insertelement <4 x float> %x2, float 4.0, i32 2
   %x4 = insertelement <4 x float> %x3, float 8.0, i32 3		
   %y1 = insertelement <4 x float> %v2, float 0.0, i32 0
   %y2 = insertelement <4 x float> %y1, float 1.0, i32 1
   %y3 = insertelement <4 x float> %y2, float 2.0, i32 2
   %y4 = insertelement <4 x float> %y3, float 3.0, i32 3		
   %ans = fdiv <4 x float> %y4, %x4
   ret <4 x float> %ans
}


define <4 x float> @vec_neg() {
   %p1 = alloca < 4 x float >
   %v1 = load < 4 x float >, ptr %p1
   %x1 = insertelement <4 x float> %v1, float 1.0, i32 0
   %x2 = insertelement <4 x float> %x1, float 2.0, i32 1
   %x3 = insertelement <4 x float> %x2, float 4.0, i32 2
   %x4 = insertelement <4 x float> %x3, float 8.0, i32 3		
   %ans = fneg <4 x float> %x4
   ret <4 x float> %ans
}



; ASSERT EQ: <4 x float> <float 1.0, float 3.0, float 6.0, float 11.0> = call <4 x float> @vec_add()
; ASSERT EQ: <4 x float> <float 0.0, float 2.0, float 8.0, float 24.0> = call <4 x float> @vec_mul()
; ASSERT EQ: <4 x float> <float 1.0, float 1.0, float 2.0, float 5.0> = call <4 x float> @vec_sub()
; ASSERT EQ: <4 x float> <float 0.0, float 0.5, float 0.5, float 0.375> = call <4 x float> @vec_div()
; ASSERT EQ: <4 x float> <float -1.0, float -2.0, float -4.0, float -8.0> = call <4 x float> @vec_neg()
