define <4 x double> @vec_add() {
   %p1 = alloca < 4 x double >
   %p2 = alloca < 4 x double >
   %v1 = load < 4 x double >, ptr %p1
   %v2 = load < 4 x double >, ptr %p2   
   %x1 = insertelement <4 x double> %v1, double 1.0, i32 0
   %x2 = insertelement <4 x double> %x1, double 2.0, i32 1
   %x3 = insertelement <4 x double> %x2, double 4.0, i32 2
   %x4 = insertelement <4 x double> %x3, double 8.0, i32 3		
   %y1 = insertelement <4 x double> %v2, double 0.0, i32 0
   %y2 = insertelement <4 x double> %y1, double 1.0, i32 1
   %y3 = insertelement <4 x double> %y2, double 2.0, i32 2
   %y4 = insertelement <4 x double> %y3, double 3.0, i32 3		
   %ans = fadd <4 x double> %x4, %y4
   ret <4 x double> %ans
}

define <4 x double> @vec_mul() {
   %p1 = alloca < 4 x double >
   %p2 = alloca < 4 x double >
   %v1 = load < 4 x double >, ptr %p1
   %v2 = load < 4 x double >, ptr %p2   
   %x1 = insertelement <4 x double> %v1, double 1.0, i32 0
   %x2 = insertelement <4 x double> %x1, double 2.0, i32 1
   %x3 = insertelement <4 x double> %x2, double 4.0, i32 2
   %x4 = insertelement <4 x double> %x3, double 8.0, i32 3		
   %y1 = insertelement <4 x double> %v2, double 0.0, i32 0
   %y2 = insertelement <4 x double> %y1, double 1.0, i32 1
   %y3 = insertelement <4 x double> %y2, double 2.0, i32 2
   %y4 = insertelement <4 x double> %y3, double 3.0, i32 3		
   %ans = fmul <4 x double> %x4, %y4
   ret <4 x double> %ans
}

define <4 x double> @vec_sub() {
   %p1 = alloca < 4 x double >
   %p2 = alloca < 4 x double >
   %v1 = load < 4 x double >, ptr %p1
   %v2 = load < 4 x double >, ptr %p2   
   %x1 = insertelement <4 x double> %v1, double 1.0, i32 0
   %x2 = insertelement <4 x double> %x1, double 2.0, i32 1
   %x3 = insertelement <4 x double> %x2, double 4.0, i32 2
   %x4 = insertelement <4 x double> %x3, double 8.0, i32 3		
   %y1 = insertelement <4 x double> %v2, double 0.0, i32 0
   %y2 = insertelement <4 x double> %y1, double 1.0, i32 1
   %y3 = insertelement <4 x double> %y2, double 2.0, i32 2
   %y4 = insertelement <4 x double> %y3, double 3.0, i32 3		
   %ans = fsub <4 x double> %x4, %y4
   ret <4 x double> %ans
}


define <4 x double> @vec_div() {
   %p1 = alloca < 4 x double >
   %p2 = alloca < 4 x double >
   %v1 = load < 4 x double >, ptr %p1
   %v2 = load < 4 x double >, ptr %p2   
   %x1 = insertelement <4 x double> %v1, double 1.0, i32 0
   %x2 = insertelement <4 x double> %x1, double 2.0, i32 1
   %x3 = insertelement <4 x double> %x2, double 4.0, i32 2
   %x4 = insertelement <4 x double> %x3, double 8.0, i32 3		
   %y1 = insertelement <4 x double> %v2, double 0.0, i32 0
   %y2 = insertelement <4 x double> %y1, double 1.0, i32 1
   %y3 = insertelement <4 x double> %y2, double 2.0, i32 2
   %y4 = insertelement <4 x double> %y3, double 3.0, i32 3		
   %ans = fdiv <4 x double> %y4, %x4
   ret <4 x double> %ans
}


define <4 x double> @vec_neg() {
   %p1 = alloca < 4 x double >
   %v1 = load < 4 x double >, ptr %p1
   %x1 = insertelement <4 x double> %v1, double 1.0, i32 0
   %x2 = insertelement <4 x double> %x1, double 2.0, i32 1
   %x3 = insertelement <4 x double> %x2, double 4.0, i32 2
   %x4 = insertelement <4 x double> %x3, double 8.0, i32 3		
   %ans = fneg <4 x double> %x4
   ret <4 x double> %ans
}



; ASSERT EQ: <4 x double> <double 1.0, double 3.0, double 6.0, double 11.0> = call <4 x double> @vec_add()
; ASSERT EQ: <4 x double> <double 0.0, double 2.0, double 8.0, double 24.0> = call <4 x double> @vec_mul()
; ASSERT EQ: <4 x double> <double 1.0, double 1.0, double 2.0, double 5.0> = call <4 x double> @vec_sub()
; ASSERT EQ: <4 x double> <double 0.0, double 0.5, double 0.5, double 0.375> = call <4 x double> @vec_div()
; ASSERT EQ: <4 x double> <double -1.0, double -2.0, double -4.0, double -8.0> = call <4 x double> @vec_neg()
