define i8 @to_i8(double %f) {
  %ans = fptosi double %f to i8
  ret i8 %ans
}   

; ASSERT EQ: i8 poison = call i8 @to_i8(double 1.0E+300)
; ASSERT EQ: i8 poison = call i8 @to_i8(double 1.04E+17)
; ASSERT EQ: i8 123 = call i8 @to_i8(double 123.0)
; ASSERT EQ: i8 123 = call i8 @to_i8(double 123.1)
; ASSERT EQ: i8 122 = call i8 @to_i8(double 122.9)
; ASSERT EQ: i8 -123 = call i8 @to_i8(double -123.0)
; ASSERT EQ: i8 -123 = call i8 @to_i8(double -123.1)
; ASSERT EQ: i8 -122 = call i8 @to_i8(double -122.9)
; ASSERT EQ: i8 0 = call i8 @to_i8(double -0.0)
; ASSERT EQ: i8 0 = call i8 @to_i8(double 0.0)
; ASSERT EQ: i8 -1 = call i8 @to_i8(double -1.2)



define i1 @to_i1(double %f) {
  %Z = fptosi double %f to i1 
  ret i1 %Z
}

; ASSERT EQ: i1 poison = call i1 @to_i1(double 1.0E+300)
; ASSERT EQ: i1 poison = call i1 @to_i1(double 1.04E+17)
; ASSERT EQ: i1 0 = call i1 @to_i1(double 0.0)
; ASSERT EQ: i1 0 = call i1 @to_i1(double 0.75)
; ASSERT EQ: i1 poison = call i1 @to_i1(double 1.0)
; ASSERT EQ: i1 -1 = call i1 @to_i1(double -1.0)
; ASSERT EQ: i1 -1 = call i1 @to_i1(double -1.1)
; ASSERT EQ: i1 0 = call i1 @to_i1(double -0.5)
