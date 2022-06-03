define i32 @test32bit(i32 %value) {
  %ptr = alloca i32
  store i32 %value, i32* %ptr                          
  %val = load i32, i32* %ptr
  ret i32 %val
}

define i64 @test64bit(i64 %value) {
  %ptr = alloca i64
  store i64 %value, i64* %ptr                          
  %val = load i64, i64* %ptr
  ret i64 %val
}

define float @testfloat(float %value) {
  %ptr = alloca float
  store float %value, float* %ptr                          
  %val = load float, float* %ptr
  ret float %val
}

define double @testdouble(double %value) {
  %ptr = alloca double
  store double %value, double* %ptr                          
  %val = load double, double* %ptr
  ret double %val
}

define [4 x i32] @testAlloca() {
  ;;;; %ptr = alloca i32, i32 4 ;;;; not sure if this syntax is correct, but if it is it does not work.
  %ptr = alloca [4 x i32]
  store [4 x i32] [i32 0, i32 1, i32 2, i32 3], [4 x i32]* %ptr
  %val = load [4 x i32], [4 x i32]* %ptr
  ret [4 x i32] %val
}

; ASSERT EQ: i32 15 = call i32 @test32bit(i32 15)
; ASSERT EQ: i32 0 = call i32 @test32bit(i32 0)
; ASSERT EQ: i32 255 = call i32 @test32bit(i32 255)
; ASSERT EQ: i32 25500 = call i32 @test32bit(i32 25500)
; ASSERT EQ: i32 2550000 = call i32 @test32bit(i32 2550000)

; ASSERT EQ: i64 15 = call i64 @test64bit(i64 15)
; ASSERT EQ: i64 0 = call i64 @test64bit(i64 0)
; ASSERT EQ: i64 255 = call i64 @test64bit(i64 255)
; ASSERT EQ: i64 25500 = call i64 @test64bit(i64 25500)
; ASSERT EQ: i64 2550000 = call i64 @test64bit(i64 2550000)

; ASSERT EQ: float 15.0 = call float @testfloat(float 15.0)
; ASSERT EQ: float 0.0 = call float @testfloat(float 0.0)
; ASSERT EQ: float 255.0 = call float @testfloat(float 255.0)
; ASSERT EQ: float 25500.0 = call float @testfloat(float 25500.0)
; ASSERT EQ: float 2550000.0 = call float @testfloat(float 2550000.0)

; ASSERT EQ: float 15.5 = call float @testfloat(float 15.5)
; ASSERT EQ: float 0.25 = call float @testfloat(float 0.25)
; ASSERT EQ: float 255.125 = call float @testfloat(float 255.125)
; ASSERT EQ: float 25500.0625 = call float @testfloat(float 25500.0625)
; ASSERT EQ: float 25500.03125 = call float @testfloat(float 25500.03125)

;;;; ASSERT EQ: float 0.33 = call float @testfloat(float 0.33)
;;;; ASSERT EQ: float 255.294 = call float @testfloat(float 255.294)
;;;; ASSERT EQ: float 25500.798 = call float @testfloat(float 25500.798)
;;;; ASSERT EQ: float 255.12345 = call float @testfloat(float 255.12345)

; ASSERT EQ: double 15.0 = call double @testdouble(double 15.0)
; ASSERT EQ: double 0.0 = call double @testdouble(double 0.0)
; ASSERT EQ: double 255.0 = call double @testdouble(double 255.0)
; ASSERT EQ: double 25500.0 = call double @testdouble(double 25500.0)
; ASSERT EQ: double 2550000.0 = call double @testdouble(double 2550000.0)

; ASSERT EQ: double 15.5 = call double @testdouble(double 15.5)
; ASSERT EQ: double 0.25 = call double @testdouble(double 0.25)
; ASSERT EQ: double 255.125 = call double @testdouble(double 255.125)
; ASSERT EQ: double 25500.0625 = call double @testdouble(double 25500.0625)
; ASSERT EQ: double 25500.03125 = call double @testdouble(double 25500.03125)

; ASSERT EQ: double 0.33 = call double @testdouble(double 0.33)
; ASSERT EQ: double 255.294 = call double @testdouble(double 255.294)
; ASSERT EQ: double 25500.798 = call double @testdouble(double 25500.798)
; ASSERT EQ: double 255.12345 = call double @testdouble(double 255.12345)

; ASSERT EQ: [4 x i32] [i32 0, i32 1, i32 2, i32 3] = call [4 x i32] @testAlloca()
