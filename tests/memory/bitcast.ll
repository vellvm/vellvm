define i8 @testi8toi8(i8 %val) {
  %returnVal = bitcast i8 %val to i8
  ret i8 %returnVal
}

define i32 @testi32toi32(i32 %val) {
  %returnVal = bitcast i32 %val to i32
  ret i32 %returnVal
}

define double @testdoubletodouble(double %val) {
  %returnVal = bitcast double %val to double
  ret double %returnVal
}

define float @testi32tofloat(i32 %val) {
  %returnVal = bitcast i32 %val to float
  ret float %returnVal
}

define i32 @testfloattoi32(float %val) {
  %returnVal = bitcast float %val to i32
  ret i32 %returnVal
}

define i32 @testPointerCast(i32 %val) {
  %ptr = inttoptr i32 %val to i32*
  %newptr = bitcast i32* %ptr to i64*
  %returnVal = ptrtoint i64* %newptr to i32
  ret i32 %returnVal
}

define i64 @testVectorToi64(<2 x i32> %V) {
  %u = add <2 x i32> <i32 0, i32 0>, zeroinitializer
  %returnVal = bitcast <2 x i32> %u to i64
  ret i64 %returnVal
}

define i32 @main(i32 %argc, i8** %argv) {
  %v = call i8 @testi8toi8(i8 255)
  %ans = sext i8 %v to i32
  ret i32 %ans
}


; ASSERT EQ: i8 255 = call i8 @testi8toi8(i8 255)
; ASSERT EQ: i8 -1 = call i8 @testi8toi8(i8 -1)
; ASSERT EQ: i8 25 = call i8 @testi8toi8(i8 25)

; ASSERT EQ: i32 2550 = call i32 @testi32toi32(i32 2550)
; ASSERT EQ: i32 7 = call i32 @testi32toi32(i32 7)

; ASSERT EQ: float 0.0 = call float @testi32tofloat(i32 0)

; ASSERT EQ: i32 0 = call i32 @testfloattoi32(float 0.0)

; ASSERT EQ: i32 0 = call i32 @testPointerCast(i32 0)

; ASSERT EQ: i64 0 = call i64 @testVectorToi64()

