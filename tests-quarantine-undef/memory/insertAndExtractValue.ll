define i32  @testExtractX() {
  %agg1 = insertvalue {i32, float} undef, i32 1, 0            
  %agg2 = insertvalue {i32, float} %agg1, float 10.0, 1
  %val = extractvalue {i32, float} %agg2, 0
  ret i32 %val
}

define float @testExtractY() {
  %agg1 = insertvalue {i32, float} undef, i32 1, 0            
  %agg2 = insertvalue {i32, float} %agg1, float 20.0, 1
  %val = extractvalue {i32, float} %agg2, 1
  ret float %val
}

define i32 @testValuesChange() {
  %ptr = alloca [4 x i32]
  store [4 x i32] [i32 10, i32 20, i32 30, i32 40], [4 x i32]* %ptr
  %agg1 = load [4 x i32], [4 x i32]* %ptr
  %agg2 = insertvalue [4 x i32] %agg1, i32 100, 1
  %val = extractvalue [4 x i32] %agg2, 1
  ret i32 %val
}

define i32 @testChangeDifferentLocation() {
  %ptr = alloca [4 x i32]
  store [4 x i32] [i32 10, i32 20, i32 30, i32 40], [4 x i32]* %ptr
  %agg1 = load [4 x i32], [4 x i32]* %ptr        
  %agg2 = insertvalue [4 x i32] %agg1, i32 100, 1
  %val = extractvalue [4 x i32] %agg2, 3
  ret i32 %val
}

define i32 @testSingletonArray() {
  %ptr = alloca [4 x i32]
  store [4 x i32] [i32 10, i32 20, i32 30, i32 40], [4 x i32]* %ptr
  %agg1 = load [4 x i32], [4 x i32]* %ptr
  %agg2 = insertvalue [4 x i32] %agg1, i32 60, 0
  %val = extractvalue [4 x i32] %agg2, 0
  ret i32 %val
}

; ASSERT EQ: i32 1 = call i32 @testExtractX()

; ASSERT EQ: float 20.0 = call float @testExtractY()

; ASSERT EQ: i32 100 = call i32 @testValuesChange()

; ASSERT EQ: i32 40 = call i32 @testChangeDifferentLocation()

; ASSERT EQ: i32 60 = call i32 @testSingletonArray() 
