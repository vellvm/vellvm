define i32  @testExtractX() {
  %agg1 = insertvalue {i32, float} undef, i32 1, 0            
  %agg2 = insertvalue {i32, float} %agg1, float 10.0, 1
  %val = extractvalue {i32, float} %agg2, 0
  ret i32 %agg2
}

define float @testExtractY() {
  %agg1 = insertvalue {i32, float} undef, i32 1, 0            
  %agg2 = insertvalue {i32, float} %agg1, float 20.0, 1
  %val = extractvalue {i32, float} %agg2, 1
  ret float %agg2
}

; ASSERT EQ: i32 1 = call i32 @testExtractX()

; ASSERT EQ: float 20.0 = call float @testExtractY()
