define i64 @test() {
  add i64 5, 9
  add nsw i64 5, 9	
  add nuw i64 5, 9	
  add nuw nsw i64 5, 9
  add nsw nuw i64 5, 9	
  sub i64 5, 9
  sub nuw i64 5, 9
  sub nsw i64 5, 9  
  sub nuw nsw i64 5, 9
  sub nsw nuw i64 5, 9	
  mul i64 5, 9
  mul nsw i64 5, 9
  mul nuw i64 5, 9	
  mul nuw nsw i64 5, 9
  mul nsw nuw i64 5, 9	
  shl i64 5, 9
  shl nuw i64 5, 9	
  shl nsw i64 5, 9
  shl nsw nuw i64 5, 9	
  shl nuw nsw i64 5, 9
  ret i64 0
}

