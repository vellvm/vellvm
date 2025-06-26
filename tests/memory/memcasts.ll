define i32 @casts() {
  %arr_ptr = alloca [2 x i32], align 8
  %i64_ptr = bitcast [2 x i32]* %arr_ptr to i64*
  store i64 4294967303, i64* %i64_ptr   ; 0x0000000100000007
  %ind1 = getelementptr [2 x i32], [2 x i32]* %arr_ptr, i32 0, i32 0
  %ind2 = getelementptr [2 x i32], [2 x i32]* %arr_ptr, i32 0, i32 1
  %v1 = load i32, i32* %ind1            ; load value 7
  %v2 = load i32, i32* %ind2            ; load value 1
  %sum = add i32 %v1, %v2               ; sum = 8
  %iptr = ptrtoint i64* %i64_ptr to i64 ; cast to an integer
  %iptr2 = add i64 %iptr, 3             ; offset into bits
  %ptr = inttoptr i64 %iptr2 to i32*    ; cast back to pointer
  %v3 = load i32, i32* %ptr             ; load value 256, i.e. (1 >> 256)
  %sum2 = add i32 %sum, %v3             ; sum2 = 264
  ret i32 %sum2
}

define i32 @main(i64 %argc, i8** %arcv) {
  %1 = call i32 @casts()
  ret i32 %1
}
