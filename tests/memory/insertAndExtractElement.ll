declare void @print_int(i64 %x)

define i64 @main(i64 %location, i64 %val, i64 %removeLoc) {
  %loc = add i64 0, 0
  %value = add i64 0, 2
  %removeLocation = add i64 0, 0
  call void @print_int(i64 %loc)
  call void @print_int(i64 %value)
  call void @print_int(i64 %removeLocation)
  %vec = add <4 x i64> <i64 5, i64 10, i64 15, i64 20>, zeroinitializer
  %result = insertelement <4 x i64> %vec, i64 %value, i64 %loc
  %returnVal = extractelement <4 x i64> %result, i64 %removeLocation
  call void @print_int(i64 %returnVal)
  ret i64 %returnVal
}

define i64 @insertAndRemove(i64 %location, i64 %val, i64 %removeLoc) {
  %vec = add <4 x i64> <i64 5, i64 10, i64 15, i64 20>, zeroinitializer
  %result = insertelement <4 x i64> %vec, i64 %val, i64 %location
  %returnVal = extractelement <4 x i64> %result, i64 %removeLoc
  call void @print_int(i64 %returnVal)
  ret i64 %returnVal
}

; ASSERT EQ: i64 2 = call i64 @insertAndRemove(i64 0, i64 2, i64 0)
; ASSERT EQ: i64 10 = call i64 @insertAndRemove(i64 0, i64 2, i64 1)
; ASSERT EQ: i64 15 = call i64 @insertAndRemove(i64 0, i64 2, i64 2)
; ASSERT EQ: i64 20 = call i64 @insertAndRemove(i64 0, i64 2, i64 3)

; ASSERT EQ: i64 5 = call i64 @insertAndRemove(i64 1, i64 2, i64 0)
; ASSERT EQ: i64 2 = call i64 @insertAndRemove(i64 1, i64 2, i64 1)
; ASSERT EQ: i64 15 = call i64 @insertAndRemove(i64 1, i64 2, i64 2)
; ASSERT EQ: i64 20 = call i64 @insertAndRemove(i64 1, i64 2, i64 3)

; ASSERT EQ: i64 5 = call i64 @insertAndRemove(i64 2, i64 2, i64 0)
; ASSERT EQ: i64 10 = call i64 @insertAndRemove(i64 2, i64 2, i64 1)
; ASSERT EQ: i64 2 = call i64 @insertAndRemove(i64 2, i64 2, i64 2)
; ASSERT EQ: i64 20 = call i64 @insertAndRemove(i64 2, i64 2, i64 3)

; ASSERT EQ: i64 5 = call i64 @insertAndRemove(i64 3, i64 2, i64 0)
; ASSERT EQ: i64 10 = call i64 @insertAndRemove(i64 3, i64 2, i64 1)
; ASSERT EQ: i64 15 = call i64 @insertAndRemove(i64 3, i64 2, i64 2)
; ASSERT EQ: i64 2 = call i64 @insertAndRemove(i64 3, i64 2, i64 3)




