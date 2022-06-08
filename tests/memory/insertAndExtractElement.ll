define i64 @insertAndRemove(i64 %location, i64 %val, i64 %removeLoc) {
  %ptr = alloca <4 x i64>
  store <4 x i64> <i64 5, i64 10, i64 15, i64 20>, <4 x i64>* %ptr
  %vec = load <4 x i64>, <4 x i64>* %ptr
  %result = insertelement <4 x i64> %vec, i64 %val, i64 %location
  %returnVal = extractelement <4 x i64> %result, i64 %removeLoc
  ret i64 %returnVal
}

define i64 @main() {
  %retVal = call i64 @insertAndRemove(i64 0, i64 2, i64 0)
  ret i64 %retVal
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

