;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_add(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw add ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 42 = call i32 @atomicrmw_i32_add(i32 17, i32 25)
; ASSERT EQ: i32 100 = call i32 @atomicrmw_i32_add(i32 10, i32 90)


;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_sub(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw sub ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 8 = call i32 @atomicrmw_i32_sub(i32 25, i32 17)
; ASSERT EQ: i32 80 = call i32 @atomicrmw_i32_sub(i32 90, i32 10)


;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_xchg(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw xchg ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 17 = call i32 @atomicrmw_i32_xchg(i32 25, i32 17)
; ASSERT EQ: i32 10 = call i32 @atomicrmw_i32_xchg(i32 90, i32 10)


;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_and(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw and ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 17 = call i32 @atomicrmw_i32_and(i32 25, i32 17)
; ASSERT EQ: i32 16 = call i32 @atomicrmw_i32_and(i32 25, i32 16)


;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_or(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw or ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 27 = call i32 @atomicrmw_i32_or(i32 24, i32 11)
; ASSERT EQ: i32 25 = call i32 @atomicrmw_i32_or(i32 25, i32 16)

;; Compare and swap when the values stored/compared are i32s
define i32 @atomicrmw_i32_xor(i32 %x, i32 %y) {
   %ptr = alloca i32
   store i32 %x, ptr %ptr
   %ans = atomicrmw xor ptr %ptr, i32 %y acq_rel
   %res = load i32, ptr %ptr
   ret i32 %res
}

; ASSERT EQ: i32 19 = call i32 @atomicrmw_i32_xor(i32 24, i32 11)
; ASSERT EQ: i32 9 = call i32 @atomicrmw_i32_xor(i32 25, i32 16)


