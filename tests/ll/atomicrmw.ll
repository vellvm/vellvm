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



;; Compare and swap when the values stored/compared are i5s
define i5 @atomicrmw_i5_nand(i5 %x, i5 %y) {
   %ptr = alloca i5
   store i5 %x, ptr %ptr
   %ans = atomicrmw nand ptr %ptr, i5 %y acq_rel
   %res = load i5, ptr %ptr
   ret i5 %res
}

; ASSERT EQ: i5 23 = call i5 @atomicrmw_i5_nand(i5 24, i5 11)
; ASSERT EQ: i5 22 = call i5 @atomicrmw_i5_nand(i5 15, i5 9)


;; Compare and swap when the values stored/compared are i8s
define i8 @atomicrmw_i8_nand(i8 %x, i8 %y) {
   %ptr = alloca i8
   store i8 %x, ptr %ptr
   %ans = atomicrmw nand ptr %ptr, i8 %y acq_rel
   %res = load i8, ptr %ptr
   ret i8 %res
}

; ASSERT EQ: i8 127 = call i8 @atomicrmw_i8_nand(i8 255, i8 128)

define i8 @atomicrmw_annotations(ptr %ptr) {
  %1 = atomicrmw sub ptr %ptr, i64 1 release, align 8, !noalias !5
  ret i8 0
}

; Two scope domains:
!0 = !{!0}
!1 = !{!1}

; Some scopes in these domains:
!2 = !{!2, !0}
!3 = !{!3, !0}
!4 = !{!4, !1}

; Some scope lists:
!5 = !{!4} ; A list containing only scope !4
