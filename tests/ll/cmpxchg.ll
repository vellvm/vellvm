;; Compare and swap when the values stored/compared are i32s
define i32 @cmpxchg_i32(i32 %x) {
   %ptr = alloca i32
   store i32 17, ptr %ptr
   %ans = cmpxchg ptr %ptr, i32 %x, i32 42 acq_rel monotonic
   %value_loaded = extractvalue { i32, i1 } %ans, 0
   %success = extractvalue { i32, i1 } %ans, 1   
   br i1 %success, label %true, label %false

true:
  %loaded_value = load i32, ptr %ptr
  ret i32 %loaded_value

false:
  %other_value = load i32, ptr %ptr
  ret i32 %other_value
}

;; Compare and swap when the values stored/compared are i64s
define i64 @cmpxchg_i64(i64 %x) {
   %ptr = alloca i64
   store i64 17, ptr %ptr
   %ans = cmpxchg ptr %ptr, i64 %x, i64 42 acq_rel monotonic
   %value_loaded = extractvalue { i64, i1 } %ans, 0
   %success = extractvalue { i64, i1 } %ans, 1   
   br i1 %success, label %true, label %false

true:
  %loaded_value = load i64, ptr %ptr
  ret i64 %loaded_value

false:
  %other_value = load i64, ptr %ptr
  ret i64 %other_value
}

;; Compare and swap when the values stored are pointers
define i32 @cmpxchg_ptr(i32 %x) {
   %ptr = alloca ptr
   %ptr_i = alloca i32
   %ptr_j = alloca i32
   
   store i32 %x, ptr %ptr_i
   store i32 17, ptr %ptr_j
   store ptr %ptr_i, ptr %ptr

   ;; if %x is 42 then the compare and swap succeeds
   %cmp = icmp eq i32 %x, 42
   br i1 %cmp, label %true, label %false

true:
   %ans = cmpxchg ptr %ptr, ptr %ptr_i, ptr %ptr_j acq_rel monotonic
   %value_loaded = extractvalue { ptr, i1 } %ans, 0
   %success = extractvalue { ptr, i1 } %ans, 1
   br i1 %success, label %load_success, label %load_fail

load_success:
   %ptr_loaded = load i32*, ptr %ptr
   %ans_s = load i32, ptr %ptr_loaded
   ret i32 %ans_s

false:
  %ans_f = cmpxchg ptr %ptr, ptr %ptr_j, ptr %ptr_i acq_rel monotonic
  %vl = extractvalue { ptr, i1 } %ans_f, 0
  %sl = extractvalue { ptr, i1 } %ans_f, 1
  br i1 %sl, label %load_success, label %load_fail

load_fail:
  ret i32 0
}



; ASSERT EQ: i32 42 = call i32 @cmpxchg_i32(i32 17)
; ASSERT EQ: i32 17 = call i32 @cmpxchg_i32(i32 55)

; ASSERT EQ: i64 42 = call i64 @cmpxchg_i64(i64 17)
; ASSERT EQ: i64 17 = call i64 @cmpxchg_i64(i64 55)

; ASSERT EQ: i32 0 = call i32 @cmpxchg_ptr(i32 17)
; ASSERT EQ: i32 17 = call i32 @cmpxchg_ptr(i32 42)
