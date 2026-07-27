; Examples from the LLVM LangRef's 'alloca' Instruction section.
; langref: alloca-instruction sha1=a761d9afb43d8ec7f06a7cfa8d9d82f4196f598b
;
; LangRef 24.0.0git gives the following example(s):
;
; %ptr = alloca i32                             ; yields ptr
; %ptr = alloca i32, i32 4                      ; yields ptr
; %ptr = alloca i32, i32 4, align 1024          ; yields ptr
; %ptr = alloca i32, align 1024                 ; yields ptr

; %ptr = alloca i32
define i32 @alloca_plain() {
  %ptr = alloca i32
  store i32 3, ptr %ptr
  %val = load i32, ptr %ptr
  ret i32 %val
}

; %ptr = alloca i32, i32 4  -- room for four i32s
define i32 @alloca_array() {
  %ptr = alloca i32, i32 4
  %p2 = getelementptr i32, ptr %ptr, i32 2
  store i32 21, ptr %p2
  %val = load i32, ptr %p2
  ret i32 %val
}

; %ptr = alloca i32, i32 4, align 1024
define i32 @alloca_array_aligned() {
  %ptr = alloca i32, i32 4, align 1024
  store i32 9, ptr %ptr
  %val = load i32, ptr %ptr
  ret i32 %val
}

; %ptr = alloca i32, align 1024
define i32 @alloca_aligned() {
  %ptr = alloca i32, align 1024
  store i32 11, ptr %ptr
  %val = load i32, ptr %ptr
  ret i32 %val
}

; ASSERT EQ: i32 3 = call i32 @alloca_plain()
; ASSERT EQ: i32 21 = call i32 @alloca_array()
; ASSERT EQ: i32 9 = call i32 @alloca_array_aligned()
; ASSERT EQ: i32 11 = call i32 @alloca_aligned()
