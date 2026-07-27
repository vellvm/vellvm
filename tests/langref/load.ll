; Examples from the LLVM LangRef's 'load' Instruction section.
; langref: load-instruction sha1=d4a734206c9874fb15a4eb97ef8d89a06e836df9
;
; LangRef 24.0.0git gives the following example(s):
;
; %ptr = alloca i32                               ; yields ptr
; store i32 3, ptr %ptr                           ; yields void
; %val = load i32, ptr %ptr                       ; yields i32:val = i32 3

define i32 @store_then_load() {
  %ptr = alloca i32
  store i32 3, ptr %ptr
  %val = load i32, ptr %ptr
  ret i32 %val
}

; ASSERT EQ: i32 3 = call i32 @store_then_load()
