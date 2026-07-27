; Examples from the LLVM LangRef's 'xor' Instruction section.
; langref: xor-instruction sha1=c6ee27985ad3fd4a9d3df32fc00070ec625f54b6
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = xor i32 4, %var         ; yields i32:result = 4 ^ %var
; <result> = xor i32 15, 40          ; yields i32:result = 39
; <result> = xor i32 4, 8            ; yields i32:result = 12
; <result> = xor i32 %V, -1          ; yields i32:result = ~%V

define i32 @xor_4(i32 %var) {
  %r = xor i32 4, %var
  ret i32 %r
}

define i32 @xor_15_40() {
  %r = xor i32 15, 40
  ret i32 %r
}

define i32 @xor_4_8() {
  %r = xor i32 4, 8
  ret i32 %r
}

; The idiomatic bitwise complement.
define i32 @complement(i32 %V) {
  %r = xor i32 %V, -1
  ret i32 %r
}

; ASSERT EQ: i32 5 = call i32 @xor_4(i32 1)
; ASSERT EQ: i32 0 = call i32 @xor_4(i32 4)
; ASSERT EQ: i32 39 = call i32 @xor_15_40()
; ASSERT EQ: i32 12 = call i32 @xor_4_8()
; ASSERT EQ: i32 -1 = call i32 @complement(i32 0)
; ASSERT EQ: i32 -6 = call i32 @complement(i32 5)
