; Examples from the LLVM LangRef's 'select' Instruction section.
; langref: select-instruction sha1=700cecc06eed89b32c0f2fb48a3789f16beb0287
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = select i1 true, i8 17, i8 42                   ; yields i8:17
; %Y = select nnan i1 true, float 0.0, float NaN      ; yields float:0.0
; %Z = select nnan i1 false, float 0.0, float NaN     ; yields float:poison

define i8 @select_true() {
  %X = select i1 true, i8 17, i8 42
  ret i8 %X
}

define i8 @select_false() {
  %X = select i1 false, i8 17, i8 42
  ret i8 %X
}

; ASSERT EQ: i8 17 = call i8 @select_true()
; ASSERT EQ: i8 42 = call i8 @select_false()
