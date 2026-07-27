; Examples from the LLVM LangRef's 'trunc .. to' Instruction section.
; langref: trunc-to-instruction sha1=79b9cb52a0ccb148ef5eed3f2cb404d5f3af2371
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = trunc i32 257 to i8                        ; yields i8:1
; %Y = trunc i32 123 to i1                        ; yields i1:true
; %Z = trunc i32 122 to i1                        ; yields i1:false
; %W = trunc <2 x i16> <i16 8, i16 7> to <2 x i8> ; yields <i8 8, i8 7>

define i8 @trunc_257() {
  %X = trunc i32 257 to i8
  ret i8 %X
}

define i1 @trunc_123() {
  %Y = trunc i32 123 to i1
  ret i1 %Y
}

define i1 @trunc_122() {
  %Z = trunc i32 122 to i1
  ret i1 %Z
}

define <2 x i8> @trunc_vec() {
  %W = trunc <2 x i16> <i16 8, i16 7> to <2 x i8>
  ret <2 x i8> %W
}

; ASSERT EQ: i8 1 = call i8 @trunc_257()
; ASSERT EQ: i1 1 = call i1 @trunc_123()
; ASSERT EQ: i1 0 = call i1 @trunc_122()
; ASSERT EQ: <2 x i8> <i8 8, i8 7> = call <2 x i8> @trunc_vec()
