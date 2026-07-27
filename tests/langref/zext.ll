; Examples from the LLVM LangRef's 'zext .. to' Instruction section.
; langref: zext-to-instruction sha1=84bd3ad1d4f33561254e5e615535a89ba01bac6a
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = zext i32 257 to i64              ; yields i64:257
; %Y = zext i1 true to i32              ; yields i32:1
; %Z = zext <2 x i16> <i16 8, i16 7> to <2 x i32> ; yields <i32 8, i32 7>
;
; %a = zext nneg i8 127 to i16 ; yields i16 127
; %b = zext nneg i8 -1 to i16  ; yields i16 poison

define i64 @zext_257() {
  %X = zext i32 257 to i64
  ret i64 %X
}

define i32 @zext_true() {
  %Y = zext i1 true to i32
  ret i32 %Y
}

define <2 x i32> @zext_vec() {
  %Z = zext <2 x i16> <i16 8, i16 7> to <2 x i32>
  ret <2 x i32> %Z
}

; ASSERT EQ: i64 257 = call i64 @zext_257()
; ASSERT EQ: i32 1 = call i32 @zext_true()
; ASSERT EQ: <2 x i32> <i32 8, i32 7> = call <2 x i32> @zext_vec()
