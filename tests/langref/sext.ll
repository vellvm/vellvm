; Examples from the LLVM LangRef's 'sext .. to' Instruction section.
; langref: sext-to-instruction sha1=4837d52be2e4814a6162f881fa8628831a98c8b3
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = sext i8  -1 to i16              ; yields i16   :65535
; %Y = sext i1 true to i32             ; yields i32:-1
; %Z = sext <2 x i16> <i16 8, i16 7> to <2 x i32> ; yields <i32 8, i32 7>

; LangRef writes the result as i16 65535, which is -1.
define i16 @sext_m1() {
  %X = sext i8 -1 to i16
  ret i16 %X
}

; sext of i1 true is all-ones, i.e. -1, not 1.
define i32 @sext_true() {
  %Y = sext i1 true to i32
  ret i32 %Y
}

define <2 x i32> @sext_vec() {
  %Z = sext <2 x i16> <i16 8, i16 7> to <2 x i32>
  ret <2 x i32> %Z
}

; ASSERT EQ: i16 -1 = call i16 @sext_m1()
; ASSERT EQ: i32 -1 = call i32 @sext_true()
; ASSERT EQ: <2 x i32> <i32 8, i32 7> = call <2 x i32> @sext_vec()
