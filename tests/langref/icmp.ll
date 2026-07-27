; Examples from the LLVM LangRef's 'icmp' Instruction section.
; langref: icmp-instruction sha1=58b940bb0cb275e0b262267b556648c608566088
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = icmp eq i32 4, 5          ; yields: result=false
; <result> = icmp ne ptr %X, %X        ; yields: result=false
; <result> = icmp ult i16  4, 5        ; yields: result=true
; <result> = icmp sgt i16  4, 5        ; yields: result=false
; <result> = icmp ule i16 -4, 5        ; yields: result=false
; <result> = icmp sge i16  4, 5        ; yields: result=false

define i1 @icmp_eq_4_5() {
  %r = icmp eq i32 4, 5
  ret i1 %r
}

define i1 @icmp_ne_self(ptr %X) {
  %r = icmp ne ptr %X, %X
  ret i1 %r
}

define i1 @icmp_ult_4_5() {
  %r = icmp ult i16 4, 5
  ret i1 %r
}

define i1 @icmp_sgt_4_5() {
  %r = icmp sgt i16 4, 5
  ret i1 %r
}

; Unsigned comparison: -4 is 65532, which is not <= 5.
define i1 @icmp_ule_m4_5() {
  %r = icmp ule i16 -4, 5
  ret i1 %r
}

define i1 @icmp_sge_4_5() {
  %r = icmp sge i16 4, 5
  ret i1 %r
}

; ASSERT EQ: i1 0 = call i1 @icmp_eq_4_5()
; ASSERT EQ: i1 0 = call i1 @icmp_ne_self(ptr null)
; ASSERT EQ: i1 1 = call i1 @icmp_ult_4_5()
; ASSERT EQ: i1 0 = call i1 @icmp_sgt_4_5()
; ASSERT EQ: i1 0 = call i1 @icmp_ule_m4_5()
; ASSERT EQ: i1 0 = call i1 @icmp_sge_4_5()
