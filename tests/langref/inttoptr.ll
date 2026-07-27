; Examples from the LLVM LangRef's 'inttoptr .. to' Instruction section.
; langref: inttoptr-to-instruction sha1=a091f399840f4dcb1e9e7a61c7d3bcfcab2201f9
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = inttoptr i32 255 to ptr           ; yields zero extension on 64-bit architecture
; %Y = inttoptr i32 255 to ptr           ; yields no-op on 32-bit architecture
; %Z = inttoptr i64 0 to ptr             ; yields truncation on 32-bit architecture
; %Z = inttoptr <4 x i32> %G to <4 x ptr>; yields truncation of vector G to four pointers

; The round trip through an integer of pointer width preserves the pointer.
define i32 @roundtrip() {
  %ptr = alloca i32
  store i32 12, ptr %ptr
  %i = ptrtoint ptr %ptr to i64
  %X = inttoptr i64 %i to ptr
  %r = load i32, ptr %X
  ret i32 %r
}

; %Z = inttoptr i64 0 to ptr
define i1 @inttoptr_zero() {
  %Z = inttoptr i64 0 to ptr
  %r = icmp eq ptr %Z, null
  ret i1 %r
}

; ASSERT EQ: i32 12 = call i32 @roundtrip()
; ASSERT EQ: i1 1 = call i1 @inttoptr_zero()
