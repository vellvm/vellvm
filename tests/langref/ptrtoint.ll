; Examples from the LLVM LangRef's 'ptrtoint .. to' Instruction section.
; langref: ptrtoint-to-instruction sha1=c9965d799a7e722d4f6a7dd4ee3f99ec70be24f8
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = ptrtoint ptr %P to i8                         ; yields truncation on 32-bit architecture
; %Y = ptrtoint ptr %P to i64                        ; yields zero extension on 32-bit architecture
; %Z = ptrtoint <4 x ptr> %P to <4 x i64>; yields vector zero extension for a vector of addresses on 32-bit architecture

; LangRef's examples are about widening and truncation relative to the
; pointer width; what is stable across targets is the round trip.
define i32 @roundtrip_i64() {
  %ptr = alloca i32
  store i32 5, ptr %ptr
  %Y = ptrtoint ptr %ptr to i64
  %back = inttoptr i64 %Y to ptr
  %r = load i32, ptr %back
  ret i32 %r
}

; Truncating to a narrower integer keeps the low bits.
define i8 @truncating(i8 %unused) {
  %ptr = alloca i32
  %wide = ptrtoint ptr %ptr to i64
  %X = ptrtoint ptr %ptr to i8
  %low = trunc i64 %wide to i8
  %eq = icmp eq i8 %X, %low
  %r = zext i1 %eq to i8
  ret i8 %r
}

; ASSERT EQ: i32 5 = call i32 @roundtrip_i64()
; ASSERT EQ: i8 1 = call i8 @truncating(i8 0)
