; Examples from the LLVM LangRef's 'ptrtoaddr .. to' Instruction section.
; langref: ptrtoaddr-to-instruction sha1=1178151febc40f1c42e8951e6919964d7b327854
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = ptrtoaddr ptr addrspace(1) %P to i32              ; extracts low 32 bits of pointer
; %Y = ptrtoaddr <4 x ptr addrspace(1)> %P to <4 x i32>  ; yields vector of low 32 bits for each pointer

; LangRef's examples use addrspace(1); Vellvm models a single address space,
; so these use the default one. What ptrtoaddr yields is the address without
; the provenance, so an address taken from a live allocation is non-null and
; agrees with what ptrtoint gives for the same pointer.
define i1 @addr_is_nonnull() {
  %p = alloca i32
  %X = ptrtoaddr ptr %p to i64
  %r = icmp ne i64 %X, 0
  ret i1 %r
}

define i1 @agrees_with_ptrtoint() {
  %p = alloca i32
  %addr = ptrtoaddr ptr %p to i64
  %int = ptrtoint ptr %p to i64
  %r = icmp eq i64 %addr, %int
  ret i1 %r
}

; Truncating to a narrower integer extracts the low bits.
define i1 @low_bits() {
  %p = alloca i32
  %wide = ptrtoaddr ptr %p to i64
  %X = ptrtoaddr ptr %p to i32
  %low = trunc i64 %wide to i32
  %r = icmp eq i32 %X, %low
  ret i1 %r
}

; ASSERT EQ: i1 1 = call i1 @addr_is_nonnull()
; ASSERT EQ: i1 1 = call i1 @agrees_with_ptrtoint()
; ASSERT EQ: i1 1 = call i1 @low_bits()
