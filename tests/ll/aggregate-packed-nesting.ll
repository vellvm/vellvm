; An *unpacked* aggregate nested inside a *packed* one.
;
; A packed struct does not align its field offsets, so a nested unpacked
; struct can start at an offset that is not a multiple of its alignment.
; Its internal padding is nevertheless relative to its own start, not to the
; enclosing offset. The serializer used to compute field padding from the
; absolute offset, which inserted 3 spurious bytes before the inner struct's
; first i32 here: %pk came out 12 bytes instead of 9, disagreeing with
; getelementptr, with the loader, and with clang.

%inner = type { i32, i32 }
%pk    = type <{ i8, %inner }>
%pkarr = type <{ i8, [2 x %inner] }>

; --- sizes and offsets (these exercise getelementptr) ---
define i64 @size_pk() {
  %p = alloca %pk
  %f = getelementptr %pk, ptr %p, i32 1
  %a = ptrtoint ptr %p to i64
  %b = ptrtoint ptr %f to i64
  %d = sub i64 %b, %a
  ret i64 %d
}

define i64 @offset_pk_inner() {
  %p = alloca %pk
  %f = getelementptr %pk, ptr %p, i32 0, i32 1
  %a = ptrtoint ptr %p to i64
  %b = ptrtoint ptr %f to i64
  %d = sub i64 %b, %a
  ret i64 %d
}

define i64 @size_pkarr() {
  %p = alloca %pkarr
  %f = getelementptr %pkarr, ptr %p, i32 1
  %a = ptrtoint ptr %p to i64
  %b = ptrtoint ptr %f to i64
  %d = sub i64 %b, %a
  ret i64 %d
}

; --- store/load round trip (this exercises the serializer) ---
; If the writer pads the inner struct against the enclosing offset while the
; reader does not, these come back wrong.
define i64 @roundtrip_inner_first() {
  %s = alloca %pk
  %v0 = insertvalue %pk zeroinitializer, i8 1, 0
  %v1 = insertvalue %pk %v0, i32 22, 1, 0
  %v2 = insertvalue %pk %v1, i32 33, 1, 1
  store %pk %v2, %pk* %s
  %r = load %pk, %pk* %s
  %x = extractvalue %pk %r, 1, 0
  %w = zext i32 %x to i64
  ret i64 %w
}

define i64 @roundtrip_inner_second() {
  %s = alloca %pk
  %v0 = insertvalue %pk zeroinitializer, i8 1, 0
  %v1 = insertvalue %pk %v0, i32 22, 1, 0
  %v2 = insertvalue %pk %v1, i32 33, 1, 1
  store %pk %v2, %pk* %s
  %r = load %pk, %pk* %s
  %x = extractvalue %pk %r, 1, 1
  %w = zext i32 %x to i64
  ret i64 %w
}

; --- the store and getelementptr must agree on where the inner field lives ---
define i64 @gep_agrees_in_packed() {
  %s = alloca %pk
  %v0 = insertvalue %pk zeroinitializer, i8 1, 0
  %v1 = insertvalue %pk %v0, i32 44, 1, 0
  store %pk %v1, %pk* %s
  %p = getelementptr %pk, %pk* %s, i64 0, i32 1, i32 0
  %x = load i32, i32* %p
  %w = zext i32 %x to i64
  ret i64 %w
}

@f1 = private unnamed_addr constant [18 x i8] c"size_pk() = %lld\0A\00"
@f2 = private unnamed_addr constant [26 x i8] c"offset_pk_inner() = %lld\0A\00"
@f3 = private unnamed_addr constant [21 x i8] c"size_pkarr() = %lld\0A\00"
@f4 = private unnamed_addr constant [32 x i8] c"roundtrip_inner_first() = %lld\0A\00"
@f5 = private unnamed_addr constant [33 x i8] c"roundtrip_inner_second() = %lld\0A\00"
@f6 = private unnamed_addr constant [31 x i8] c"gep_agrees_in_packed() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v1 = call i64 @size_pk()
  %p1 = call i32 (ptr, ...) @printf(ptr @f1, i64 %v1)
  %v2 = call i64 @offset_pk_inner()
  %p2 = call i32 (ptr, ...) @printf(ptr @f2, i64 %v2)
  %v3 = call i64 @size_pkarr()
  %p3 = call i32 (ptr, ...) @printf(ptr @f3, i64 %v3)
  %v4 = call i64 @roundtrip_inner_first()
  %p4 = call i32 (ptr, ...) @printf(ptr @f4, i64 %v4)
  %v5 = call i64 @roundtrip_inner_second()
  %p5 = call i32 (ptr, ...) @printf(ptr @f5, i64 %v5)
  %v6 = call i64 @gep_agrees_in_packed()
  %p6 = call i32 (ptr, ...) @printf(ptr @f6, i64 %v6)
  ret i32 0
}

; ASSERT EQ: i64 9  = call i64 @size_pk()
; ASSERT EQ: i64 1  = call i64 @offset_pk_inner()
; ASSERT EQ: i64 17 = call i64 @size_pkarr()
; ASSERT EQ: i64 22 = call i64 @roundtrip_inner_first()
; ASSERT EQ: i64 33 = call i64 @roundtrip_inner_second()
; ASSERT EQ: i64 44 = call i64 @gep_agrees_in_packed()
