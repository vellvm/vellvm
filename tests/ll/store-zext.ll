; Stores and loads of integers whose width is not a whole number of bytes.
;
; LangRef ('store'): "When writing a value of a type like i20 with a size
; that is not an integral number of bytes, the value will be zero extended
; to the next larger multiple of the byte size (here i24) and then stored.
; As such, a non-byte-sized store behaves like a zext followed by a
; byte-sized store."  It also writes no more bytes than the type needs.
;
; Vellvm used to pad the last byte with poison instead, so reading it back
; at a wider type gave poison.  And its reader for non-byte-sized loads
; accepted only such a padded last byte, so loading i4 from memory written
; by an i8 store failed outright.

; the padding bits are zeros
define i64 @store_i4_load_i8() {
  %p = alloca i8
  store i4 5, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

; zero extension, not sign extension: i4 -1 is 0b1111, so the byte is 15
define i64 @store_i4_negative_load_i8() {
  %p = alloca i8
  store i4 -1, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

define i64 @store_i1_load_i8() {
  %p = alloca i8
  store i1 true, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

; i7 -1 is 0x7f: the top bit of the byte is the zero padding
define i64 @store_i7_load_i8() {
  %p = alloca i8
  store i7 -1, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

; a multi-byte value: i12 0xfff over a slot of 0xffff leaves 0x0fff -- the
; high nibble of the second byte is zeroed
define i64 @store_i12_over_ones() {
  %p = alloca i16
  store i16 -1, ptr %p
  store i12 -1, ptr %p
  %v = load i16, ptr %p
  %r = zext i16 %v to i64
  ret i64 %r
}

; an i20 store writes three bytes and no more: the fourth byte of the slot
; keeps its 0xff, and the third holds the top nibble 0xa zero-extended
define i64 @store_i20_writes_three_bytes() {
  %p = alloca i32
  store i32 -1, ptr %p
  store i20 703710, ptr %p              ; 0xabcde
  %v = load i32, ptr %p                 ; 0xff0abcde
  %r = zext i32 %v to i64
  ret i64 %r
}

; the other direction: a non-byte-sized load of bytes written at a wider
; type takes just the low bits
define i64 @store_i8_load_i4() {
  %p = alloca i8
  store i8 245, ptr %p                  ; 0xf5
  %v = load i4, ptr %p                  ; 0x5
  %r = zext i4 %v to i64
  ret i64 %r
}

define i64 @store_i16_load_i12() {
  %p = alloca i16
  store i16 4660, ptr %p                ; 0x1234
  %v = load i12, ptr %p                 ; 0x234
  %r = zext i12 %v to i64
  ret i64 %r
}

; a round trip at the odd width itself
define i64 @store_i20_load_i20() {
  %p = alloca i32
  store i20 703710, ptr %p
  %v = load i20, ptr %p
  %r = zext i20 %v to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_store_i4_load_i8 = private unnamed_addr constant [27 x i8] c"store_i4_load_i8() = %lld\0A\00"
@fmt_store_i4_negative_load_i8 = private unnamed_addr constant [36 x i8] c"store_i4_negative_load_i8() = %lld\0A\00"
@fmt_store_i1_load_i8 = private unnamed_addr constant [27 x i8] c"store_i1_load_i8() = %lld\0A\00"
@fmt_store_i7_load_i8 = private unnamed_addr constant [27 x i8] c"store_i7_load_i8() = %lld\0A\00"
@fmt_store_i12_over_ones = private unnamed_addr constant [30 x i8] c"store_i12_over_ones() = %lld\0A\00"
@fmt_store_i20_writes_three_bytes = private unnamed_addr constant [39 x i8] c"store_i20_writes_three_bytes() = %lld\0A\00"
@fmt_store_i8_load_i4 = private unnamed_addr constant [27 x i8] c"store_i8_load_i4() = %lld\0A\00"
@fmt_store_i16_load_i12 = private unnamed_addr constant [29 x i8] c"store_i16_load_i12() = %lld\0A\00"
@fmt_store_i20_load_i20 = private unnamed_addr constant [29 x i8] c"store_i20_load_i20() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @store_i4_load_i8()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_store_i4_load_i8, i64 %v0)
  %v1 = call i64 @store_i4_negative_load_i8()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_store_i4_negative_load_i8, i64 %v1)
  %v2 = call i64 @store_i1_load_i8()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_store_i1_load_i8, i64 %v2)
  %v3 = call i64 @store_i7_load_i8()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_store_i7_load_i8, i64 %v3)
  %v4 = call i64 @store_i12_over_ones()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_store_i12_over_ones, i64 %v4)
  %v5 = call i64 @store_i20_writes_three_bytes()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_store_i20_writes_three_bytes, i64 %v5)
  %v6 = call i64 @store_i8_load_i4()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_store_i8_load_i4, i64 %v6)
  %v7 = call i64 @store_i16_load_i12()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_store_i16_load_i12, i64 %v7)
  %v8 = call i64 @store_i20_load_i20()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_store_i20_load_i20, i64 %v8)
  ret i32 0
}

; ASSERT EQ: i64 5          = call i64 @store_i4_load_i8()
; ASSERT EQ: i64 15         = call i64 @store_i4_negative_load_i8()
; ASSERT EQ: i64 1          = call i64 @store_i1_load_i8()
; ASSERT EQ: i64 127        = call i64 @store_i7_load_i8()
; ASSERT EQ: i64 4095       = call i64 @store_i12_over_ones()
; ASSERT EQ: i64 4278893790 = call i64 @store_i20_writes_three_bytes()
; ASSERT EQ: i64 5          = call i64 @store_i8_load_i4()
; ASSERT EQ: i64 564        = call i64 @store_i16_load_i12()
; ASSERT EQ: i64 703710     = call i64 @store_i20_load_i20()
