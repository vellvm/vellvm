; bitcast and memory layout of vectors whose elements are not byte-sized
; (<N x i1>, <N x i2>, <N x i4>, <N x i12>, ...).  See vellvm issue #273.
;
; LangRef (vector type): "A bitcast from a vector type to a scalar integer
; type will see the elements being packed together (without padding).  ... For
; little endian element zero is put in the least significant bits of the
; integer."  So <8 x i1> is 8 bits, not 8 bytes, and bitcasts to i8.  The
; in-memory layout of such a vector is defined as that of the same-sized
; integer, so storing an <8 x i1> and loading an i8 agrees with the bitcast.
; When N*M is not a multiple of 8 the memory layout of the padding is
; unspecified, so the memory tests below only use whole-byte vectors (or
; round-trip at the same type).
;
; Each case returns an i64 so the file can also be run natively, e.g.
;   clang -w tests/ll/bitcast-packed-vectors.ll -o a.out && ./a.out
; and its output compared with the ASSERTs at the bottom.
;
; Generated with tests/gen.py (print-all mode) from the functions below.

; ------------------------------------------------------- <N x i1> <-> int

; bits 0, 2, 3 set  ==>  0b00001101
define i64 @v8i1_to_i8() {
  %i = bitcast <8 x i1> <i1 1, i1 0, i1 1, i1 1, i1 0, i1 0, i1 0, i1 0> to i8
  %r = zext i8 %i to i64
  ret i64 %r
}

; element 7 is the most significant bit
define i64 @v8i1_high_to_i8() {
  %i = bitcast <8 x i1> <i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1> to i8
  %r = zext i8 %i to i64
  ret i64 %r
}

; elements 0, 8 and 15 set  ==>  0x8101
define i64 @v16i1_to_i16() {
  %i = bitcast <16 x i1> <i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                          i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1> to i16
  %r = zext i16 %i to i64
  ret i64 %r
}

; all 32 set  ==>  0xFFFFFFFF
define i64 @v32i1_to_i32() {
  %i = bitcast <32 x i1> <i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1,
                          i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1,
                          i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1,
                          i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1> to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; a sub-byte total size: <4 x i1> is an i4
define i64 @v4i1_to_i4() {
  %i = bitcast <4 x i1> <i1 0, i1 1, i1 1, i1 0> to i4
  %r = zext i4 %i to i64
  ret i64 %r
}

; 0b10100110 ==> <0,1,1,0,0,1,0,1>: elements 1, 2, 5, 7 are set, 0 is not;
; returns e0*10000 + e1*1000 + e2*100 + e5*10 + e7
define i64 @i8_to_v8i1() {
  %v = bitcast i8 -90 to <8 x i1>          ; 0xA6
  %e1 = extractelement <8 x i1> %v, i32 1
  %e2 = extractelement <8 x i1> %v, i32 2
  %e5 = extractelement <8 x i1> %v, i32 5
  %e7 = extractelement <8 x i1> %v, i32 7
  %e0 = extractelement <8 x i1> %v, i32 0
  %x1 = zext i1 %e1 to i64
  %x2 = zext i1 %e2 to i64
  %x5 = zext i1 %e5 to i64
  %x7 = zext i1 %e7 to i64
  %x0 = zext i1 %e0 to i64
  %y0 = mul i64 %x0, 10000
  %y1 = mul i64 %x1, 1000
  %y2 = mul i64 %x2, 100
  %y5 = mul i64 %x5, 10
  %s1 = add i64 %y0, %y1
  %s2 = add i64 %s1, %y2
  %s3 = add i64 %s2, %y5
  %s4 = add i64 %s3, %x7
  ret i64 %s4
}

; i16 0x0100 ==> <16 x i1>: only element 8 is set
define i64 @i16_to_v16i1() {
  %v = bitcast i16 256 to <16 x i1>
  %a = extractelement <16 x i1> %v, i32 8
  %b = extractelement <16 x i1> %v, i32 0
  %xa = zext i1 %a to i64
  %xb = zext i1 %b to i64
  %ya = mul i64 %xa, 10
  %s = add i64 %ya, %xb
  ret i64 %s
}

; ------------------------------------------- <N x i2>, <N x i4>, odd widths

; <4 x i2> <1, 2, 3, 0>  ==>  0b00_11_10_01
define i64 @v4i2_to_i8() {
  %i = bitcast <4 x i2> <i2 1, i2 2, i2 3, i2 0> to i8
  %r = zext i8 %i to i64
  ret i64 %r
}

; <2 x i4> <0xA, 0x5>  ==>  0x5A
define i64 @v2i4_to_i8() {
  %i = bitcast <2 x i4> <i4 10, i4 5> to i8
  %r = zext i8 %i to i64
  ret i64 %r
}

; <8 x i4> <1..8>  ==>  0x87654321
define i64 @v8i4_to_i32() {
  %i = bitcast <8 x i4> <i4 1, i4 2, i4 3, i4 4, i4 5, i4 6, i4 7, i4 8> to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; <2 x i12> <0x978, 0xCBA>  ==>  0xCBA978 (the example from issue #273)
define i64 @v2i12_to_i24() {
  %i = bitcast <2 x i12> <i12 2424, i12 3258> to i24
  %r = zext i24 %i to i64
  ret i64 %r
}

; <4 x i6> <1, 2, 3, 4>  ==>  1 | 2<<6 | 3<<12 | 4<<18: elements straddle bytes
define i64 @v4i6_to_i24() {
  %i = bitcast <4 x i6> <i6 1, i6 2, i6 3, i6 4> to i24
  %r = zext i24 %i to i64
  ret i64 %r
}

; <3 x i5> <31, 0, 1>  ==>  31 | 1<<10
define i64 @v3i5_to_i15() {
  %i = bitcast <3 x i5> <i5 31, i5 0, i5 1> to i15
  %r = zext i15 %i to i64
  ret i64 %r
}

; i24 0xCBA978 ==> <2 x i12>; returns e1 * 4096 + e0
define i64 @i24_to_v2i12() {
  %v = bitcast i24 13347192 to <2 x i12>
  %e0 = extractelement <2 x i12> %v, i32 0
  %e1 = extractelement <2 x i12> %v, i32 1
  %x0 = zext i12 %e0 to i64
  %x1 = zext i12 %e1 to i64
  %y1 = mul i64 %x1, 4096
  %s = add i64 %y1, %x0
  ret i64 %s
}

; i24 ==> <4 x i6>: element 2 sits in bits 12..17, across the byte boundary
define i64 @i24_to_v4i6() {
  %v = bitcast i24 1060993 to <4 x i6>     ; <1, 2, 3, 4>
  %e = extractelement <4 x i6> %v, i32 2
  %r = zext i6 %e to i64
  ret i64 %r
}

; ------------------------------------------------- packed vector <-> vector

; <8 x i1> ==> <2 x i4>: element 1 is bits 4..7
define i64 @v8i1_to_v2i4() {
  %v = bitcast <8 x i1> <i1 0, i1 0, i1 0, i1 0, i1 1, i1 0, i1 1, i1 0> to <2 x i4>
  %e = extractelement <2 x i4> %v, i32 1
  %r = zext i4 %e to i64
  ret i64 %r
}

; <16 x i1> ==> <2 x i8>: element 1 is bits 8..15
define i64 @v16i1_to_v2i8() {
  %v = bitcast <16 x i1> <i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1,
                          i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1> to <2 x i8>
  %e = extractelement <2 x i8> %v, i32 1
  %r = zext i8 %e to i64
  ret i64 %r
}

; <4 x i8> ==> <32 x i1>: 0x00000100 has only bit 8 set
define i64 @v4i8_to_v32i1() {
  %v = bitcast <4 x i8> <i8 0, i8 1, i8 0, i8 0> to <32 x i1>
  %a = extractelement <32 x i1> %v, i32 8
  %b = extractelement <32 x i1> %v, i32 1
  %xa = zext i1 %a to i64
  %xb = zext i1 %b to i64
  %ya = mul i64 %xa, 10
  %s = add i64 %ya, %xb
  ret i64 %s
}

; <2 x i12> ==> <3 x i8>: the middle byte holds the high nibble of e0 and the
; low nibble of e1 (0x978, 0xCBA -> bytes 78 A9 CB).
; NB: clang 23 at -O0 on arm64 prints 186 (0xBA) here; -O0 on x86-64 and
; -O2 on either give 169 (0xA9), which agrees with LangRef and with
; store_v2i12_load_byte below.
define i64 @v2i12_to_v3i8() {
  %v = bitcast <2 x i12> <i12 2424, i12 3258> to <3 x i8>
  %e = extractelement <3 x i8> %v, i32 1
  %r = zext i8 %e to i64
  ret i64 %r
}

; <32 x i1> ==> float: bits of 1.0f are 0x3F800000 (bits 23..29 set)
define i64 @v32i1_to_float() {
  %f = bitcast <32 x i1> <i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                          i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                          i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1,
                          i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 0, i1 0> to float
  %d = fmul float %f, 3.0
  %r = fptosi float %d to i64
  ret i64 %r
}

; ------------------------------------------------------------------ memory

; a stored <8 x i1> occupies one byte, laid out as the bitcast to i8
define i64 @store_v8i1_load_i8() {
  %p = alloca i8
  store <8 x i1> <i1 1, i1 0, i1 1, i1 1, i1 0, i1 0, i1 0, i1 0>, ptr %p
  %i = load i8, ptr %p
  %r = zext i8 %i to i64
  ret i64 %r
}

; ... and conversely
define i64 @store_i8_load_v8i1() {
  %p = alloca i8
  store i8 -90, ptr %p                     ; 0xA6
  %v = load <8 x i1>, ptr %p
  %e5 = extractelement <8 x i1> %v, i32 5
  %e6 = extractelement <8 x i1> %v, i32 6
  %x5 = zext i1 %e5 to i64
  %x6 = zext i1 %e6 to i64
  %y5 = mul i64 %x5, 10
  %s = add i64 %y5, %x6
  ret i64 %s
}

; a <32 x i1> fits exactly in an i32-sized slot (from issue #273: the store
; used to touch 32 bytes and fault)
define i64 @store_v32i1_in_i32() {
  %p = alloca i32
  store i32 -1, ptr %p
  store <32 x i1> <i1 0, i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                   i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                   i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                   i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1>, ptr %p
  %i = load i32, ptr %p
  %r = zext i32 %i to i64
  ret i64 %r
}

; a stored <16 x i1> does not spill into the next byte pair
define i64 @store_v16i1_neighbor() {
  %p = alloca [2 x i16]
  %q = getelementptr i16, ptr %p, i64 1
  store i16 12345, ptr %q
  store <16 x i1> zeroinitializer, ptr %p
  %i = load i16, ptr %q
  %r = zext i16 %i to i64
  ret i64 %r
}

; <2 x i4> in memory is one byte, laid out as the bitcast to i8
define i64 @store_v2i4_load_i8() {
  %p = alloca i8
  store <2 x i4> <i4 10, i4 5>, ptr %p
  %i = load i8, ptr %p
  %r = zext i8 %i to i64
  ret i64 %r
}

; <2 x i12> is 3 bytes: 78 A9 CB
define i64 @store_v2i12_load_byte() {
  %p = alloca i32
  store <2 x i12> <i12 2424, i12 3258>, ptr %p
  %q = getelementptr i8, ptr %p, i64 1
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; a non-byte-multiple vector round-trips through memory at its own type
define i64 @store_v5i1_roundtrip() {
  %p = alloca <5 x i1>
  store <5 x i1> <i1 0, i1 0, i1 0, i1 1, i1 1>, ptr %p
  %v = load <5 x i1>, ptr %p
  %i = bitcast <5 x i1> %v to i5
  %r = zext i5 %i to i64
  ret i64 %r
}

; extractelement after a load of a packed global (issue #273: <7 x i1>)
@g7 = global <7 x i1> <i1 0, i1 0, i1 0, i1 1, i1 0, i1 1, i1 0>

define i64 @load_v7i1_global() {
  %v = load <7 x i1>, ptr @g7
  %e3 = extractelement <7 x i1> %v, i32 3
  %e4 = extractelement <7 x i1> %v, i32 4
  %x3 = zext i1 %e3 to i64
  %x4 = zext i1 %e4 to i64
  %y3 = mul i64 %x3, 10
  %s = add i64 %y3, %x4
  ret i64 %s
}

; the allocation size of a packed vector, observed through gep: a
; <8 x i1> takes one byte, so the next element of an array is one byte on
define i64 @sizeof_v8i1() {
  %p = getelementptr <8 x i1>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @sizeof_v32i1() {
  %p = getelementptr <32 x i1>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_v8i1_to_i8 = private unnamed_addr constant [21 x i8] c"v8i1_to_i8() = %lld\0A\00"
@fmt_v8i1_high_to_i8 = private unnamed_addr constant [26 x i8] c"v8i1_high_to_i8() = %lld\0A\00"
@fmt_v16i1_to_i16 = private unnamed_addr constant [23 x i8] c"v16i1_to_i16() = %lld\0A\00"
@fmt_v32i1_to_i32 = private unnamed_addr constant [23 x i8] c"v32i1_to_i32() = %lld\0A\00"
@fmt_v4i1_to_i4 = private unnamed_addr constant [21 x i8] c"v4i1_to_i4() = %lld\0A\00"
@fmt_i8_to_v8i1 = private unnamed_addr constant [21 x i8] c"i8_to_v8i1() = %lld\0A\00"
@fmt_i16_to_v16i1 = private unnamed_addr constant [23 x i8] c"i16_to_v16i1() = %lld\0A\00"
@fmt_v4i2_to_i8 = private unnamed_addr constant [21 x i8] c"v4i2_to_i8() = %lld\0A\00"
@fmt_v2i4_to_i8 = private unnamed_addr constant [21 x i8] c"v2i4_to_i8() = %lld\0A\00"
@fmt_v8i4_to_i32 = private unnamed_addr constant [22 x i8] c"v8i4_to_i32() = %lld\0A\00"
@fmt_v2i12_to_i24 = private unnamed_addr constant [23 x i8] c"v2i12_to_i24() = %lld\0A\00"
@fmt_v4i6_to_i24 = private unnamed_addr constant [22 x i8] c"v4i6_to_i24() = %lld\0A\00"
@fmt_v3i5_to_i15 = private unnamed_addr constant [22 x i8] c"v3i5_to_i15() = %lld\0A\00"
@fmt_i24_to_v2i12 = private unnamed_addr constant [23 x i8] c"i24_to_v2i12() = %lld\0A\00"
@fmt_i24_to_v4i6 = private unnamed_addr constant [22 x i8] c"i24_to_v4i6() = %lld\0A\00"
@fmt_v8i1_to_v2i4 = private unnamed_addr constant [23 x i8] c"v8i1_to_v2i4() = %lld\0A\00"
@fmt_v16i1_to_v2i8 = private unnamed_addr constant [24 x i8] c"v16i1_to_v2i8() = %lld\0A\00"
@fmt_v4i8_to_v32i1 = private unnamed_addr constant [24 x i8] c"v4i8_to_v32i1() = %lld\0A\00"
@fmt_v2i12_to_v3i8 = private unnamed_addr constant [24 x i8] c"v2i12_to_v3i8() = %lld\0A\00"
@fmt_v32i1_to_float = private unnamed_addr constant [25 x i8] c"v32i1_to_float() = %lld\0A\00"
@fmt_store_v8i1_load_i8 = private unnamed_addr constant [29 x i8] c"store_v8i1_load_i8() = %lld\0A\00"
@fmt_store_i8_load_v8i1 = private unnamed_addr constant [29 x i8] c"store_i8_load_v8i1() = %lld\0A\00"
@fmt_store_v32i1_in_i32 = private unnamed_addr constant [29 x i8] c"store_v32i1_in_i32() = %lld\0A\00"
@fmt_store_v16i1_neighbor = private unnamed_addr constant [31 x i8] c"store_v16i1_neighbor() = %lld\0A\00"
@fmt_store_v2i4_load_i8 = private unnamed_addr constant [29 x i8] c"store_v2i4_load_i8() = %lld\0A\00"
@fmt_store_v2i12_load_byte = private unnamed_addr constant [32 x i8] c"store_v2i12_load_byte() = %lld\0A\00"
@fmt_store_v5i1_roundtrip = private unnamed_addr constant [31 x i8] c"store_v5i1_roundtrip() = %lld\0A\00"
@fmt_load_v7i1_global = private unnamed_addr constant [27 x i8] c"load_v7i1_global() = %lld\0A\00"
@fmt_sizeof_v8i1 = private unnamed_addr constant [22 x i8] c"sizeof_v8i1() = %lld\0A\00"
@fmt_sizeof_v32i1 = private unnamed_addr constant [23 x i8] c"sizeof_v32i1() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @v8i1_to_i8()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_v8i1_to_i8, i64 %v0)
  %v1 = call i64 @v8i1_high_to_i8()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_v8i1_high_to_i8, i64 %v1)
  %v2 = call i64 @v16i1_to_i16()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_v16i1_to_i16, i64 %v2)
  %v3 = call i64 @v32i1_to_i32()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_v32i1_to_i32, i64 %v3)
  %v4 = call i64 @v4i1_to_i4()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_v4i1_to_i4, i64 %v4)
  %v5 = call i64 @i8_to_v8i1()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_i8_to_v8i1, i64 %v5)
  %v6 = call i64 @i16_to_v16i1()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_i16_to_v16i1, i64 %v6)
  %v7 = call i64 @v4i2_to_i8()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_v4i2_to_i8, i64 %v7)
  %v8 = call i64 @v2i4_to_i8()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_v2i4_to_i8, i64 %v8)
  %v9 = call i64 @v8i4_to_i32()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_v8i4_to_i32, i64 %v9)
  %v10 = call i64 @v2i12_to_i24()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_v2i12_to_i24, i64 %v10)
  %v11 = call i64 @v4i6_to_i24()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_v4i6_to_i24, i64 %v11)
  %v12 = call i64 @v3i5_to_i15()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_v3i5_to_i15, i64 %v12)
  %v13 = call i64 @i24_to_v2i12()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_i24_to_v2i12, i64 %v13)
  %v14 = call i64 @i24_to_v4i6()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_i24_to_v4i6, i64 %v14)
  %v15 = call i64 @v8i1_to_v2i4()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_v8i1_to_v2i4, i64 %v15)
  %v16 = call i64 @v16i1_to_v2i8()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_v16i1_to_v2i8, i64 %v16)
  %v17 = call i64 @v4i8_to_v32i1()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_to_v32i1, i64 %v17)
  %v18 = call i64 @v2i12_to_v3i8()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_v2i12_to_v3i8, i64 %v18)
  %v19 = call i64 @v32i1_to_float()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_v32i1_to_float, i64 %v19)
  %v20 = call i64 @store_v8i1_load_i8()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_store_v8i1_load_i8, i64 %v20)
  %v21 = call i64 @store_i8_load_v8i1()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_store_i8_load_v8i1, i64 %v21)
  %v22 = call i64 @store_v32i1_in_i32()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_store_v32i1_in_i32, i64 %v22)
  %v23 = call i64 @store_v16i1_neighbor()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_store_v16i1_neighbor, i64 %v23)
  %v24 = call i64 @store_v2i4_load_i8()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_store_v2i4_load_i8, i64 %v24)
  %v25 = call i64 @store_v2i12_load_byte()
  %p25 = call i32 (ptr, ...) @printf(ptr @fmt_store_v2i12_load_byte, i64 %v25)
  %v26 = call i64 @store_v5i1_roundtrip()
  %p26 = call i32 (ptr, ...) @printf(ptr @fmt_store_v5i1_roundtrip, i64 %v26)
  %v27 = call i64 @load_v7i1_global()
  %p27 = call i32 (ptr, ...) @printf(ptr @fmt_load_v7i1_global, i64 %v27)
  %v28 = call i64 @sizeof_v8i1()
  %p28 = call i32 (ptr, ...) @printf(ptr @fmt_sizeof_v8i1, i64 %v28)
  %v29 = call i64 @sizeof_v32i1()
  %p29 = call i32 (ptr, ...) @printf(ptr @fmt_sizeof_v32i1, i64 %v29)
  ret i32 0
}

; ASSERT EQ: i64 13         = call i64 @v8i1_to_i8()
; ASSERT EQ: i64 128        = call i64 @v8i1_high_to_i8()
; ASSERT EQ: i64 33025      = call i64 @v16i1_to_i16()
; ASSERT EQ: i64 4294967295 = call i64 @v32i1_to_i32()
; ASSERT EQ: i64 6          = call i64 @v4i1_to_i4()
; ASSERT EQ: i64 1111       = call i64 @i8_to_v8i1()
; ASSERT EQ: i64 10         = call i64 @i16_to_v16i1()
; ASSERT EQ: i64 57         = call i64 @v4i2_to_i8()
; ASSERT EQ: i64 90         = call i64 @v2i4_to_i8()
; ASSERT EQ: i64 2271560481 = call i64 @v8i4_to_i32()
; ASSERT EQ: i64 13347192   = call i64 @v2i12_to_i24()
; ASSERT EQ: i64 1060993    = call i64 @v4i6_to_i24()
; ASSERT EQ: i64 1055       = call i64 @v3i5_to_i15()
; ASSERT EQ: i64 13347192   = call i64 @i24_to_v2i12()
; ASSERT EQ: i64 3          = call i64 @i24_to_v4i6()
; ASSERT EQ: i64 5          = call i64 @v8i1_to_v2i4()
; ASSERT EQ: i64 129        = call i64 @v16i1_to_v2i8()
; ASSERT EQ: i64 10         = call i64 @v4i8_to_v32i1()
; ASSERT EQ: i64 169        = call i64 @v2i12_to_v3i8()
; ASSERT EQ: i64 3          = call i64 @v32i1_to_float()
; ASSERT EQ: i64 13         = call i64 @store_v8i1_load_i8()
; ASSERT EQ: i64 10         = call i64 @store_i8_load_v8i1()
; ASSERT EQ: i64 2147483650 = call i64 @store_v32i1_in_i32()
; ASSERT EQ: i64 12345      = call i64 @store_v16i1_neighbor()
; ASSERT EQ: i64 90         = call i64 @store_v2i4_load_i8()
; ASSERT EQ: i64 169        = call i64 @store_v2i12_load_byte()
; ASSERT EQ: i64 24         = call i64 @store_v5i1_roundtrip()
; ASSERT EQ: i64 10         = call i64 @load_v7i1_global()
; ASSERT EQ: i64 1          = call i64 @sizeof_v8i1()
; ASSERT EQ: i64 4          = call i64 @sizeof_v32i1()
