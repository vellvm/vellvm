; bitcast between vectors with byte-sized elements and scalar types.
;
; LangRef ('bitcast'): the conversion is done as if the value had been stored
; to memory and read back as the destination type.  For vectors of byte-sized
; elements that is the array layout, so on a little-endian target element 0
; lands in the least significant bits of the integer.  (Vellvm, like the
; default datalayout, is little-endian; the expected values below assume it.)
;
; Each case returns an i64 so the file can also be run natively, e.g.
;   clang -w tests/ll/bitcast-vectors.ll -o a.out && ./a.out
; and its output compared with the ASSERTs at the bottom.
;
; Generated with tests/gen.py (print-all mode) from the functions below.

; ----------------------------------------------------------- vector -> int

; <4 x i8> <1, 2, 3, 4>  ==>  0x04030201
define i64 @v4i8_to_i32() {
  %i = bitcast <4 x i8> <i8 1, i8 2, i8 3, i8 4> to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; the element bit patterns are kept as-is: -1 is 0xFF, not a sign extension
define i64 @v4i8_neg_to_i32() {
  %i = bitcast <4 x i8> <i8 -1, i8 0, i8 -128, i8 127> to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; <2 x i16> <0x1234, 0xABCD>  ==>  0xABCD1234
define i64 @v2i16_to_i32() {
  %i = bitcast <2 x i16> <i16 4660, i16 -21555> to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; <8 x i8> <1..8>  ==>  0x0807060504030201
define i64 @v8i8_to_i64() {
  %i = bitcast <8 x i8> <i8 1, i8 2, i8 3, i8 4, i8 5, i8 6, i8 7, i8 8> to i64
  ret i64 %i
}

; <4 x i16> <1, 2, 3, 4>  ==>  0x0004000300020001
define i64 @v4i16_to_i64() {
  %i = bitcast <4 x i16> <i16 1, i16 2, i16 3, i16 4> to i64
  ret i64 %i
}

; <2 x i32> <7, 1>  ==>  0x0000000100000007
define i64 @v2i32_to_i64() {
  %i = bitcast <2 x i32> <i32 7, i32 1> to i64
  ret i64 %i
}

; a single-element vector is the same bits as its element
define i64 @v1i64_to_i64() {
  %i = bitcast <1 x i64> <i64 -2> to i64
  ret i64 %i
}

; the vector does not have to be a constant
define i64 @v4i8_built_to_i32() {
  %a = insertelement <4 x i8> zeroinitializer, i8 16, i32 0
  %b = insertelement <4 x i8> %a, i8 32, i32 1
  %c = insertelement <4 x i8> %b, i8 48, i32 2
  %d = insertelement <4 x i8> %c, i8 64, i32 3
  %i = bitcast <4 x i8> %d to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; ----------------------------------------------------------- int -> vector

; 0x04030201 ==> <1, 2, 3, 4>; returns e0 + 10*e1 + 100*e2 + 1000*e3
define i64 @i32_to_v4i8() {
  %v = bitcast i32 67305985 to <4 x i8>
  %e0 = extractelement <4 x i8> %v, i32 0
  %e1 = extractelement <4 x i8> %v, i32 1
  %e2 = extractelement <4 x i8> %v, i32 2
  %e3 = extractelement <4 x i8> %v, i32 3
  %x0 = zext i8 %e0 to i64
  %x1 = zext i8 %e1 to i64
  %x2 = zext i8 %e2 to i64
  %x3 = zext i8 %e3 to i64
  %y1 = mul i64 %x1, 10
  %y2 = mul i64 %x2, 100
  %y3 = mul i64 %x3, 1000
  %s1 = add i64 %x0, %y1
  %s2 = add i64 %s1, %y2
  %s3 = add i64 %s2, %y3
  ret i64 %s3
}

; the most significant byte is the last element
define i64 @i32_to_v4i8_last() {
  %v = bitcast i32 -16777216 to <4 x i8>     ; 0xFF000000
  %e = extractelement <4 x i8> %v, i32 3
  %r = sext i8 %e to i64
  ret i64 %r
}

; 0x0000000100000007 ==> <7, 1>; returns e0 * 100 + e1
define i64 @i64_to_v2i32() {
  %v = bitcast i64 4294967303 to <2 x i32>
  %e0 = extractelement <2 x i32> %v, i32 0
  %e1 = extractelement <2 x i32> %v, i32 1
  %x0 = zext i32 %e0 to i64
  %x1 = zext i32 %e1 to i64
  %y0 = mul i64 %x0, 100
  %s = add i64 %y0, %x1
  ret i64 %s
}

; i64 ==> <4 x i16>, element 2 is bits 32..47
define i64 @i64_to_v4i16() {
  %v = bitcast i64 1407404948520961 to <4 x i16>   ; 0x0005000700030001
  %e = extractelement <4 x i16> %v, i32 2
  %r = zext i16 %e to i64
  ret i64 %r
}

; -------------------------------------------------------- vector -> vector

; <4 x i8> <1, 2, 3, 4> ==> <2 x i16> <0x0201, 0x0403>; returns e1 * 65536 + e0
define i64 @v4i8_to_v2i16() {
  %v = bitcast <4 x i8> <i8 1, i8 2, i8 3, i8 4> to <2 x i16>
  %e0 = extractelement <2 x i16> %v, i32 0
  %e1 = extractelement <2 x i16> %v, i32 1
  %x0 = zext i16 %e0 to i64
  %x1 = zext i16 %e1 to i64
  %y1 = shl i64 %x1, 16
  %s = or i64 %y1, %x0
  ret i64 %s
}

; <2 x i16> <0x0201, 0x0403> ==> <4 x i8>; returns element 2
define i64 @v2i16_to_v4i8() {
  %v = bitcast <2 x i16> <i16 513, i16 1027> to <4 x i8>
  %e = extractelement <4 x i8> %v, i32 2
  %r = zext i8 %e to i64
  ret i64 %r
}

; <8 x i8> ==> <2 x i32>; returns element 1
define i64 @v8i8_to_v2i32() {
  %v = bitcast <8 x i8> <i8 1, i8 2, i8 3, i8 4, i8 5, i8 6, i8 7, i8 8> to <2 x i32>
  %e = extractelement <2 x i32> %v, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; round trip through a different shape gives back the original
define i64 @v4i8_roundtrip() {
  %a = bitcast <4 x i8> <i8 9, i8 8, i8 7, i8 6> to <2 x i16>
  %b = bitcast <2 x i16> %a to i32
  %c = bitcast i32 %b to <4 x i8>
  %e = extractelement <4 x i8> %c, i32 1
  %r = zext i8 %e to i64
  ret i64 %r
}

; ---------------------------------------------------------- floating point

; 1.0f is 0x3F800000 ==> <4 x i8> <0, 0, 0x80, 0x3F>; returns e3 * 256 + e2
define i64 @float_to_v4i8() {
  %v = bitcast float 1.0 to <4 x i8>
  %e2 = extractelement <4 x i8> %v, i32 2
  %e3 = extractelement <4 x i8> %v, i32 3
  %x2 = zext i8 %e2 to i64
  %x3 = zext i8 %e3 to i64
  %y3 = shl i64 %x3, 8
  %s = or i64 %y3, %x2
  ret i64 %s
}

; <4 x i8> <0, 0, 0x80, 0x3F> ==> 1.0f; returns it converted to an integer
define i64 @v4i8_to_float() {
  %f = bitcast <4 x i8> <i8 0, i8 0, i8 -128, i8 63> to float
  %d = fmul float %f, 5.0
  %r = fptosi float %d to i64
  ret i64 %r
}

; 2.0 is 0x4000000000000000 ==> <2 x i32> <0, 0x40000000>; returns element 1
define i64 @double_to_v2i32() {
  %v = bitcast double 2.0 to <2 x i32>
  %e = extractelement <2 x i32> %v, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; <2 x float> <1.0, 2.0> ==> 0x400000003F800000: element 1 is the high word
define i64 @v2float_to_i64() {
  %i = bitcast <2 x float> <float 1.0, float 2.0> to i64
  ret i64 %i
}

; i64 ==> <2 x float>, then add the two elements
define i64 @i64_to_v2float() {
  %v = bitcast i64 4611686019492741120 to <2 x float>  ; <1.0, 2.0>
  %a = extractelement <2 x float> %v, i32 0
  %b = extractelement <2 x float> %v, i32 1
  %s = fadd float %a, %b
  %r = fptosi float %s to i64
  ret i64 %r
}

; ------------------------------------------------------------------ memory
;
; Not bitcast instructions, but the same layout rule seen through memory:
; storing at one type and loading at another must agree with bitcast.

define i64 @store_v4i8_load_i32() {
  %p = alloca i32
  store <4 x i8> <i8 1, i8 2, i8 3, i8 4>, ptr %p
  %i = load i32, ptr %p
  %r = zext i32 %i to i64
  ret i64 %r
}

define i64 @store_i32_load_v4i8() {
  %p = alloca i32
  store i32 67305985, ptr %p
  %v = load <4 x i8>, ptr %p
  %e = extractelement <4 x i8> %v, i32 3
  %r = zext i8 %e to i64
  ret i64 %r
}

define i64 @store_v2i32_load_i64() {
  %p = alloca i64
  store <2 x i32> <i32 7, i32 1>, ptr %p
  %i = load i64, ptr %p
  ret i64 %i
}

; the byte at offset 1 of a stored <2 x i16> is the high byte of element 0
define i64 @store_v2i16_load_byte() {
  %p = alloca <2 x i16>
  store <2 x i16> <i16 4660, i16 -21555>, ptr %p
  %q = getelementptr i8, ptr %p, i64 1
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_v4i8_to_i32 = private unnamed_addr constant [22 x i8] c"v4i8_to_i32() = %lld\0A\00"
@fmt_v4i8_neg_to_i32 = private unnamed_addr constant [26 x i8] c"v4i8_neg_to_i32() = %lld\0A\00"
@fmt_v2i16_to_i32 = private unnamed_addr constant [23 x i8] c"v2i16_to_i32() = %lld\0A\00"
@fmt_v8i8_to_i64 = private unnamed_addr constant [22 x i8] c"v8i8_to_i64() = %lld\0A\00"
@fmt_v4i16_to_i64 = private unnamed_addr constant [23 x i8] c"v4i16_to_i64() = %lld\0A\00"
@fmt_v2i32_to_i64 = private unnamed_addr constant [23 x i8] c"v2i32_to_i64() = %lld\0A\00"
@fmt_v1i64_to_i64 = private unnamed_addr constant [23 x i8] c"v1i64_to_i64() = %lld\0A\00"
@fmt_v4i8_built_to_i32 = private unnamed_addr constant [28 x i8] c"v4i8_built_to_i32() = %lld\0A\00"
@fmt_i32_to_v4i8 = private unnamed_addr constant [22 x i8] c"i32_to_v4i8() = %lld\0A\00"
@fmt_i32_to_v4i8_last = private unnamed_addr constant [27 x i8] c"i32_to_v4i8_last() = %lld\0A\00"
@fmt_i64_to_v2i32 = private unnamed_addr constant [23 x i8] c"i64_to_v2i32() = %lld\0A\00"
@fmt_i64_to_v4i16 = private unnamed_addr constant [23 x i8] c"i64_to_v4i16() = %lld\0A\00"
@fmt_v4i8_to_v2i16 = private unnamed_addr constant [24 x i8] c"v4i8_to_v2i16() = %lld\0A\00"
@fmt_v2i16_to_v4i8 = private unnamed_addr constant [24 x i8] c"v2i16_to_v4i8() = %lld\0A\00"
@fmt_v8i8_to_v2i32 = private unnamed_addr constant [24 x i8] c"v8i8_to_v2i32() = %lld\0A\00"
@fmt_v4i8_roundtrip = private unnamed_addr constant [25 x i8] c"v4i8_roundtrip() = %lld\0A\00"
@fmt_float_to_v4i8 = private unnamed_addr constant [24 x i8] c"float_to_v4i8() = %lld\0A\00"
@fmt_v4i8_to_float = private unnamed_addr constant [24 x i8] c"v4i8_to_float() = %lld\0A\00"
@fmt_double_to_v2i32 = private unnamed_addr constant [26 x i8] c"double_to_v2i32() = %lld\0A\00"
@fmt_v2float_to_i64 = private unnamed_addr constant [25 x i8] c"v2float_to_i64() = %lld\0A\00"
@fmt_i64_to_v2float = private unnamed_addr constant [25 x i8] c"i64_to_v2float() = %lld\0A\00"
@fmt_store_v4i8_load_i32 = private unnamed_addr constant [30 x i8] c"store_v4i8_load_i32() = %lld\0A\00"
@fmt_store_i32_load_v4i8 = private unnamed_addr constant [30 x i8] c"store_i32_load_v4i8() = %lld\0A\00"
@fmt_store_v2i32_load_i64 = private unnamed_addr constant [31 x i8] c"store_v2i32_load_i64() = %lld\0A\00"
@fmt_store_v2i16_load_byte = private unnamed_addr constant [32 x i8] c"store_v2i16_load_byte() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @v4i8_to_i32()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_to_i32, i64 %v0)
  %v1 = call i64 @v4i8_neg_to_i32()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_neg_to_i32, i64 %v1)
  %v2 = call i64 @v2i16_to_i32()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_v2i16_to_i32, i64 %v2)
  %v3 = call i64 @v8i8_to_i64()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_v8i8_to_i64, i64 %v3)
  %v4 = call i64 @v4i16_to_i64()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_v4i16_to_i64, i64 %v4)
  %v5 = call i64 @v2i32_to_i64()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_v2i32_to_i64, i64 %v5)
  %v6 = call i64 @v1i64_to_i64()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_v1i64_to_i64, i64 %v6)
  %v7 = call i64 @v4i8_built_to_i32()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_built_to_i32, i64 %v7)
  %v8 = call i64 @i32_to_v4i8()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_i32_to_v4i8, i64 %v8)
  %v9 = call i64 @i32_to_v4i8_last()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_i32_to_v4i8_last, i64 %v9)
  %v10 = call i64 @i64_to_v2i32()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_i64_to_v2i32, i64 %v10)
  %v11 = call i64 @i64_to_v4i16()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_i64_to_v4i16, i64 %v11)
  %v12 = call i64 @v4i8_to_v2i16()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_to_v2i16, i64 %v12)
  %v13 = call i64 @v2i16_to_v4i8()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_v2i16_to_v4i8, i64 %v13)
  %v14 = call i64 @v8i8_to_v2i32()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_v8i8_to_v2i32, i64 %v14)
  %v15 = call i64 @v4i8_roundtrip()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_roundtrip, i64 %v15)
  %v16 = call i64 @float_to_v4i8()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_float_to_v4i8, i64 %v16)
  %v17 = call i64 @v4i8_to_float()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_v4i8_to_float, i64 %v17)
  %v18 = call i64 @double_to_v2i32()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_double_to_v2i32, i64 %v18)
  %v19 = call i64 @v2float_to_i64()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_v2float_to_i64, i64 %v19)
  %v20 = call i64 @i64_to_v2float()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_i64_to_v2float, i64 %v20)
  %v21 = call i64 @store_v4i8_load_i32()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_store_v4i8_load_i32, i64 %v21)
  %v22 = call i64 @store_i32_load_v4i8()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_store_i32_load_v4i8, i64 %v22)
  %v23 = call i64 @store_v2i32_load_i64()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_store_v2i32_load_i64, i64 %v23)
  %v24 = call i64 @store_v2i16_load_byte()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_store_v2i16_load_byte, i64 %v24)
  ret i32 0
}

; ASSERT EQ: i64 67305985            = call i64 @v4i8_to_i32()
; ASSERT EQ: i64 2139095295          = call i64 @v4i8_neg_to_i32()
; ASSERT EQ: i64 2882343476          = call i64 @v2i16_to_i32()
; ASSERT EQ: i64 578437695752307201  = call i64 @v8i8_to_i64()
; ASSERT EQ: i64 1125912791875585    = call i64 @v4i16_to_i64()
; ASSERT EQ: i64 4294967303          = call i64 @v2i32_to_i64()
; ASSERT EQ: i64 -2                  = call i64 @v1i64_to_i64()
; ASSERT EQ: i64 1076895760          = call i64 @v4i8_built_to_i32()
; ASSERT EQ: i64 4321                = call i64 @i32_to_v4i8()
; ASSERT EQ: i64 -1                  = call i64 @i32_to_v4i8_last()
; ASSERT EQ: i64 701                 = call i64 @i64_to_v2i32()
; ASSERT EQ: i64 7                   = call i64 @i64_to_v4i16()
; ASSERT EQ: i64 67305985            = call i64 @v4i8_to_v2i16()
; ASSERT EQ: i64 3                   = call i64 @v2i16_to_v4i8()
; ASSERT EQ: i64 134678021           = call i64 @v8i8_to_v2i32()
; ASSERT EQ: i64 8                   = call i64 @v4i8_roundtrip()
; ASSERT EQ: i64 16256               = call i64 @float_to_v4i8()
; ASSERT EQ: i64 5                   = call i64 @v4i8_to_float()
; ASSERT EQ: i64 1073741824          = call i64 @double_to_v2i32()
; ASSERT EQ: i64 4611686019492741120 = call i64 @v2float_to_i64()
; ASSERT EQ: i64 3                   = call i64 @i64_to_v2float()
; ASSERT EQ: i64 67305985            = call i64 @store_v4i8_load_i32()
; ASSERT EQ: i64 4                   = call i64 @store_i32_load_v4i8()
; ASSERT EQ: i64 4294967303          = call i64 @store_v2i32_load_i64()
; ASSERT EQ: i64 18                  = call i64 @store_v2i16_load_byte()
