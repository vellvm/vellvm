; Serialization / deserialization of aggregates through memory.
;
; Small, direct versions of a bug that previously only showed up in
; tests/perf/mem-aggregate.ll: the serializer emitted no inter-field padding
; while the deserializer skipped it, so every field after the first misaligned
; one was read back from the wrong offset. Each test below round-trips one
; value through a store/load pair, so it fails if the two sides disagree.
;
; Also covers the layout rules these depend on: a field advances by its *alloc*
; size, a non-packed struct's size includes its own tail padding, and
; getelementptr must agree with all of that.

%pad2   = type { i32, i64 }                 ; 4 bytes of padding before the i64
%tail   = type { i64, i32 }                 ; 4 bytes of padding after the i32
%nest   = type { { i64, i32 }, i8 }         ; nested struct, itself tail-padded
%packed = type <{ i32, i64 }>               ; packed: no padding anywhere
%mixed  = type { i64, i32, [4 x i64], i8 }  ; the mem-aggregate shape

; --- the field that sits immediately after inter-field padding ---
; This is the minimal failing case: before the fix @pad_second_field returned 0.
define i64 @pad_second_field() {
  %s = alloca %pad2
  %v0 = insertvalue %pad2 zeroinitializer, i32 11, 0
  %v1 = insertvalue %pad2 %v0, i64 22, 1
  store %pad2 %v1, %pad2* %s
  %r = load %pad2, %pad2* %s
  %x = extractvalue %pad2 %r, 1
  ret i64 %x
}

; the field *before* the padding must still be intact
define i64 @pad_first_field() {
  %s = alloca %pad2
  %v0 = insertvalue %pad2 zeroinitializer, i32 11, 0
  %v1 = insertvalue %pad2 %v0, i64 22, 1
  store %pad2 %v1, %pad2* %s
  %r = load %pad2, %pad2* %s
  %x = extractvalue %pad2 %r, 0
  %w = zext i32 %x to i64
  ret i64 %w
}

; a struct needing no padding at all: the control case
define i64 @no_padding_needed() {
  %s = alloca { i64, i64 }
  %v0 = insertvalue { i64, i64 } zeroinitializer, i64 11, 0
  %v1 = insertvalue { i64, i64 } %v0, i64 22, 1
  store { i64, i64 } %v1, { i64, i64 }* %s
  %r = load { i64, i64 }, { i64, i64 }* %s
  %x = extractvalue { i64, i64 } %r, 1
  ret i64 %x
}

; --- trailing padding: %tail is 12 bytes of fields, 16 of alloc size ---
define i64 @tail_padding_roundtrip() {
  %s = alloca %tail
  %v0 = insertvalue %tail zeroinitializer, i64 33, 0
  %v1 = insertvalue %tail %v0, i32 44, 1
  store %tail %v1, %tail* %s
  %r = load %tail, %tail* %s
  %x = extractvalue %tail %r, 1
  %w = zext i32 %x to i64
  ret i64 %w
}

; a struct whose own tail padding matters only once it is nested
define i64 @nested_after_tail_padding() {
  %s = alloca %nest
  %v0 = insertvalue %nest zeroinitializer, i64 55, 0, 0
  %v1 = insertvalue %nest %v0, i8 66, 1
  store %nest %v1, %nest* %s
  %r = load %nest, %nest* %s
  %x = extractvalue %nest %r, 1
  %w = zext i8 %x to i64
  ret i64 %w
}

; --- array stride is the element's alloc size, not its store size ---
; %tail is 12 bytes of fields but strides by 16, so element 1 starts at 16.
define i64 @array_of_padded_structs() {
  %a = alloca [2 x %tail]
  %p0 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 0, i32 0
  store i64 77, i64* %p0
  %p1 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 1, i32 0
  store i64 88, i64* %p1
  ; if the stride were wrong the two writes would overlap
  %q0 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 0, i32 0
  %v0 = load i64, i64* %q0
  %q1 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 1, i32 0
  %v1 = load i64, i64* %q1
  %sum = add i64 %v0, %v1
  ret i64 %sum
}

; --- getelementptr offsets must agree with the serializer's layout ---
; Write field 1 through a GEP, then read the whole struct back and extract it.
define i64 @gep_agrees_with_store() {
  %s = alloca %pad2
  store %pad2 zeroinitializer, %pad2* %s
  %p1 = getelementptr %pad2, %pad2* %s, i64 0, i32 1
  store i64 99, i64* %p1
  %r = load %pad2, %pad2* %s
  %x = extractvalue %pad2 %r, 1
  ret i64 %x
}

; and the converse: store the whole struct, read one field through a GEP
define i64 @store_agrees_with_gep() {
  %s = alloca %pad2
  %v0 = insertvalue %pad2 zeroinitializer, i32 11, 0
  %v1 = insertvalue %pad2 %v0, i64 123, 1
  store %pad2 %v1, %pad2* %s
  %p1 = getelementptr %pad2, %pad2* %s, i64 0, i32 1
  %x = load i64, i64* %p1
  ret i64 %x
}

; --- packed structs get no padding: field 1 sits at byte 4 ---
define i64 @packed_no_padding() {
  %s = alloca %packed
  %v0 = insertvalue %packed zeroinitializer, i32 11, 0
  %v1 = insertvalue %packed %v0, i64 22, 1
  store %packed %v1, %packed* %s
  %r = load %packed, %packed* %s
  %x = extractvalue %packed %r, 1
  ret i64 %x
}

; --- the mem-aggregate shape, one iteration ---
; Sums the fields the perf test sums; before the fix the [4 x i64] members
; came back as 0 because the array followed 4 bytes of padding.
define i64 @mixed_struct_roundtrip() {
  %s = alloca %mixed
  %v0 = insertvalue %mixed zeroinitializer, i64 1, 0
  %v1 = insertvalue %mixed %v0, i32 2, 1
  %v2 = insertvalue %mixed %v1, i64 4, 2, 1
  %v3 = insertvalue %mixed %v2, i64 8, 2, 3
  %v4 = insertvalue %mixed %v3, i8 16, 3
  store %mixed %v4, %mixed* %s
  %r = load %mixed, %mixed* %s
  %f0 = extractvalue %mixed %r, 0
  %f1 = extractvalue %mixed %r, 1
  %f1w = zext i32 %f1 to i64
  %f21 = extractvalue %mixed %r, 2, 1
  %f23 = extractvalue %mixed %r, 2, 3
  %f3 = extractvalue %mixed %r, 3
  %f3w = zext i8 %f3 to i64
  %a = add i64 %f0, %f1w
  %b = add i64 %f21, %f23
  %c = add i64 %a, %b
  %d = add i64 %c, %f3w
  ret i64 %d
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_pad_second_field = private unnamed_addr constant [27 x i8] c"pad_second_field() = %lld\0A\00"
@fmt_pad_first_field = private unnamed_addr constant [26 x i8] c"pad_first_field() = %lld\0A\00"
@fmt_no_padding_needed = private unnamed_addr constant [28 x i8] c"no_padding_needed() = %lld\0A\00"
@fmt_tail_padding_roundtrip = private unnamed_addr constant [33 x i8] c"tail_padding_roundtrip() = %lld\0A\00"
@fmt_nested_after_tail_padding = private unnamed_addr constant [36 x i8] c"nested_after_tail_padding() = %lld\0A\00"
@fmt_array_of_padded_structs = private unnamed_addr constant [34 x i8] c"array_of_padded_structs() = %lld\0A\00"
@fmt_gep_agrees_with_store = private unnamed_addr constant [32 x i8] c"gep_agrees_with_store() = %lld\0A\00"
@fmt_store_agrees_with_gep = private unnamed_addr constant [32 x i8] c"store_agrees_with_gep() = %lld\0A\00"
@fmt_packed_no_padding = private unnamed_addr constant [28 x i8] c"packed_no_padding() = %lld\0A\00"
@fmt_mixed_struct_roundtrip = private unnamed_addr constant [33 x i8] c"mixed_struct_roundtrip() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @pad_second_field()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_pad_second_field, i64 %v0)
  %v1 = call i64 @pad_first_field()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_pad_first_field, i64 %v1)
  %v2 = call i64 @no_padding_needed()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_no_padding_needed, i64 %v2)
  %v3 = call i64 @tail_padding_roundtrip()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_tail_padding_roundtrip, i64 %v3)
  %v4 = call i64 @nested_after_tail_padding()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_nested_after_tail_padding, i64 %v4)
  %v5 = call i64 @array_of_padded_structs()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_array_of_padded_structs, i64 %v5)
  %v6 = call i64 @gep_agrees_with_store()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_gep_agrees_with_store, i64 %v6)
  %v7 = call i64 @store_agrees_with_gep()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_store_agrees_with_gep, i64 %v7)
  %v8 = call i64 @packed_no_padding()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_packed_no_padding, i64 %v8)
  %v9 = call i64 @mixed_struct_roundtrip()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_mixed_struct_roundtrip, i64 %v9)
  ret i32 0
}

; ASSERT EQ: i64 22  = call i64 @pad_second_field()
; ASSERT EQ: i64 11  = call i64 @pad_first_field()
; ASSERT EQ: i64 22  = call i64 @no_padding_needed()
; ASSERT EQ: i64 44  = call i64 @tail_padding_roundtrip()
; ASSERT EQ: i64 66  = call i64 @nested_after_tail_padding()
; ASSERT EQ: i64 165 = call i64 @array_of_padded_structs()
; ASSERT EQ: i64 99  = call i64 @gep_agrees_with_store()
; ASSERT EQ: i64 123 = call i64 @store_agrees_with_gep()
; ASSERT EQ: i64 22  = call i64 @packed_no_padding()
; ASSERT EQ: i64 31  = call i64 @mixed_struct_roundtrip()
