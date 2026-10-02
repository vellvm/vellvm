; Poison at an aggregate type.
;
; [DVALUE_Poison] inhabits every type, so a poison struct/array value is
; well-typed and must serialize: it writes the type's worth of poison bytes.
; Serialization used to raise "type-mismatch non-struct value" instead, so a
; store of a poison aggregate failed outright.
;
; The overwrite tests matter as much as the plain store: emitting the wrong
; *number* of poison bytes would leave later writes landing at wrong offsets.

%pack   = type { i64, i32, [4 x i64], i8 }
%tail   = type { i64, i32 }
%packed = type <{ i32, i64 }>

; a poison aggregate can be stored and loaded at all
define i64 @store_poison_struct() {
  %s = alloca %pack
  store %pack poison, %pack* %s
  %r = load %pack, %pack* %s
  %f = extractvalue %pack %r, 0
  ; %f is poison: its value is undefined, and a native run would print
  ; whatever was on the stack.  Return a constant so the printed output is
  ; comparable with clang -- what this test checks is that the store/load of
  ; a poison aggregate happens at all rather than raising.
  ret i64 0
}

; ... and the bytes it wrote are the right count: a later write to field 0
; lands where field 0 actually is
define i64 @overwrite_first_field() {
  %s = alloca %pack
  store %pack poison, %pack* %s
  %p = getelementptr %pack, %pack* %s, i64 0, i32 0
  store i64 99, i64* %p
  %r = load %pack, %pack* %s
  %f = extractvalue %pack %r, 0
  ret i64 %f
}

; a field that sits after padding, overwritten on top of poison
define i64 @overwrite_after_padding() {
  %s = alloca %pack
  store %pack poison, %pack* %s
  %p = getelementptr %pack, %pack* %s, i64 0, i32 2, i64 1
  store i64 123, i64* %p
  %r = load %pack, %pack* %s
  %f = extractvalue %pack %r, 2, 1
  ret i64 %f
}

; two independent fields written over a poison struct stay independent
define i64 @overwrite_two_fields() {
  %s = alloca %tail
  store %tail poison, %tail* %s
  %p0 = getelementptr %tail, %tail* %s, i64 0, i32 0
  store i64 40, i64* %p0
  %p1 = getelementptr %tail, %tail* %s, i64 0, i32 1
  store i32 2, i32* %p1
  %r = load %tail, %tail* %s
  %f0 = extractvalue %tail %r, 0
  %f1 = extractvalue %tail %r, 1
  %f1w = zext i32 %f1 to i64
  %sum = add i64 %f0, %f1w
  ret i64 %sum
}

; poison at array type
define i64 @store_poison_array() {
  %a = alloca [3 x i64]
  store [3 x i64] poison, [3 x i64]* %a
  %p = getelementptr [3 x i64], [3 x i64]* %a, i64 0, i64 1
  store i64 42, i64* %p
  %v = load i64, i64* %p
  ret i64 %v
}

; a poison array element must not disturb its neighbours' offsets
define i64 @poison_array_stride() {
  %a = alloca [2 x %tail]
  store [2 x %tail] poison, [2 x %tail]* %a
  %p0 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 0, i32 0
  store i64 7, i64* %p0
  %p1 = getelementptr [2 x %tail], [2 x %tail]* %a, i64 0, i64 1, i32 0
  store i64 70, i64* %p1
  %v0 = load i64, i64* %p0
  %v1 = load i64, i64* %p1
  %sum = add i64 %v0, %v1
  ret i64 %sum
}

; poison at a packed aggregate type
define i64 @store_poison_packed() {
  %s = alloca %packed
  store %packed poison, %packed* %s
  %p = getelementptr %packed, %packed* %s, i64 0, i32 1
  store i64 64, i64* %p
  %v = load i64, i64* %p
  ret i64 %v
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_store_poison_struct = private unnamed_addr constant [30 x i8] c"store_poison_struct() = %lld\0A\00"
@fmt_overwrite_first_field = private unnamed_addr constant [32 x i8] c"overwrite_first_field() = %lld\0A\00"
@fmt_overwrite_after_padding = private unnamed_addr constant [34 x i8] c"overwrite_after_padding() = %lld\0A\00"
@fmt_overwrite_two_fields = private unnamed_addr constant [31 x i8] c"overwrite_two_fields() = %lld\0A\00"
@fmt_store_poison_array = private unnamed_addr constant [29 x i8] c"store_poison_array() = %lld\0A\00"
@fmt_poison_array_stride = private unnamed_addr constant [30 x i8] c"poison_array_stride() = %lld\0A\00"
@fmt_store_poison_packed = private unnamed_addr constant [30 x i8] c"store_poison_packed() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @store_poison_struct()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_store_poison_struct, i64 %v0)
  %v1 = call i64 @overwrite_first_field()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_overwrite_first_field, i64 %v1)
  %v2 = call i64 @overwrite_after_padding()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_overwrite_after_padding, i64 %v2)
  %v3 = call i64 @overwrite_two_fields()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_overwrite_two_fields, i64 %v3)
  %v4 = call i64 @store_poison_array()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_store_poison_array, i64 %v4)
  %v5 = call i64 @poison_array_stride()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_poison_array_stride, i64 %v5)
  %v6 = call i64 @store_poison_packed()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_store_poison_packed, i64 %v6)
  ret i32 0
}

; ASSERT EQ: i64 0 = call i64 @store_poison_struct()
; ASSERT EQ: i64 99  = call i64 @overwrite_first_field()
; ASSERT EQ: i64 123 = call i64 @overwrite_after_padding()
; ASSERT EQ: i64 42  = call i64 @overwrite_two_fields()
; ASSERT EQ: i64 42  = call i64 @store_poison_array()
; ASSERT EQ: i64 77  = call i64 @poison_array_stride()
; ASSERT EQ: i64 64  = call i64 @store_poison_packed()
