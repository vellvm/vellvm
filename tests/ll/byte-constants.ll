; Byte constants.
;
; LangRef ("Byte constants"): byte constants are strictly equivalent to
; integer constants -- `store b8 42, ptr %p` is equivalent to
; `store i8 42, ptr %p` -- and they are how globals of byte type are
; initialized.
;
; Vellvm currently rejects every one of these with "bad type for constant
; int: bN": [denote_int_syntax_as_int] (Semantics/Denotation.v) has no
; [DTYPE_B] case.

@gb = global b32 7

; the LangRef's own example: a byte constant stored and read back as an integer
define i64 @store_byte_constant() {
  %p = alloca b8
  store b8 42, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

; negative literals denote the same bits as for integers
define i64 @store_negative_byte_constant() {
  %p = alloca b8
  store b8 -1, ptr %p
  %v = load i8, ptr %p
  %r = zext i8 %v to i64
  ret i64 %r
}

; a byte constant used directly as an operand, not via memory
define i64 @bitcast_byte_constant() {
  %i = bitcast b32 1000 to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; a global initialized with a byte constant
define i64 @global_byte_constant() {
  %v = load i32, ptr @gb
  %r = zext i32 %v to i64
  ret i64 %r
}

; byte constants as vector elements; element 0 is the low byte on a
; little-endian target, so the result is 2 * 256 + 1
define i64 @vector_byte_constant() {
  %i = bitcast <2 x b8> <b8 1, b8 2> to i16
  %r = zext i16 %i to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_store_byte_constant = private unnamed_addr constant [30 x i8] c"store_byte_constant() = %lld\0A\00"
@fmt_store_negative_byte_constant = private unnamed_addr constant [39 x i8] c"store_negative_byte_constant() = %lld\0A\00"
@fmt_bitcast_byte_constant = private unnamed_addr constant [32 x i8] c"bitcast_byte_constant() = %lld\0A\00"
@fmt_global_byte_constant = private unnamed_addr constant [31 x i8] c"global_byte_constant() = %lld\0A\00"
@fmt_vector_byte_constant = private unnamed_addr constant [31 x i8] c"vector_byte_constant() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @store_byte_constant()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_store_byte_constant, i64 %v0)
  %v1 = call i64 @store_negative_byte_constant()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_store_negative_byte_constant, i64 %v1)
  %v2 = call i64 @bitcast_byte_constant()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_bitcast_byte_constant, i64 %v2)
  %v3 = call i64 @global_byte_constant()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_global_byte_constant, i64 %v3)
  %v4 = call i64 @vector_byte_constant()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_vector_byte_constant, i64 %v4)
  ret i32 0
}

; ASSERT EQ: i64 42   = call i64 @store_byte_constant()
; ASSERT EQ: i64 255  = call i64 @store_negative_byte_constant()
; ASSERT EQ: i64 1000 = call i64 @bitcast_byte_constant()
; ASSERT EQ: i64 7    = call i64 @global_byte_constant()
; ASSERT EQ: i64 513  = call i64 @vector_byte_constant()
