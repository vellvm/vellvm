; Aggregate literals in ASSERT lines: `zeroinitializer` and structured `poison`.
;
; The harness evaluates the literals of an assertion with the semantics'
; own [denote_exp], so the expected value and the arguments of an ASSERT may
; be any closed constant: `zeroinitializer` at an aggregate type, `poison` at
; an aggregate type, and aggregates with `poison` or `zeroinitializer` inside.
; These are spot checks of that, not of the operations used to build the
; values.
;
; The aggregate-typed assertions sit next to their functions.  The `nat_*`
; functions at the end reduce the defined results to an i64, so that the file
; can also be run natively (`main` prints them) and diffed against clang.
; Functions whose result is poison are only asserted, never printed.
;
; Generated tail: python3 tests/gen.py (print-all mode).

; ------------------------------------------- zeroinitializer, expected value

; ASSERT EQ: {i32, i64} zeroinitializer = call {i32, i64} @zero_struct()
define {i32, i64} @zero_struct() {
  ret {i32, i64} zeroinitializer
}

; the same value, built field by field
; ASSERT EQ: {i32, i64} zeroinitializer = call {i32, i64} @zero_struct_built()
define {i32, i64} @zero_struct_built() {
  %a = insertvalue {i32, i64} poison, i32 0, 0
  %b = insertvalue {i32, i64} %a, i64 0, 1
  ret {i32, i64} %b
}

; ... and through memory
; ASSERT EQ: [3 x i32] zeroinitializer = call [3 x i32] @zero_array_loaded()
define [3 x i32] @zero_array_loaded() {
  %p = alloca [3 x i32]
  store [3 x i32] zeroinitializer, ptr %p
  %r = load [3 x i32], ptr %p
  ret [3 x i32] %r
}

; ASSERT EQ: <4 x i32> zeroinitializer = call <4 x i32> @zero_vector_xor(<4 x i32> <i32 1, i32 2, i32 3, i32 4>)
define <4 x i32> @zero_vector_xor(<4 x i32> %v) {
  %r = xor <4 x i32> %v, %v
  ret <4 x i32> %r
}

; nested, with padding between the fields
; ASSERT EQ: {i8, [2 x {i16, i32}], <2 x i64>} zeroinitializer = call {i8, [2 x {i16, i32}], <2 x i64>} @zero_nested()
define {i8, [2 x {i16, i32}], <2 x i64>} @zero_nested() {
  %p = alloca {i8, [2 x {i16, i32}], <2 x i64>}
  store {i8, [2 x {i16, i32}], <2 x i64>} zeroinitializer, ptr %p
  %r = load {i8, [2 x {i16, i32}], <2 x i64>}, ptr %p
  ret {i8, [2 x {i16, i32}], <2 x i64>} %r
}

; ASSERT EQ: {float, double} zeroinitializer = call {float, double} @zero_floats()
define {float, double} @zero_floats() {
  %a = insertvalue {float, double} poison, float 0.0, 0
  %b = insertvalue {float, double} %a, double 0.0, 1
  ret {float, double} %b
}

; ASSERT EQ: <{i8, i32}> zeroinitializer = call <{i8, i32}> @zero_packed()
define <{i8, i32}> @zero_packed() {
  %p = alloca <{i8, i32}>
  store <{i8, i32}> zeroinitializer, ptr %p
  %r = load <{i8, i32}>, ptr %p
  ret <{i8, i32}> %r
}

; zeroinitializer nested inside a literal
; ASSERT EQ: {i32, [2 x i32]} {i32 7, [2 x i32] zeroinitializer} = call {i32, [2 x i32]} @partly_zero()
define {i32, [2 x i32]} @partly_zero() {
  %a = insertvalue {i32, [2 x i32]} zeroinitializer, i32 7, 0
  ret {i32, [2 x i32]} %a
}

; ------------------------------------------------ zeroinitializer, argument

; ASSERT EQ: i64 0 = call i64 @sum_struct({i32, i64} zeroinitializer)
; ASSERT EQ: i64 5 = call i64 @sum_struct({i32, i64} {i32 2, i64 3})
define i64 @sum_struct({i32, i64} %s) {
  %a = extractvalue {i32, i64} %s, 0
  %b = extractvalue {i32, i64} %s, 1
  %a64 = zext i32 %a to i64
  %r = add i64 %a64, %b
  ret i64 %r
}

; ASSERT EQ: i64 0 = call i64 @sum_array([3 x i32] zeroinitializer)
; ASSERT EQ: i64 6 = call i64 @sum_array([3 x i32] [i32 1, i32 2, i32 3])
define i64 @sum_array([3 x i32] %a) {
  %x = extractvalue [3 x i32] %a, 0
  %y = extractvalue [3 x i32] %a, 1
  %z = extractvalue [3 x i32] %a, 2
  %xy = add i32 %x, %y
  %xyz = add i32 %xy, %z
  %r = zext i32 %xyz to i64
  ret i64 %r
}

; zeroinitializer and the spelled-out zero are the same value
; ASSERT EQ: {i32, i64} zeroinitializer = call {i32, i64} @id_struct({i32, i64} zeroinitializer)
; ASSERT EQ: {i32, i64} zeroinitializer = call {i32, i64} @id_struct({i32, i64} {i32 0, i64 0})
; ASSERT EQ: {i32, i64} {i32 0, i64 0} = call {i32, i64} @id_struct({i32, i64} zeroinitializer)
define {i32, i64} @id_struct({i32, i64} %s) {
  ret {i32, i64} %s
}

; ------------------------------------------------------- structured poison

; poison at a struct type, as argument and as expected value
; ASSERT EQ: {i32, i64} poison = call {i32, i64} @id_struct({i32, i64} poison)

; a struct with one poison field
; ASSERT EQ: {i32, i64} {i32 1, i64 poison} = call {i32, i64} @one_field_poison()
define {i32, i64} @one_field_poison() {
  %a = insertvalue {i32, i64} poison, i32 1, 0
  ret {i32, i64} %a
}

; uninitialized memory reads as poison at the aggregate's type
; ASSERT EQ: {i32, i64} poison = call {i32, i64} @load_uninit_struct()
define {i32, i64} @load_uninit_struct() {
  %p = alloca {i32, i64}
  %r = load {i32, i64}, ptr %p
  ret {i32, i64} %r
}

; ASSERT EQ: [2 x i32] poison = call [2 x i32] @store_load_poison_array()
define [2 x i32] @store_load_poison_array() {
  %p = alloca [2 x i32]
  store [2 x i32] poison, ptr %p
  %r = load [2 x i32], ptr %p
  ret [2 x i32] %r
}

; poison nested inside a literal: the inner struct was never written
; ASSERT EQ: {{i32, i32}, i32} {{i32, i32} poison, i32 1} = call {{i32, i32}, i32} @nested_poison_loaded()
define {{i32, i32}, i32} @nested_poison_loaded() {
  %p = alloca {{i32, i32}, i32}
  store {{i32, i32}, i32} poison, ptr %p
  %q = getelementptr {{i32, i32}, i32}, ptr %p, i32 0, i32 1
  store i32 1, ptr %q
  %r = load {{i32, i32}, i32}, ptr %p
  ret {{i32, i32}, i32} %r
}

; a poison vector inside a struct
; ASSERT EQ: {i32, <2 x i32>} {i32 1, <2 x i32> poison} = call {i32, <2 x i32>} @vec_in_struct()
define {i32, <2 x i32>} @vec_in_struct() {
  %a = insertvalue {i32, <2 x i32>} poison, i32 1, 0
  ret {i32, <2 x i32>} %a
}

; a vector literal of poison lanes is the value poison
; ASSERT EQ: <2 x i32> poison = call <2 x i32> @id_vec(<2 x i32> <i32 poison, i32 poison>)
; ASSERT EQ: <2 x i32> <i32 poison, i32 poison> = call <2 x i32> @id_vec(<2 x i32> poison)
define <2 x i32> @id_vec(<2 x i32> %v) {
  ret <2 x i32> %v
}

; poison in an argument that is not used, or only partly used
; ASSERT EQ: i64 5 = call i64 @ignore_struct({i32, i64} poison)
define i64 @ignore_struct({i32, i64} %s) {
  ret i64 5
}

; ASSERT EQ: i64 7 = call i64 @second_field({i32, i64} {i32 poison, i64 7})
; ASSERT EQ: i64 poison = call i64 @second_field({i32, i64} poison)
; ASSERT EQ: i64 poison = call i64 @second_field({i32, i64} {i32 7, i64 poison})
define i64 @second_field({i32, i64} %s) {
  %r = extractvalue {i32, i64} %s, 1
  ret i64 %r
}

; ----------------------------------------------- the defined results, as i64

define i64 @nat_zero_struct() {
  %s = call {i32, i64} @zero_struct_built()
  %r = call i64 @sum_struct({i32, i64} %s)
  ret i64 %r
}

define i64 @nat_sum_struct() {
  %r = call i64 @sum_struct({i32, i64} {i32 2, i64 3})
  ret i64 %r
}

define i64 @nat_zero_array() {
  %a = call [3 x i32] @zero_array_loaded()
  %r = call i64 @sum_array([3 x i32] %a)
  ret i64 %r
}

define i64 @nat_zero_vector() {
  %v = call <4 x i32> @zero_vector_xor(<4 x i32> <i32 1, i32 2, i32 3, i32 4>)
  %a = extractelement <4 x i32> %v, i32 0
  %b = extractelement <4 x i32> %v, i32 3
  %ab = add i32 %a, %b
  %r = zext i32 %ab to i64
  ret i64 %r
}

define i64 @nat_zero_nested() {
  %s = call {i8, [2 x {i16, i32}], <2 x i64>} @zero_nested()
  %a = extractvalue {i8, [2 x {i16, i32}], <2 x i64>} %s, 0
  %b = extractvalue {i8, [2 x {i16, i32}], <2 x i64>} %s, 1, 1, 1
  %v = extractvalue {i8, [2 x {i16, i32}], <2 x i64>} %s, 2
  %c = extractelement <2 x i64> %v, i32 1
  %a64 = zext i8 %a to i64
  %b64 = zext i32 %b to i64
  %ab = add i64 %a64, %b64
  %r = add i64 %ab, %c
  ret i64 %r
}

define i64 @nat_partly_zero() {
  %s = call {i32, [2 x i32]} @partly_zero()
  %a = extractvalue {i32, [2 x i32]} %s, 0
  %b = extractvalue {i32, [2 x i32]} %s, 1, 1
  %ab = add i32 %a, %b
  %r = zext i32 %ab to i64
  ret i64 %r
}

define i64 @nat_one_field() {
  %s = call {i32, i64} @one_field_poison()
  %a = extractvalue {i32, i64} %s, 0
  %r = zext i32 %a to i64
  ret i64 %r
}

define i64 @nat_nested_poison() {
  %s = call {{i32, i32}, i32} @nested_poison_loaded()
  %a = extractvalue {{i32, i32}, i32} %s, 1
  %r = zext i32 %a to i64
  ret i64 %r
}

define i64 @nat_vec_in_struct() {
  %s = call {i32, <2 x i32>} @vec_in_struct()
  %a = extractvalue {i32, <2 x i32>} %s, 0
  %r = zext i32 %a to i64
  ret i64 %r
}

define i64 @nat_ignore_struct() {
  %r = call i64 @ignore_struct({i32, i64} poison)
  ret i64 %r
}

define i64 @nat_second_field() {
  %r = call i64 @second_field({i32, i64} {i32 poison, i64 7})
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_nat_zero_struct = private unnamed_addr constant [26 x i8] c"nat_zero_struct() = %lld\0A\00"
@fmt_nat_sum_struct = private unnamed_addr constant [25 x i8] c"nat_sum_struct() = %lld\0A\00"
@fmt_nat_zero_array = private unnamed_addr constant [25 x i8] c"nat_zero_array() = %lld\0A\00"
@fmt_nat_zero_vector = private unnamed_addr constant [26 x i8] c"nat_zero_vector() = %lld\0A\00"
@fmt_nat_zero_nested = private unnamed_addr constant [26 x i8] c"nat_zero_nested() = %lld\0A\00"
@fmt_nat_partly_zero = private unnamed_addr constant [26 x i8] c"nat_partly_zero() = %lld\0A\00"
@fmt_nat_one_field = private unnamed_addr constant [24 x i8] c"nat_one_field() = %lld\0A\00"
@fmt_nat_nested_poison = private unnamed_addr constant [28 x i8] c"nat_nested_poison() = %lld\0A\00"
@fmt_nat_vec_in_struct = private unnamed_addr constant [28 x i8] c"nat_vec_in_struct() = %lld\0A\00"
@fmt_nat_ignore_struct = private unnamed_addr constant [28 x i8] c"nat_ignore_struct() = %lld\0A\00"
@fmt_nat_second_field = private unnamed_addr constant [27 x i8] c"nat_second_field() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @nat_zero_struct()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_nat_zero_struct, i64 %v0)
  %v1 = call i64 @nat_sum_struct()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_nat_sum_struct, i64 %v1)
  %v2 = call i64 @nat_zero_array()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_nat_zero_array, i64 %v2)
  %v3 = call i64 @nat_zero_vector()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_nat_zero_vector, i64 %v3)
  %v4 = call i64 @nat_zero_nested()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_nat_zero_nested, i64 %v4)
  %v5 = call i64 @nat_partly_zero()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_nat_partly_zero, i64 %v5)
  %v6 = call i64 @nat_one_field()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_nat_one_field, i64 %v6)
  %v7 = call i64 @nat_nested_poison()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_nat_nested_poison, i64 %v7)
  %v8 = call i64 @nat_vec_in_struct()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_nat_vec_in_struct, i64 %v8)
  %v9 = call i64 @nat_ignore_struct()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_nat_ignore_struct, i64 %v9)
  %v10 = call i64 @nat_second_field()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_nat_second_field, i64 %v10)
  ret i32 0
}

; ASSERT EQ: i64 0 = call i64 @nat_zero_struct()
; ASSERT EQ: i64 5 = call i64 @nat_sum_struct()
; ASSERT EQ: i64 0 = call i64 @nat_zero_array()
; ASSERT EQ: i64 0 = call i64 @nat_zero_vector()
; ASSERT EQ: i64 0 = call i64 @nat_zero_nested()
; ASSERT EQ: i64 7 = call i64 @nat_partly_zero()
; ASSERT EQ: i64 1 = call i64 @nat_one_field()
; ASSERT EQ: i64 1 = call i64 @nat_nested_poison()
; ASSERT EQ: i64 1 = call i64 @nat_vec_in_struct()
; ASSERT EQ: i64 5 = call i64 @nat_ignore_struct()
; ASSERT EQ: i64 7 = call i64 @nat_second_field()
