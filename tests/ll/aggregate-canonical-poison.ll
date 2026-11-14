; The canonical form of poison at aggregate types.
;
; An aggregate all of whose fields are poison *is* the value poison, and an
; operation that produces one must return it in that form -- as loading
; all-poison bytes from memory already does.  An aggregate with no fields
; ({} or [0 x T]) is not poison: its one value is the empty aggregate.
; (tests/ll/vector-poison.ll has the corresponding checks for vectors.)
;
; The harness compares an aggregate-typed answer structurally, so these check
; the representation.  MOST OF THESE FAIL until struct/array literals,
; insertvalue, the nofpclass/!range rewrites, and the reader's treatment of
; empty types are made canonical; each case says what it currently returns.
;
; As in assert-aggregate-literals.ll, the `nat_*` functions reduce the
; defined results to an i64 so that the file can be run natively and diffed
; against clang.
;
; Generated tail: python3 tests/gen.py (print-all mode).

; ---------------------------------------------------------------- literals

; currently {poison, poison}
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @struct_literal()
define {i32, i32} @struct_literal() {
  ret {i32, i32} {i32 poison, i32 poison}
}

; currently <{poison, poison}>
; ASSERT EQ: <{i32, i32}> poison = call <{i32, i32}> @packed_literal()
define <{i32, i32}> @packed_literal() {
  ret <{i32, i32}> <{i32 poison, i32 poison}>
}

; currently [poison, poison]
; ASSERT EQ: [2 x i32] poison = call [2 x i32] @array_literal()
define [2 x i32] @array_literal() {
  ret [2 x i32] [i32 poison, i32 poison]
}

; the elements are canonical, the array is not: currently [poison, poison]
; ASSERT EQ: [2 x <2 x i32>] poison = call [2 x <2 x i32>] @array_of_vectors_literal()
define [2 x <2 x i32>] @array_of_vectors_literal() {
  ret [2 x <2 x i32>] [<2 x i32> <i32 poison, i32 poison>, <2 x i32> poison]
}

; one level down: currently {{poison, poison}, i32 1}
; ASSERT EQ: {{i32, i32}, i32} {{i32, i32} poison, i32 1} = call {{i32, i32}, i32} @nested_literal()
define {{i32, i32}, i32} @nested_literal() {
  ret {{i32, i32}, i32} {{i32, i32} {i32 poison, i32 poison}, i32 1}
}

; ... which extractvalue then hands out: currently {poison, poison}
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @nested_extract()
define {i32, i32} @nested_extract() {
  %r = extractvalue {{i32, i32}, i32} {{i32, i32} {i32 poison, i32 poison}, i32 1}, 0
  ret {i32, i32} %r
}

; a literal as an argument: currently {poison, poison}
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @id_struct({i32, i32} {i32 poison, i32 poison})
define {i32, i32} @id_struct({i32, i32} %s) {
  ret {i32, i32} %s
}

; (passes) memory already canonicalizes: store the literal, load poison
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @literal_through_memory()
define {i32, i32} @literal_through_memory() {
  %p = alloca {i32, i32}
  store {i32, i32} {i32 poison, i32 poison}, ptr %p
  %r = load {i32, i32}, ptr %p
  ret {i32, i32} %r
}

; ------------------------------------------------------------- insertvalue

; currently {poison, poison}
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @insert_poison_into_poison()
define {i32, i32} @insert_poison_into_poison() {
  %r = insertvalue {i32, i32} poison, i32 poison, 0
  ret {i32, i32} %r
}

; overwriting the only defined field: currently {poison, poison}
; ASSERT EQ: {i32, i32} poison = call {i32, i32} @insert_overwrite_struct(i32 3)
define {i32, i32} @insert_overwrite_struct(i32 %x) {
  %a = insertvalue {i32, i32} poison, i32 %x, 0
  %r = insertvalue {i32, i32} %a, i32 poison, 0
  ret {i32, i32} %r
}

; currently [poison, poison]
; ASSERT EQ: [2 x i32] poison = call [2 x i32] @insert_overwrite_array(i32 3)
define [2 x i32] @insert_overwrite_array(i32 %x) {
  %a = insertvalue [2 x i32] poison, i32 %x, 0
  %r = insertvalue [2 x i32] %a, i32 poison, 0
  ret [2 x i32] %r
}

; inserting into a poison array at an index other than 0: currently the
; result is one element short ([poison, 7]), and extracting index 2 is UB
; ASSERT EQ: [3 x i32] [i32 poison, i32 poison, i32 7] = call [3 x i32] @insert_array_last(i32 7)
define [3 x i32] @insert_array_last(i32 %x) {
  %r = insertvalue [3 x i32] poison, i32 %x, 2
  ret [3 x i32] %r
}

; ------------------------------------------- poison-producing annotations

; every lane is a NaN, so nofpclass(nan) makes every lane poison:
; currently <poison, poison>
; ASSERT EQ: <2 x float> poison = call <2 x float> @nofpclass_all_lanes()
define <2 x float> @nofpclass_callee(<2 x float> nofpclass(nan) %v) {
  ret <2 x float> %v
}
define <2 x float> @nofpclass_all_lanes() {
  %r = call <2 x float> @nofpclass_callee(<2 x float> <float 0x7FF8000000000000, float 0x7FF8000000000000>)
  ret <2 x float> %r
}

; every lane is out of range: currently <poison, poison>
; ASSERT EQ: <2 x i8> poison = call <2 x i8> @range_all_lanes()
define <2 x i8> @range_all_lanes() {
  %p = alloca <2 x i8>
  store <2 x i8> <i8 5, i8 6>, ptr %p
  %r = load <2 x i8>, ptr %p, !range !0
  ret <2 x i8> %r
}

; --------------------------------------------------------- empty aggregates

; (passes)
; ASSERT EQ: {} zeroinitializer = call {} @empty_struct()
define {} @empty_struct() {
  ret {} zeroinitializer
}

; (passes)
; ASSERT EQ: [0 x i32] zeroinitializer = call [0 x i32] @empty_array()
define [0 x i32] @empty_array() {
  ret [0 x i32] zeroinitializer
}

; there is no poison at an empty type: currently poison
; ASSERT EQ: {} zeroinitializer = call {} @empty_poison()
define {} @empty_poison() {
  ret {} poison
}

; reading zero bytes gives the empty value: currently poison
; ASSERT EQ: {} zeroinitializer = call {} @empty_loaded()
define {} @empty_loaded() {
  %p = alloca {}
  %r = load {}, ptr %p
  ret {} %r
}

; ... so it is well defined: currently UB (noundef violated)
; ASSERT EQ: i64 1 = call i64 @empty_noundef()
define i64 @empty_noundef_callee({} noundef %x) {
  ret i64 1
}
define i64 @empty_noundef() {
  %p = alloca {}
  %v = load {}, ptr %p
  %r = call i64 @empty_noundef_callee({} noundef %v)
  ret i64 %r
}

; an empty field inside a non-empty struct (a C flexible array member)
; survives a round trip through memory: currently {i32 5, poison}
; ASSERT EQ: {i32, [0 x i8]} {i32 5, [0 x i8] zeroinitializer} = call {i32, [0 x i8]} @flexible_member()
define {i32, [0 x i8]} @flexible_member() {
  %p = alloca {i32, [0 x i8]}
  store {i32, [0 x i8]} {i32 5, [0 x i8] zeroinitializer}, ptr %p
  %r = load {i32, [0 x i8]}, ptr %p
  ret {i32, [0 x i8]} %r
}

; currently {poison, i32 5}
; ASSERT EQ: {{}, i32} {{} zeroinitializer, i32 5} = call {{}, i32} @empty_field_first()
define {{}, i32} @empty_field_first() {
  %p = alloca {{}, i32}
  store {{}, i32} {{} zeroinitializer, i32 5}, ptr %p
  %r = load {{}, i32}, ptr %p
  ret {{}, i32} %r
}

; a struct whose only non-empty field is poison is poison (passes today,
; because the empty field reads as poison too)
; ASSERT EQ: {{}, i32} poison = call {{}, i32} @empty_field_uninit()
define {{}, i32} @empty_field_uninit() {
  %p = alloca {{}, i32}
  %r = load {{}, i32}, ptr %p
  ret {{}, i32} %r
}

; zero-sized but not field-less: currently poison
; ASSERT EQ: {{}} zeroinitializer = call {{}} @nested_empty()
define {{}} @nested_empty() {
  %p = alloca {{}}
  store {{}} zeroinitializer, ptr %p
  %r = load {{}}, ptr %p
  ret {{}} %r
}

; currently poison
; ASSERT EQ: [2 x {}] zeroinitializer = call [2 x {}] @array_of_empty()
define [2 x {}] @array_of_empty() {
  %p = alloca [2 x {}]
  store [2 x {}] zeroinitializer, ptr %p
  %r = load [2 x {}], ptr %p
  ret [2 x {}] %r
}

!0 = !{i8 0, i8 2}

; ----------------------------------------------- the defined results, as i64

; currently UB: see @insert_array_last
define i64 @nat_insert_array_last() {
  %a = call [3 x i32] @insert_array_last(i32 7)
  %x = extractvalue [3 x i32] %a, 2
  %r = zext i32 %x to i64
  ret i64 %r
}

define i64 @nat_nested_literal() {
  %s = call {{i32, i32}, i32} @nested_literal()
  %x = extractvalue {{i32, i32}, i32} %s, 1
  %r = zext i32 %x to i64
  ret i64 %r
}

define i64 @nat_flexible_member() {
  %s = call {i32, [0 x i8]} @flexible_member()
  %x = extractvalue {i32, [0 x i8]} %s, 0
  %r = zext i32 %x to i64
  ret i64 %r
}

define i64 @nat_empty_field_first() {
  %s = call {{}, i32} @empty_field_first()
  %x = extractvalue {{}, i32} %s, 1
  %r = zext i32 %x to i64
  ret i64 %r
}

; currently UB: see @empty_noundef
define i64 @nat_empty_noundef() {
  %r = call i64 @empty_noundef()
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_nat_insert_array_last = private unnamed_addr constant [32 x i8] c"nat_insert_array_last() = %lld\0A\00"
@fmt_nat_nested_literal = private unnamed_addr constant [29 x i8] c"nat_nested_literal() = %lld\0A\00"
@fmt_nat_flexible_member = private unnamed_addr constant [30 x i8] c"nat_flexible_member() = %lld\0A\00"
@fmt_nat_empty_field_first = private unnamed_addr constant [32 x i8] c"nat_empty_field_first() = %lld\0A\00"
@fmt_nat_empty_noundef = private unnamed_addr constant [28 x i8] c"nat_empty_noundef() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @nat_insert_array_last()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_nat_insert_array_last, i64 %v0)
  %v1 = call i64 @nat_nested_literal()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_nat_nested_literal, i64 %v1)
  %v2 = call i64 @nat_flexible_member()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_nat_flexible_member, i64 %v2)
  %v3 = call i64 @nat_empty_field_first()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_nat_empty_field_first, i64 %v3)
  %v4 = call i64 @nat_empty_noundef()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_nat_empty_noundef, i64 %v4)
  ret i32 0
}

; ASSERT EQ: i64 7 = call i64 @nat_insert_array_last()
; ASSERT EQ: i64 1 = call i64 @nat_nested_literal()
; ASSERT EQ: i64 5 = call i64 @nat_flexible_member()
; ASSERT EQ: i64 5 = call i64 @nat_empty_field_first()
; ASSERT EQ: i64 1 = call i64 @nat_empty_noundef()
