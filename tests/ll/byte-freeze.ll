; Freezing values of the byte type.
;
; LangRef ('freeze'): "Values of the byte type are frozen on a per-bit
; basis."  A byte whose bits are partly poison therefore freezes to a byte
; with *no* poison bits: the poison bits become arbitrary-but-fixed bits and
; every other bit (integer or pointer) is unchanged.
;
; Vellvm's [freeze_base] (Semantics/Denotation.v) only draws a fresh value
; when the whole value is [DVALUE_Poison]; a [DVALUE_B] holding a
; [BYTE_Mixed] with some poison bits comes back unchanged, still poison
; wherever it is used.  The partial-poison tests below fail for that reason;
; the others are guards for the fix.
;
; The frozen bits are arbitrary, so every test only observes bits whose
; value is determined, keeping the output comparable with a native run.

; low byte defined, high byte uninitialized: after freeze the value is no
; longer poison, and its low byte is still 7
define i64 @freeze_partial_poison() {
  %p = alloca i16
  store i8 7, ptr %p
  %b = load b16, ptr %p
  %f = freeze b16 %b
  %i = bitcast b16 %f to i16
  %lo = and i16 %i, 255
  %r = zext i16 %lo to i64
  ret i64 %r
}

; same, with the defined byte on the high side and a wider type
define i64 @freeze_partial_poison_high() {
  %p = alloca i32
  %q = getelementptr i8, ptr %p, i64 3
  store i8 5, ptr %q
  %b = load b32, ptr %p
  %f = freeze b32 %b
  %i = bitcast b32 %f to i32
  %hi = lshr i32 %i, 24
  %r = zext i32 %hi to i64
  ret i64 %r
}

; all uses of one freeze observe the same bits, so x - x is 0 even though
; x's upper byte is arbitrary
define i64 @freeze_partial_poison_same_value() {
  %p = alloca i16
  store i8 7, ptr %p
  %b = load b16, ptr %p
  %f = freeze b16 %b
  %i = bitcast b16 %f to i16
  %j = bitcast b16 %f to i16
  %d = sub i16 %i, %j
  %r = zext i16 %d to i64
  ret i64 %r
}

; guard: freezing a fully defined byte is the identity
define i64 @freeze_defined() {
  %p = alloca i16
  store i16 4660, ptr %p
  %b = load b16, ptr %p
  %f = freeze b16 %b
  %i = bitcast b16 %f to i16
  %r = zext i16 %i to i64
  ret i64 %r
}

; guard: a fully uninitialized byte freezes to some defined value
define i64 @freeze_all_poison() {
  %p = alloca i16
  %b = load b16, ptr %p
  %f = freeze b16 %b
  %i = bitcast b16 %f to i16
  %z = and i16 %i, 0
  %r = zext i16 %z to i64
  ret i64 %r
}

; guard: per-bit freeze leaves pointer bits alone.  The low 8 bytes hold a
; pointer and the high 8 are uninitialized; after freeze, the low half must
; still be that pointer, provenance included, so it can be loaded through.
define i64 @freeze_keeps_pointer_bits() {
  %x = alloca i64
  store i64 42, ptr %x
  %s = alloca [2 x ptr]
  store ptr %x, ptr %s
  %b = load b128, ptr %s
  %f = freeze b128 %b
  %v = bitcast b128 %f to <2 x b64>
  %e = extractelement <2 x b64> %v, i32 0
  %q = bitcast b64 %e to ptr
  %r = load i64, ptr %q
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_freeze_partial_poison = private unnamed_addr constant [32 x i8] c"freeze_partial_poison() = %lld\0A\00"
@fmt_freeze_partial_poison_high = private unnamed_addr constant [37 x i8] c"freeze_partial_poison_high() = %lld\0A\00"
@fmt_freeze_partial_poison_same_value = private unnamed_addr constant [43 x i8] c"freeze_partial_poison_same_value() = %lld\0A\00"
@fmt_freeze_defined = private unnamed_addr constant [25 x i8] c"freeze_defined() = %lld\0A\00"
@fmt_freeze_all_poison = private unnamed_addr constant [28 x i8] c"freeze_all_poison() = %lld\0A\00"
@fmt_freeze_keeps_pointer_bits = private unnamed_addr constant [36 x i8] c"freeze_keeps_pointer_bits() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @freeze_partial_poison()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_partial_poison, i64 %v0)
  %v1 = call i64 @freeze_partial_poison_high()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_partial_poison_high, i64 %v1)
  %v2 = call i64 @freeze_partial_poison_same_value()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_partial_poison_same_value, i64 %v2)
  %v3 = call i64 @freeze_defined()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_defined, i64 %v3)
  %v4 = call i64 @freeze_all_poison()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_all_poison, i64 %v4)
  %v5 = call i64 @freeze_keeps_pointer_bits()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_keeps_pointer_bits, i64 %v5)
  ret i32 0
}

; ASSERT EQ: i64 7    = call i64 @freeze_partial_poison()
; ASSERT EQ: i64 5    = call i64 @freeze_partial_poison_high()
; ASSERT EQ: i64 0    = call i64 @freeze_partial_poison_same_value()
; ASSERT EQ: i64 4660 = call i64 @freeze_defined()
; ASSERT EQ: i64 0    = call i64 @freeze_all_poison()
; ASSERT EQ: i64 42   = call i64 @freeze_keeps_pointer_bits()
