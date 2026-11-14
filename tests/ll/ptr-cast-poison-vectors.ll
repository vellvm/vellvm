; ptrtoint / inttoptr on vectors with poison.
;
; A vector all of whose lanes are poison is the value poison (see
; vector-poison.ll and aggregate-canonical-poison.ll), so the casts between
; pointer and integer vectors must accept that form as their operand, and
; return it when every result lane is poison.  They used to accept only a
; vector written out lane by lane: `ptrtoint <2 x ptr> poison to <2 x i64>`
; failed with "convert_impure: type mismatch".
;
; The vector-typed assertions check the representation of the result.  The
; `nat_*` functions reduce the defined results to an i64, so that the file
; can be run natively and diffed against clang; a poison result is frozen
; and masked away.
;
; Generated tail: python3 tests/gen.py (print-all mode).

; ---------------------------------------------------------------- ptrtoint

; ASSERT EQ: <2 x i64> poison = call <2 x i64> @p2i_poison_constant()
define <2 x i64> @p2i_poison_constant() {
  %r = ptrtoint <2 x ptr> poison to <2 x i64>
  ret <2 x i64> %r
}

; the operand written lane by lane is the same value
; ASSERT EQ: <2 x i64> poison = call <2 x i64> @p2i_poison_lanes()
define <2 x i64> @p2i_poison_lanes() {
  %r = ptrtoint <2 x ptr> <ptr poison, ptr poison> to <2 x i64>
  ret <2 x i64> %r
}

; an uninitialized vector of pointers, read from memory
; ASSERT EQ: <2 x i64> poison = call <2 x i64> @p2i_uninit_load()
define <2 x i64> @p2i_uninit_load() {
  %s = alloca <2 x ptr>
  %v = load <2 x ptr>, ptr %s
  %r = ptrtoint <2 x ptr> %v to <2 x i64>
  ret <2 x i64> %r
}

; to a narrower integer
; ASSERT EQ: <2 x i32> poison = call <2 x i32> @p2i_poison_narrow()
define <2 x i32> @p2i_poison_narrow() {
  %r = ptrtoint <2 x ptr> poison to <2 x i32>
  ret <2 x i32> %r
}

; one poison lane: the other lane converts
; ASSERT EQ: <2 x i64> <i64 poison, i64 0> = call <2 x i64> @p2i_one_poison_lane()
define <2 x i64> @p2i_one_poison_lane() {
  %r = ptrtoint <2 x ptr> <ptr poison, ptr null> to <2 x i64>
  ret <2 x i64> %r
}

; ---------------------------------------------------------------- inttoptr

; there and back: both casts take the poison form
; ASSERT EQ: <2 x i64> poison = call <2 x i64> @i2p_poison_constant()
define <2 x i64> @i2p_poison_constant() {
  %p = inttoptr <2 x i64> poison to <2 x ptr>
  %r = ptrtoint <2 x ptr> %p to <2 x i64>
  ret <2 x i64> %r
}

; ASSERT EQ: <2 x i64> poison = call <2 x i64> @i2p_poison_lanes()
define <2 x i64> @i2p_poison_lanes() {
  %p = inttoptr <2 x i64> <i64 poison, i64 poison> to <2 x ptr>
  %r = ptrtoint <2 x ptr> %p to <2 x i64>
  ret <2 x i64> %r
}

; an operation whose every lane overflows produces the poison form
; ASSERT EQ: <2 x i64> poison = call <2 x i64> @i2p_computed_poison()
define <2 x i64> @i2p_computed_poison() {
  %s = add nuw <2 x i64> <i64 -1, i64 -1>, <i64 1, i64 1>
  %p = inttoptr <2 x i64> %s to <2 x ptr>
  %r = ptrtoint <2 x ptr> %p to <2 x i64>
  ret <2 x i64> %r
}

; one poison lane: the other lane survives the round trip
; ASSERT EQ: <2 x i64> <i64 poison, i64 8> = call <2 x i64> @i2p_one_poison_lane()
define <2 x i64> @i2p_one_poison_lane() {
  %p = inttoptr <2 x i64> <i64 poison, i64 8> to <2 x ptr>
  %r = ptrtoint <2 x ptr> %p to <2 x i64>
  ret <2 x i64> %r
}

; a poison vector of pointers can be passed and returned
; ASSERT EQ: <2 x i64> poison = call <2 x i64> @i2p_through_call()
define <2 x ptr> @id_ptrs(<2 x ptr> %v) {
  ret <2 x ptr> %v
}
define <2 x i64> @i2p_through_call() {
  %p = inttoptr <2 x i64> poison to <2 x ptr>
  %q = call <2 x ptr> @id_ptrs(<2 x ptr> %p)
  %r = ptrtoint <2 x ptr> %q to <2 x i64>
  ret <2 x i64> %r
}

; ----------------------------------------------- the defined results, as i64

; the cast does not trap: the poison result is frozen and masked away
define i64 @nat_p2i_poison() {
  %v = call <2 x i64> @p2i_poison_constant()
  %f = freeze <2 x i64> %v
  %x = extractelement <2 x i64> %f, i32 0
  %r = and i64 %x, 0
  ret i64 %r
}

define i64 @nat_i2p_poison() {
  %v = call <2 x i64> @i2p_poison_constant()
  %f = freeze <2 x i64> %v
  %x = extractelement <2 x i64> %f, i32 1
  %r = and i64 %x, 0
  ret i64 %r
}

define i64 @nat_p2i_defined_lane() {
  %v = call <2 x i64> @p2i_one_poison_lane()
  %r = extractelement <2 x i64> %v, i32 1
  ret i64 %r
}

define i64 @nat_i2p_defined_lane() {
  %v = call <2 x i64> @i2p_one_poison_lane()
  %r = extractelement <2 x i64> %v, i32 1
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_nat_p2i_poison = private unnamed_addr constant [25 x i8] c"nat_p2i_poison() = %lld\0A\00"
@fmt_nat_i2p_poison = private unnamed_addr constant [25 x i8] c"nat_i2p_poison() = %lld\0A\00"
@fmt_nat_p2i_defined_lane = private unnamed_addr constant [31 x i8] c"nat_p2i_defined_lane() = %lld\0A\00"
@fmt_nat_i2p_defined_lane = private unnamed_addr constant [31 x i8] c"nat_i2p_defined_lane() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @nat_p2i_poison()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_nat_p2i_poison, i64 %v0)
  %v1 = call i64 @nat_i2p_poison()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_nat_i2p_poison, i64 %v1)
  %v2 = call i64 @nat_p2i_defined_lane()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_nat_p2i_defined_lane, i64 %v2)
  %v3 = call i64 @nat_i2p_defined_lane()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_nat_i2p_defined_lane, i64 %v3)
  ret i32 0
}

; ASSERT EQ: i64 0 = call i64 @nat_p2i_poison()
; ASSERT EQ: i64 0 = call i64 @nat_i2p_poison()
; ASSERT EQ: i64 0 = call i64 @nat_p2i_defined_lane()
; ASSERT EQ: i64 8 = call i64 @nat_i2p_defined_lane()
