; Poison in vectors.
;
; LangRef: poison propagates lane by lane through vector operations -- an
; element-wise operation (binary operators, icmp/fcmp, select with a vector
; condition, casts, freeze) produces a poison lane exactly where an input
; lane is poison (or where that lane alone overflows an nsw/nuw/exact flag),
; and leaves the other lanes defined.  extractelement/insertelement with an
; out-of-range or poison index give poison; a poison shufflevector mask
; element gives a poison lane.  Floating-point division by poison is poison,
; not UB (only *integer* division by poison is UB, see tests/ub/udiv.ll).
;
; Two representations of an all-poison vector reach the operations:
;   - the constant `<4 x i32> poison` (and `undef`), and a load of memory
;     whose bytes are all poison, both give the scalar DVALUE_Poison;
;   - `<i32 poison, i32 poison, ...>` and lane-wise results give a vector of
;     poison lanes.
; Every operation must accept both.  Many cases below exist to push the
; scalar form through each vector operation (see notes/vector-poison.md on
; the mocha branch: `add <4 x i32> %v, poison` raised "eval_iop called on
; illegal dvalue").
;
; Most cases return an i64 that depends only on defined lanes (or on a
; frozen value), so the file runs natively and its output can be diffed
; against clang.  Cases whose answer *is* poison carry a hand-written
; `ASSERT EQ: i64 poison` next to their definition and are not printed by
; @main; their expected answers were checked with llubi, which reports
; "resulted in poison return value".  Memory that should be all poison is
; written with an explicit `store ... poison` rather than left uninitialized,
; because llubi reads uninitialized memory as undef bytes, not poison.

; ---------------------------------------------------------------- constants

define i64 @extract_defined_lane_of_partial_literal() {
  %e = extractelement <4 x i32> <i32 1, i32 poison, i32 3, i32 poison>, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @extract_poison_lane_of_partial_literal()
define i64 @extract_poison_lane_of_partial_literal() {
  %e = extractelement <4 x i32> <i32 1, i32 poison, i32 3, i32 poison>, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @extract_from_poison_constant()
define i64 @extract_from_poison_constant() {
  %e = extractelement <4 x i32> poison, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @insert_into_poison_constant() {
  %v = insertelement <4 x i32> poison, i32 5, i32 1
  %e = extractelement <4 x i32> %v, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @insert_into_undef_constant() {
  %v = insertelement <4 x i32> undef, i32 5, i32 1
  %e = extractelement <4 x i32> %v, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; the usual way clang builds a vector: insert every lane into poison
define i64 @build_vector_from_poison() {
  %v0 = insertelement <4 x i32> poison, i32 1, i32 0
  %v1 = insertelement <4 x i32> %v0, i32 2, i32 1
  %v2 = insertelement <4 x i32> %v1, i32 3, i32 2
  %v3 = insertelement <4 x i32> %v2, i32 4, i32 3
  %s  = add <4 x i32> %v3, <i32 10, i32 20, i32 30, i32 40>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e3 = extractelement <4 x i32> %s, i32 3
  %t  = add i32 %e0, %e3
  %r  = zext i32 %t to i64
  ret i64 %r
}

; ... and a splat: insert into lane 0 of poison, shuffle with a zero mask
define i64 @splat_via_shuffle() {
  %v = insertelement <4 x i32> poison, i32 7, i32 0
  %s = shufflevector <4 x i32> %v, <4 x i32> poison, <4 x i32> zeroinitializer
  %t = mul <4 x i32> %s, <i32 1, i32 2, i32 3, i32 4>
  %e = extractelement <4 x i32> %t, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

; ------------------------------------------------------ integer binary ops

; the scalar-poison vector as an operand: every lane of %s is poison, and
; overwriting one lane makes it defined again
define i64 @add_poison_constant_then_insert() {
  %s = add <4 x i32> <i32 1, i32 2, i32 3, i32 4>, poison
  %t = insertelement <4 x i32> %s, i32 9, i32 0
  %e = extractelement <4 x i32> %t, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @add_poison_constant_left_then_insert() {
  %s = add <4 x i32> poison, <i32 1, i32 2, i32 3, i32 4>
  %t = insertelement <4 x i32> %s, i32 9, i32 2
  %e = extractelement <4 x i32> %t, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @add_poison_constant_lane()
define i64 @add_poison_constant_lane() {
  %s = add <4 x i32> <i32 1, i32 2, i32 3, i32 4>, poison
  %e = extractelement <4 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @add_partial_poison_defined_lane() {
  %s = add <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, <i32 10, i32 20, i32 30, i32 40>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e3 = extractelement <4 x i32> %s, i32 3
  %t = add i32 %e0, %e3
  %r = zext i32 %t to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @add_partial_poison_poison_lane()
define i64 @add_partial_poison_poison_lane() {
  %s = add <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, <i32 10, i32 20, i32 30, i32 40>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; nsw overflow poisons only the lane that overflows
define i64 @add_nsw_overflow_one_lane() {
  %s = add nsw <2 x i32> <i32 2147483647, i32 1>, <i32 1, i32 1>
  %e = extractelement <2 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @add_nsw_overflow_lane_is_poison()
define i64 @add_nsw_overflow_lane_is_poison() {
  %s = add nsw <2 x i32> <i32 2147483647, i32 1>, <i32 1, i32 1>
  %e = extractelement <2 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; every lane overflows: an all-poison vector computed lane by lane, used again
define i64 @add_nsw_overflow_all_lanes_then_reuse() {
  %s = add nsw <2 x i32> <i32 2147483647, i32 2147483647>, <i32 1, i32 1>
  %t = add <2 x i32> %s, <i32 1, i32 1>
  %u = insertelement <2 x i32> %t, i32 7, i32 1
  %e = extractelement <2 x i32> %u, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; a shift amount >= the bit width poisons that lane only
define i64 @shl_oversized_amount_one_lane() {
  %s = shl <2 x i32> <i32 1, i32 1>, <i32 3, i32 40>
  %e = extractelement <2 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @shl_oversized_amount_lane_is_poison()
define i64 @shl_oversized_amount_lane_is_poison() {
  %s = shl <2 x i32> <i32 1, i32 1>, <i32 3, i32 40>
  %e = extractelement <2 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; poison is not absorbed by `and 0` / `or -1` / `mul 0`
; ASSERT EQ: i64 poison = call i64 @and_poison_constant_with_zero()
define i64 @and_poison_constant_with_zero() {
  %s = and <4 x i32> poison, zeroinitializer
  %e = extractelement <4 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @mul_poison_lane_by_zero()
define i64 @mul_poison_lane_by_zero() {
  %s = mul <2 x i32> <i32 poison, i32 5>, zeroinitializer
  %e = extractelement <2 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @bitwise_ops_on_poison_constant_then_insert() {
  %a = and <4 x i32> poison, <i32 1, i32 2, i32 3, i32 4>
  %o = or  <4 x i32> %a, poison
  %x = xor <4 x i32> poison, %o
  %l = lshr <4 x i32> %x, <i32 1, i32 1, i32 1, i32 1>
  %t = insertelement <4 x i32> %l, i32 11, i32 3
  %e = extractelement <4 x i32> %t, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

; integer division: a poison lane in the dividend gives a poison lane; the
; divisor here has no poison lane (a poison divisor lane is UB)
define i64 @udiv_poison_dividend_lane() {
  %s = udiv <2 x i32> <i32 poison, i32 8>, <i32 2, i32 2>
  %e = extractelement <2 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @udiv_poison_constant_dividend_then_insert() {
  %s = udiv <2 x i32> poison, <i32 2, i32 2>
  %t = insertelement <2 x i32> %s, i32 3, i32 0
  %e = extractelement <2 x i32> %t, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; -------------------------------------------------------------- comparisons

define i64 @icmp_partial_poison_defined_lane() {
  %c = icmp slt <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, <i32 2, i32 2, i32 2, i32 2>
  %e0 = extractelement <4 x i1> %c, i32 0
  %e2 = extractelement <4 x i1> %c, i32 2
  %z0 = zext i1 %e0 to i64
  %z2 = zext i1 %e2 to i64
  %r = add i64 %z0, %z2
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @icmp_partial_poison_poison_lane()
define i64 @icmp_partial_poison_poison_lane() {
  %c = icmp slt <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, <i32 2, i32 2, i32 2, i32 2>
  %e = extractelement <4 x i1> %c, i32 1
  %r = zext i1 %e to i64
  ret i64 %r
}

define i64 @icmp_poison_constant_then_insert() {
  %c = icmp eq <4 x i32> <i32 1, i32 2, i32 3, i32 4>, poison
  %d = insertelement <4 x i1> %c, i1 true, i32 2
  %e = extractelement <4 x i1> %d, i32 2
  %r = zext i1 %e to i64
  ret i64 %r
}

; ------------------------------------------------------------------- select

; a poison lane of a vector condition poisons that lane only
define i64 @select_poison_condition_lane() {
  %s = select <4 x i1> <i1 true, i1 poison, i1 false, i1 true>,
              <4 x i32> <i32 1, i32 2, i32 3, i32 4>,
              <4 x i32> <i32 10, i32 20, i32 30, i32 40>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e2 = extractelement <4 x i32> %s, i32 2
  %e3 = extractelement <4 x i32> %s, i32 3
  %t0 = add i32 %e0, %e2
  %t1 = add i32 %t0, %e3
  %r = zext i32 %t1 to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @select_poison_condition_lane_is_poison()
define i64 @select_poison_condition_lane_is_poison() {
  %s = select <4 x i1> <i1 true, i1 poison, i1 false, i1 true>,
              <4 x i32> <i32 1, i32 2, i32 3, i32 4>,
              <4 x i32> <i32 10, i32 20, i32 30, i32 40>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; poison in the lanes select does not choose is harmless
define i64 @select_unchosen_poison_operand() {
  %s = select <4 x i1> <i1 false, i1 false, i1 true, i1 false>,
              <4 x i32> poison,
              <4 x i32> <i32 10, i32 20, i32 30, i32 40>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @select_unchosen_poison_lane() {
  %s = select <2 x i1> <i1 true, i1 false>,
              <2 x i32> <i32 1, i32 poison>,
              <2 x i32> <i32 poison, i32 2>
  %e0 = extractelement <2 x i32> %s, i32 0
  %e1 = extractelement <2 x i32> %s, i32 1
  %t = add i32 %e0, %e1
  %r = zext i32 %t to i64
  ret i64 %r
}

; a scalar condition picks a whole vector, poison lanes and all
define i64 @select_scalar_condition_vector_operands() {
  %s = select i1 true, <2 x i32> <i32 1, i32 poison>, <2 x i32> poison
  %e = extractelement <2 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @select_scalar_poison_condition()
define i64 @select_scalar_poison_condition() {
  %s = select i1 poison, <2 x i32> <i32 1, i32 2>, <2 x i32> <i32 1, i32 2>
  %e = extractelement <2 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; an all-poison vector condition (the scalar poison form), then a lane
; of the result overwritten
define i64 @select_poison_constant_condition_then_insert() {
  %s = select <2 x i1> poison, <2 x i32> <i32 1, i32 2>, <2 x i32> <i32 3, i32 4>
  %t = add <2 x i32> %s, <i32 1, i32 1>
  %u = insertelement <2 x i32> %t, i32 6, i32 0
  %e = extractelement <2 x i32> %u, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; -------------------------------------------------------------------- memory

define i64 @store_partial_poison_load_defined_lane() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %e = extractelement <4 x i32> %v, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @store_partial_poison_load_poison_lane()
define i64 @store_partial_poison_load_poison_lane() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %e = extractelement <4 x i32> %v, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @store_partial_poison_load_scalar() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> <i32 1, i32 poison, i32 3, i32 4>, ptr %p, align 16
  %q = getelementptr i32, ptr %p, i64 3
  %e = load i32, ptr %q, align 4
  %r = zext i32 %e to i64
  ret i64 %r
}

; a poison vector, one lane then overwritten through a scalar store
define i64 @store_poison_vector_overwrite_lane() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %q = getelementptr i32, ptr %p, i64 1
  store i32 6, ptr %q, align 4
  %v = load <4 x i32>, ptr %p, align 16
  %s = add <4 x i32> %v, <i32 1, i32 1, i32 1, i32 1>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; the mocha repro: an all-poison vector load used by a vector add
define i64 @load_all_poison_add() {
  %b = alloca <4 x i32>, align 16
  %c = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %b, align 16
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %c, align 16
  %vb = load <4 x i32>, ptr %b, align 16
  %vc = load <4 x i32>, ptr %c, align 16
  %s = add nsw <4 x i32> %vc, %vb
  %t = insertelement <4 x i32> %s, i32 7, i32 0
  %e = extractelement <4 x i32> %t, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ... the same with the memory left uninitialized (Vellvm reads it as poison;
; the inserted lane makes the answer independent of what is there)
define i64 @load_uninitialized_add() {
  %b = alloca <4 x i32>, align 16
  %vb = load <4 x i32>, ptr %b, align 16
  %s = add nsw <4 x i32> <i32 1, i32 2, i32 3, i32 4>, %vb
  %t = insertelement <4 x i32> %s, i32 7, i32 0
  %e = extractelement <4 x i32> %t, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @load_all_poison_extract()
define i64 @load_all_poison_extract() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %e = extractelement <4 x i32> %v, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

; a vector of poison lanes written lane-wise reads back as all poison
define i64 @store_poison_lanes_load_add() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> <i32 poison, i32 poison, i32 poison, i32 poison>, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %s = sub <4 x i32> %v, <i32 1, i32 2, i32 3, i32 4>
  %t = insertelement <4 x i32> %s, i32 8, i32 3
  %e = extractelement <4 x i32> %t, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @load_all_poison_icmp_select() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %c = icmp sgt <4 x i32> %v, zeroinitializer
  %d = insertelement <4 x i1> %c, i1 false, i32 1
  %s = select <4 x i1> %d, <4 x i32> %v, <4 x i32> <i32 10, i32 20, i32 30, i32 40>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; a poison <4 x i1> condition loaded from memory
define i64 @load_all_poison_condition() {
  %p = alloca <4 x i1>, align 1
  store <4 x i1> poison, ptr %p, align 1
  %c = load <4 x i1>, ptr %p, align 1
  %s = select <4 x i1> %c, <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32> zeroinitializer
  %t = or <4 x i32> %s, <i32 1, i32 1, i32 1, i32 1>
  %u = insertelement <4 x i32> %t, i32 12, i32 2
  %e = extractelement <4 x i32> %u, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @load_all_poison_shuffle_defined_lanes() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %s = shufflevector <4 x i32> %v, <4 x i32> <i32 1, i32 2, i32 3, i32 4>,
                     <4 x i32> <i32 4, i32 5, i32 0, i32 7>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e3 = extractelement <4 x i32> %s, i32 3
  %t = add i32 %e0, %e3
  %r = zext i32 %t to i64
  ret i64 %r
}

define i64 @load_all_poison_casts_then_insert() {
  %p = alloca <4 x i16>, align 8
  store <4 x i16> poison, ptr %p, align 8
  %v = load <4 x i16>, ptr %p, align 8
  %z = zext <4 x i16> %v to <4 x i32>
  %s = add <4 x i32> %z, <i32 1, i32 1, i32 1, i32 1>
  %b = bitcast <4 x i32> %s to <2 x i64>
  %t = insertelement <2 x i64> %b, i64 13, i32 1
  %e = extractelement <2 x i64> %t, i32 1
  ret i64 %e
}

define i64 @load_all_poison_store_back_overwrite() {
  %p = alloca <4 x i32>, align 16
  %q = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  store <4 x i32> %v, ptr %q, align 16
  %q2 = getelementptr i32, ptr %q, i64 2
  store i32 14, ptr %q2, align 4
  %w = load <4 x i32>, ptr %q, align 16
  %e = extractelement <4 x i32> %w, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ---------------------------------------------------------------- casts

define i64 @zext_partial_poison() {
  %z = zext <4 x i8> <i8 1, i8 poison, i8 3, i8 200> to <4 x i32>
  %e = extractelement <4 x i32> %z, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @sext_partial_poison() {
  %z = sext <2 x i8> <i8 poison, i8 -3> to <2 x i64>
  %e = extractelement <2 x i64> %z, i32 1
  %r = add i64 %e, 10
  ret i64 %r
}

define i64 @trunc_partial_poison() {
  %t = trunc <2 x i32> <i32 poison, i32 258> to <2 x i8>
  %e = extractelement <2 x i8> %t, i32 1
  %r = zext i8 %e to i64
  ret i64 %r
}

define i64 @zext_poison_constant_then_add() {
  %z = zext <4 x i8> poison to <4 x i32>
  %s = add <4 x i32> %z, <i32 1, i32 2, i32 3, i32 4>
  %t = insertelement <4 x i32> %s, i32 15, i32 1
  %e = extractelement <4 x i32> %t, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; a vector-to-vector bitcast: a destination lane is poison when any of the
; source bits it covers is poison; lane 1 here is built only from 3 and 4
define i64 @bitcast_partial_poison_defined_lane() {
  %b = bitcast <4 x i32> <i32 1, i32 poison, i32 3, i32 4> to <2 x i64>
  %e = extractelement <2 x i64> %b, i32 1
  ret i64 %e
}

; ASSERT EQ: i64 poison = call i64 @bitcast_partial_poison_poison_lane()
define i64 @bitcast_partial_poison_poison_lane() {
  %b = bitcast <4 x i32> <i32 1, i32 poison, i32 3, i32 4> to <2 x i64>
  %e = extractelement <2 x i64> %b, i32 0
  ret i64 %e
}

define i64 @bitcast_partial_poison_bytes_to_i16_lanes() {
  %b = bitcast <4 x i8> <i8 1, i8 2, i8 poison, i8 4> to <2 x i16>
  %e = extractelement <2 x i16> %b, i32 0
  %r = zext i16 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @bitcast_partial_poison_vector_to_scalar()
define i64 @bitcast_partial_poison_vector_to_scalar() {
  %b = bitcast <2 x i32> <i32 1, i32 poison> to i64
  ret i64 %b
}

define i64 @bitcast_scalar_poison_to_vector_then_insert() {
  %b = bitcast i64 poison to <2 x i32>
  %s = add <2 x i32> %b, <i32 1, i32 1>
  %t = insertelement <2 x i32> %s, i32 16, i32 0
  %e = extractelement <2 x i32> %t, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @sitofp_fptosi_partial_poison() {
  %f = sitofp <2 x i32> <i32 poison, i32 7> to <2 x double>
  %g = fmul <2 x double> %f, <double 2.0, double 2.0>
  %i = fptosi <2 x double> %g to <2 x i32>
  %e = extractelement <2 x i32> %i, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; ------------------------------------------------------------- shufflevector

; a poison (or undef) mask element gives a poison lane; the other lanes are
; picked as usual
define i64 @shuffle_poison_mask_element() {
  %s = shufflevector <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32> <i32 5, i32 6, i32 7, i32 8>,
                     <4 x i32> <i32 7, i32 poison, i32 0, i32 undef>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e2 = extractelement <4 x i32> %s, i32 2
  %t = add i32 %e0, %e2
  %r = zext i32 %t to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @shuffle_poison_mask_element_lane()
define i64 @shuffle_poison_mask_element_lane() {
  %s = shufflevector <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32> <i32 5, i32 6, i32 7, i32 8>,
                     <4 x i32> <i32 7, i32 poison, i32 0, i32 undef>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @shuffle_from_poison_operand() {
  %s = shufflevector <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32> poison,
                     <4 x i32> <i32 3, i32 6, i32 1, i32 0>
  %e = extractelement <4 x i32> %s, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @shuffle_picks_poison_operand_lane()
define i64 @shuffle_picks_poison_operand_lane() {
  %s = shufflevector <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32> poison,
                     <4 x i32> <i32 3, i32 6, i32 1, i32 0>
  %e = extractelement <4 x i32> %s, i32 1
  %r = zext i32 %e to i64
  ret i64 %r
}

; a shuffle that changes the length, from a partial-poison vector
define i64 @shuffle_widen_partial_poison() {
  %s = shufflevector <2 x i32> <i32 poison, i32 9>, <2 x i32> poison,
                     <4 x i32> <i32 1, i32 1, i32 0, i32 3>
  %e0 = extractelement <4 x i32> %s, i32 0
  %e1 = extractelement <4 x i32> %s, i32 1
  %t = add i32 %e0, %e1
  %r = zext i32 %t to i64
  ret i64 %r
}

; --------------------------------------------- extractelement / insertelement

; ASSERT EQ: i64 poison = call i64 @extract_out_of_range_index()
define i64 @extract_out_of_range_index() {
  %e = extractelement <4 x i32> <i32 1, i32 2, i32 3, i32 4>, i32 4
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @extract_poison_index()
define i64 @extract_poison_index() {
  %e = extractelement <4 x i32> <i32 1, i32 2, i32 3, i32 4>, i32 poison
  %r = zext i32 %e to i64
  ret i64 %r
}

; an out-of-range insert makes the whole result poison
; ASSERT EQ: i64 poison = call i64 @insert_out_of_range_index()
define i64 @insert_out_of_range_index() {
  %v = insertelement <4 x i32> <i32 1, i32 2, i32 3, i32 4>, i32 5, i32 4
  %e = extractelement <4 x i32> %v, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @insert_poison_index()
define i64 @insert_poison_index() {
  %v = insertelement <4 x i32> <i32 1, i32 2, i32 3, i32 4>, i32 5, i32 poison
  %e = extractelement <4 x i32> %v, i32 0
  %r = zext i32 %e to i64
  ret i64 %r
}

; inserting a poison element poisons that lane only
define i64 @insert_poison_element() {
  %v = insertelement <4 x i32> <i32 1, i32 2, i32 3, i32 4>, i32 poison, i32 1
  %e = extractelement <4 x i32> %v, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ------------------------------------------------------------------- freeze

define i64 @freeze_keeps_defined_lanes() {
  %f = freeze <4 x i32> <i32 1, i32 poison, i32 3, i32 4>
  %e = extractelement <4 x i32> %f, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; a frozen lane is some fixed value: x - x = 0
define i64 @freeze_poison_lane_is_stable() {
  %f = freeze <4 x i32> <i32 1, i32 poison, i32 3, i32 4>
  %e = extractelement <4 x i32> %f, i32 1
  %d = sub i32 %e, %e
  %r = zext i32 %d to i64
  ret i64 %r
}

define i64 @freeze_poison_constant() {
  %f = freeze <4 x i32> poison
  %x = xor <4 x i32> %f, %f
  %e = extractelement <4 x i32> %x, i32 3
  %r = zext i32 %e to i64
  ret i64 %r
}

define i64 @freeze_loaded_all_poison() {
  %p = alloca <4 x i32>, align 16
  store <4 x i32> poison, ptr %p, align 16
  %v = load <4 x i32>, ptr %p, align 16
  %f = freeze <4 x i32> %v
  %d = sub <4 x i32> %f, %f
  %s = add <4 x i32> %d, <i32 1, i32 2, i32 3, i32 4>
  %e = extractelement <4 x i32> %s, i32 2
  %r = zext i32 %e to i64
  ret i64 %r
}

; ----------------------------------------------------------- floating point

define i64 @fadd_partial_poison_defined_lane() {
  %s = fadd <2 x double> <double 1.0, double poison>, <double 2.0, double 2.0>
  %e = extractelement <2 x double> %s, i32 0
  %r = fptosi double %e to i64
  ret i64 %r
}

define i64 @fadd_poison_constant_then_insert() {
  %s = fadd <2 x double> poison, <double 2.0, double 2.0>
  %t = insertelement <2 x double> %s, double 17.0, i32 1
  %e = extractelement <2 x double> %t, i32 1
  %r = fptosi double %e to i64
  ret i64 %r
}

; floating-point division by poison is poison, not UB
define i64 @fdiv_by_poison_lane() {
  %s = fdiv <2 x double> <double 1.0, double 8.0>, <double poison, double 2.0>
  %e = extractelement <2 x double> %s, i32 1
  %r = fptosi double %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @fdiv_by_poison_lane_is_poison()
define i64 @fdiv_by_poison_lane_is_poison() {
  %s = fdiv <2 x double> <double 1.0, double 8.0>, <double poison, double 2.0>
  %e = extractelement <2 x double> %s, i32 0
  %r = fptosi double %e to i64
  ret i64 %r
}

define i64 @fdiv_by_poison_constant_then_insert() {
  %s = fdiv <2 x float> <float 1.0, float 8.0>, poison
  %t = insertelement <2 x float> %s, float 18.0, i32 0
  %e = extractelement <2 x float> %t, i32 0
  %r = fptosi float %e to i64
  ret i64 %r
}

define i64 @fcmp_partial_poison_defined_lane() {
  %c = fcmp olt <2 x float> <float poison, float 1.0>, <float 2.0, float 2.0>
  %e = extractelement <2 x i1> %c, i32 1
  %r = zext i1 %e to i64
  ret i64 %r
}

define i64 @fcmp_poison_constant_then_insert() {
  %c = fcmp oeq <2 x float> poison, <float 2.0, float 2.0>
  %d = insertelement <2 x i1> %c, i1 true, i32 0
  %e = extractelement <2 x i1> %d, i32 0
  %r = zext i1 %e to i64
  ret i64 %r
}

define i64 @fneg_poison_constant_then_insert() {
  %n = fneg <2 x double> poison
  %t = insertelement <2 x double> %n, double -19.0, i32 1
  %u = fneg <2 x double> %t
  %e = extractelement <2 x double> %u, i32 1
  %r = fptosi double %e to i64
  ret i64 %r
}

; ----------------------------------------------------------- canonical form
;
; A vector whose lanes are all poison is the value poison: an operation
; whose every result lane is poison returns it in that form.  (The harness
; compares a vector-typed `poison` answer syntactically, so these check the
; representation, not just the lanes.)

; ASSERT EQ: <2 x i32> poison = call <2 x i32> @canon_add_nsw_all_lanes_overflow()
define <2 x i32> @canon_add_nsw_all_lanes_overflow() {
  %s = add nsw <2 x i32> <i32 2147483647, i32 2147483647>, <i32 1, i32 1>
  ret <2 x i32> %s
}

; ASSERT EQ: <2 x i32> poison = call <2 x i32> @canon_poison_lanes_literal()
define <2 x i32> @canon_poison_lanes_literal() {
  ret <2 x i32> <i32 poison, i32 poison>
}

; ASSERT EQ: <2 x i1> poison = call <2 x i1> @canon_icmp_poison_constant()
define <2 x i1> @canon_icmp_poison_constant() {
  %c = icmp eq <2 x i32> <i32 1, i32 2>, poison
  ret <2 x i1> %c
}

; ASSERT EQ: <2 x i32> poison = call <2 x i32> @canon_select_poison_lanes()
define <2 x i32> @canon_select_poison_lanes() {
  %s = select <2 x i1> <i1 true, i1 poison>, <2 x i32> <i32 poison, i32 1>, <2 x i32> <i32 2, i32 3>
  ret <2 x i32> %s
}

; ASSERT EQ: <2 x i32> poison = call <2 x i32> @canon_shuffle_poison_lanes()
define <2 x i32> @canon_shuffle_poison_lanes() {
  %s = shufflevector <2 x i32> <i32 1, i32 poison>, <2 x i32> poison, <2 x i32> <i32 1, i32 poison>
  ret <2 x i32> %s
}

; ASSERT EQ: <2 x i32> poison = call <2 x i32> @canon_insert_poison_into_poison()
define <2 x i32> @canon_insert_poison_into_poison() {
  %v = insertelement <2 x i32> poison, i32 poison, i32 0
  ret <2 x i32> %v
}

; ASSERT EQ: <2 x i64> poison = call <2 x i64> @canon_zext_poison_lanes()
define <2 x i64> @canon_zext_poison_lanes() {
  %z = zext <2 x i32> <i32 poison, i32 poison> to <2 x i64>
  ret <2 x i64> %z
}

; ASSERT EQ: <2 x double> poison = call <2 x double> @canon_fneg_poison_lanes()
define <2 x double> @canon_fneg_poison_lanes() {
  %n = fneg <2 x double> <double poison, double poison>
  ret <2 x double> %n
}

; ASSERT EQ: <2 x double> poison = call <2 x double> @canon_fdiv_by_poison()
define <2 x double> @canon_fdiv_by_poison() {
  %d = fdiv <2 x double> <double 1.0, double 2.0>, poison
  ret <2 x double> %d
}

; a defined lane keeps the vector a vector
; ASSERT EQ: <2 x i32> <i32 3, i32 poison> = call <2 x i32> @canon_one_defined_lane()
define <2 x i32> @canon_one_defined_lane() {
  %s = add nsw <2 x i32> <i32 2, i32 2147483647>, <i32 1, i32 1>
  ret <2 x i32> %s
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_extract_defined_lane_of_partial_literal = private unnamed_addr constant [50 x i8] c"extract_defined_lane_of_partial_literal() = %lld\0A\00"
@fmt_insert_into_poison_constant = private unnamed_addr constant [38 x i8] c"insert_into_poison_constant() = %lld\0A\00"
@fmt_insert_into_undef_constant = private unnamed_addr constant [37 x i8] c"insert_into_undef_constant() = %lld\0A\00"
@fmt_build_vector_from_poison = private unnamed_addr constant [35 x i8] c"build_vector_from_poison() = %lld\0A\00"
@fmt_splat_via_shuffle = private unnamed_addr constant [28 x i8] c"splat_via_shuffle() = %lld\0A\00"
@fmt_add_poison_constant_then_insert = private unnamed_addr constant [42 x i8] c"add_poison_constant_then_insert() = %lld\0A\00"
@fmt_add_poison_constant_left_then_insert = private unnamed_addr constant [47 x i8] c"add_poison_constant_left_then_insert() = %lld\0A\00"
@fmt_add_partial_poison_defined_lane = private unnamed_addr constant [42 x i8] c"add_partial_poison_defined_lane() = %lld\0A\00"
@fmt_add_nsw_overflow_one_lane = private unnamed_addr constant [36 x i8] c"add_nsw_overflow_one_lane() = %lld\0A\00"
@fmt_add_nsw_overflow_all_lanes_then_reuse = private unnamed_addr constant [48 x i8] c"add_nsw_overflow_all_lanes_then_reuse() = %lld\0A\00"
@fmt_shl_oversized_amount_one_lane = private unnamed_addr constant [40 x i8] c"shl_oversized_amount_one_lane() = %lld\0A\00"
@fmt_bitwise_ops_on_poison_constant_then_insert = private unnamed_addr constant [53 x i8] c"bitwise_ops_on_poison_constant_then_insert() = %lld\0A\00"
@fmt_udiv_poison_dividend_lane = private unnamed_addr constant [36 x i8] c"udiv_poison_dividend_lane() = %lld\0A\00"
@fmt_udiv_poison_constant_dividend_then_insert = private unnamed_addr constant [52 x i8] c"udiv_poison_constant_dividend_then_insert() = %lld\0A\00"
@fmt_icmp_partial_poison_defined_lane = private unnamed_addr constant [43 x i8] c"icmp_partial_poison_defined_lane() = %lld\0A\00"
@fmt_icmp_poison_constant_then_insert = private unnamed_addr constant [43 x i8] c"icmp_poison_constant_then_insert() = %lld\0A\00"
@fmt_select_poison_condition_lane = private unnamed_addr constant [39 x i8] c"select_poison_condition_lane() = %lld\0A\00"
@fmt_select_unchosen_poison_operand = private unnamed_addr constant [41 x i8] c"select_unchosen_poison_operand() = %lld\0A\00"
@fmt_select_unchosen_poison_lane = private unnamed_addr constant [38 x i8] c"select_unchosen_poison_lane() = %lld\0A\00"
@fmt_select_scalar_condition_vector_operands = private unnamed_addr constant [50 x i8] c"select_scalar_condition_vector_operands() = %lld\0A\00"
@fmt_select_poison_constant_condition_then_insert = private unnamed_addr constant [55 x i8] c"select_poison_constant_condition_then_insert() = %lld\0A\00"
@fmt_store_partial_poison_load_defined_lane = private unnamed_addr constant [49 x i8] c"store_partial_poison_load_defined_lane() = %lld\0A\00"
@fmt_store_partial_poison_load_scalar = private unnamed_addr constant [43 x i8] c"store_partial_poison_load_scalar() = %lld\0A\00"
@fmt_store_poison_vector_overwrite_lane = private unnamed_addr constant [45 x i8] c"store_poison_vector_overwrite_lane() = %lld\0A\00"
@fmt_load_all_poison_add = private unnamed_addr constant [30 x i8] c"load_all_poison_add() = %lld\0A\00"
@fmt_load_uninitialized_add = private unnamed_addr constant [33 x i8] c"load_uninitialized_add() = %lld\0A\00"
@fmt_store_poison_lanes_load_add = private unnamed_addr constant [38 x i8] c"store_poison_lanes_load_add() = %lld\0A\00"
@fmt_load_all_poison_icmp_select = private unnamed_addr constant [38 x i8] c"load_all_poison_icmp_select() = %lld\0A\00"
@fmt_load_all_poison_condition = private unnamed_addr constant [36 x i8] c"load_all_poison_condition() = %lld\0A\00"
@fmt_load_all_poison_shuffle_defined_lanes = private unnamed_addr constant [48 x i8] c"load_all_poison_shuffle_defined_lanes() = %lld\0A\00"
@fmt_load_all_poison_casts_then_insert = private unnamed_addr constant [44 x i8] c"load_all_poison_casts_then_insert() = %lld\0A\00"
@fmt_load_all_poison_store_back_overwrite = private unnamed_addr constant [47 x i8] c"load_all_poison_store_back_overwrite() = %lld\0A\00"
@fmt_zext_partial_poison = private unnamed_addr constant [30 x i8] c"zext_partial_poison() = %lld\0A\00"
@fmt_sext_partial_poison = private unnamed_addr constant [30 x i8] c"sext_partial_poison() = %lld\0A\00"
@fmt_trunc_partial_poison = private unnamed_addr constant [31 x i8] c"trunc_partial_poison() = %lld\0A\00"
@fmt_zext_poison_constant_then_add = private unnamed_addr constant [40 x i8] c"zext_poison_constant_then_add() = %lld\0A\00"
@fmt_bitcast_partial_poison_defined_lane = private unnamed_addr constant [46 x i8] c"bitcast_partial_poison_defined_lane() = %lld\0A\00"
@fmt_bitcast_partial_poison_bytes_to_i16_lanes = private unnamed_addr constant [52 x i8] c"bitcast_partial_poison_bytes_to_i16_lanes() = %lld\0A\00"
@fmt_bitcast_scalar_poison_to_vector_then_insert = private unnamed_addr constant [54 x i8] c"bitcast_scalar_poison_to_vector_then_insert() = %lld\0A\00"
@fmt_sitofp_fptosi_partial_poison = private unnamed_addr constant [39 x i8] c"sitofp_fptosi_partial_poison() = %lld\0A\00"
@fmt_shuffle_poison_mask_element = private unnamed_addr constant [38 x i8] c"shuffle_poison_mask_element() = %lld\0A\00"
@fmt_shuffle_from_poison_operand = private unnamed_addr constant [38 x i8] c"shuffle_from_poison_operand() = %lld\0A\00"
@fmt_shuffle_widen_partial_poison = private unnamed_addr constant [39 x i8] c"shuffle_widen_partial_poison() = %lld\0A\00"
@fmt_insert_poison_element = private unnamed_addr constant [32 x i8] c"insert_poison_element() = %lld\0A\00"
@fmt_freeze_keeps_defined_lanes = private unnamed_addr constant [37 x i8] c"freeze_keeps_defined_lanes() = %lld\0A\00"
@fmt_freeze_poison_lane_is_stable = private unnamed_addr constant [39 x i8] c"freeze_poison_lane_is_stable() = %lld\0A\00"
@fmt_freeze_poison_constant = private unnamed_addr constant [33 x i8] c"freeze_poison_constant() = %lld\0A\00"
@fmt_freeze_loaded_all_poison = private unnamed_addr constant [35 x i8] c"freeze_loaded_all_poison() = %lld\0A\00"
@fmt_fadd_partial_poison_defined_lane = private unnamed_addr constant [43 x i8] c"fadd_partial_poison_defined_lane() = %lld\0A\00"
@fmt_fadd_poison_constant_then_insert = private unnamed_addr constant [43 x i8] c"fadd_poison_constant_then_insert() = %lld\0A\00"
@fmt_fdiv_by_poison_lane = private unnamed_addr constant [30 x i8] c"fdiv_by_poison_lane() = %lld\0A\00"
@fmt_fdiv_by_poison_constant_then_insert = private unnamed_addr constant [46 x i8] c"fdiv_by_poison_constant_then_insert() = %lld\0A\00"
@fmt_fcmp_partial_poison_defined_lane = private unnamed_addr constant [43 x i8] c"fcmp_partial_poison_defined_lane() = %lld\0A\00"
@fmt_fcmp_poison_constant_then_insert = private unnamed_addr constant [43 x i8] c"fcmp_poison_constant_then_insert() = %lld\0A\00"
@fmt_fneg_poison_constant_then_insert = private unnamed_addr constant [43 x i8] c"fneg_poison_constant_then_insert() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @extract_defined_lane_of_partial_literal()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_extract_defined_lane_of_partial_literal, i64 %v0)
  %v1 = call i64 @insert_into_poison_constant()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_insert_into_poison_constant, i64 %v1)
  %v2 = call i64 @insert_into_undef_constant()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_insert_into_undef_constant, i64 %v2)
  %v3 = call i64 @build_vector_from_poison()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_build_vector_from_poison, i64 %v3)
  %v4 = call i64 @splat_via_shuffle()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_splat_via_shuffle, i64 %v4)
  %v5 = call i64 @add_poison_constant_then_insert()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_add_poison_constant_then_insert, i64 %v5)
  %v6 = call i64 @add_poison_constant_left_then_insert()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_add_poison_constant_left_then_insert, i64 %v6)
  %v7 = call i64 @add_partial_poison_defined_lane()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_add_partial_poison_defined_lane, i64 %v7)
  %v8 = call i64 @add_nsw_overflow_one_lane()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_add_nsw_overflow_one_lane, i64 %v8)
  %v9 = call i64 @add_nsw_overflow_all_lanes_then_reuse()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_add_nsw_overflow_all_lanes_then_reuse, i64 %v9)
  %v10 = call i64 @shl_oversized_amount_one_lane()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_shl_oversized_amount_one_lane, i64 %v10)
  %v11 = call i64 @bitwise_ops_on_poison_constant_then_insert()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_bitwise_ops_on_poison_constant_then_insert, i64 %v11)
  %v12 = call i64 @udiv_poison_dividend_lane()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_udiv_poison_dividend_lane, i64 %v12)
  %v13 = call i64 @udiv_poison_constant_dividend_then_insert()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_udiv_poison_constant_dividend_then_insert, i64 %v13)
  %v14 = call i64 @icmp_partial_poison_defined_lane()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_icmp_partial_poison_defined_lane, i64 %v14)
  %v15 = call i64 @icmp_poison_constant_then_insert()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_icmp_poison_constant_then_insert, i64 %v15)
  %v16 = call i64 @select_poison_condition_lane()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_select_poison_condition_lane, i64 %v16)
  %v17 = call i64 @select_unchosen_poison_operand()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_select_unchosen_poison_operand, i64 %v17)
  %v18 = call i64 @select_unchosen_poison_lane()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_select_unchosen_poison_lane, i64 %v18)
  %v19 = call i64 @select_scalar_condition_vector_operands()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_select_scalar_condition_vector_operands, i64 %v19)
  %v20 = call i64 @select_poison_constant_condition_then_insert()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_select_poison_constant_condition_then_insert, i64 %v20)
  %v21 = call i64 @store_partial_poison_load_defined_lane()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_store_partial_poison_load_defined_lane, i64 %v21)
  %v22 = call i64 @store_partial_poison_load_scalar()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_store_partial_poison_load_scalar, i64 %v22)
  %v23 = call i64 @store_poison_vector_overwrite_lane()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_store_poison_vector_overwrite_lane, i64 %v23)
  %v24 = call i64 @load_all_poison_add()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_add, i64 %v24)
  %v25 = call i64 @load_uninitialized_add()
  %p25 = call i32 (ptr, ...) @printf(ptr @fmt_load_uninitialized_add, i64 %v25)
  %v26 = call i64 @store_poison_lanes_load_add()
  %p26 = call i32 (ptr, ...) @printf(ptr @fmt_store_poison_lanes_load_add, i64 %v26)
  %v27 = call i64 @load_all_poison_icmp_select()
  %p27 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_icmp_select, i64 %v27)
  %v28 = call i64 @load_all_poison_condition()
  %p28 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_condition, i64 %v28)
  %v29 = call i64 @load_all_poison_shuffle_defined_lanes()
  %p29 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_shuffle_defined_lanes, i64 %v29)
  %v30 = call i64 @load_all_poison_casts_then_insert()
  %p30 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_casts_then_insert, i64 %v30)
  %v31 = call i64 @load_all_poison_store_back_overwrite()
  %p31 = call i32 (ptr, ...) @printf(ptr @fmt_load_all_poison_store_back_overwrite, i64 %v31)
  %v32 = call i64 @zext_partial_poison()
  %p32 = call i32 (ptr, ...) @printf(ptr @fmt_zext_partial_poison, i64 %v32)
  %v33 = call i64 @sext_partial_poison()
  %p33 = call i32 (ptr, ...) @printf(ptr @fmt_sext_partial_poison, i64 %v33)
  %v34 = call i64 @trunc_partial_poison()
  %p34 = call i32 (ptr, ...) @printf(ptr @fmt_trunc_partial_poison, i64 %v34)
  %v35 = call i64 @zext_poison_constant_then_add()
  %p35 = call i32 (ptr, ...) @printf(ptr @fmt_zext_poison_constant_then_add, i64 %v35)
  %v36 = call i64 @bitcast_partial_poison_defined_lane()
  %p36 = call i32 (ptr, ...) @printf(ptr @fmt_bitcast_partial_poison_defined_lane, i64 %v36)
  %v37 = call i64 @bitcast_partial_poison_bytes_to_i16_lanes()
  %p37 = call i32 (ptr, ...) @printf(ptr @fmt_bitcast_partial_poison_bytes_to_i16_lanes, i64 %v37)
  %v38 = call i64 @bitcast_scalar_poison_to_vector_then_insert()
  %p38 = call i32 (ptr, ...) @printf(ptr @fmt_bitcast_scalar_poison_to_vector_then_insert, i64 %v38)
  %v39 = call i64 @sitofp_fptosi_partial_poison()
  %p39 = call i32 (ptr, ...) @printf(ptr @fmt_sitofp_fptosi_partial_poison, i64 %v39)
  %v40 = call i64 @shuffle_poison_mask_element()
  %p40 = call i32 (ptr, ...) @printf(ptr @fmt_shuffle_poison_mask_element, i64 %v40)
  %v41 = call i64 @shuffle_from_poison_operand()
  %p41 = call i32 (ptr, ...) @printf(ptr @fmt_shuffle_from_poison_operand, i64 %v41)
  %v42 = call i64 @shuffle_widen_partial_poison()
  %p42 = call i32 (ptr, ...) @printf(ptr @fmt_shuffle_widen_partial_poison, i64 %v42)
  %v43 = call i64 @insert_poison_element()
  %p43 = call i32 (ptr, ...) @printf(ptr @fmt_insert_poison_element, i64 %v43)
  %v44 = call i64 @freeze_keeps_defined_lanes()
  %p44 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_keeps_defined_lanes, i64 %v44)
  %v45 = call i64 @freeze_poison_lane_is_stable()
  %p45 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_poison_lane_is_stable, i64 %v45)
  %v46 = call i64 @freeze_poison_constant()
  %p46 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_poison_constant, i64 %v46)
  %v47 = call i64 @freeze_loaded_all_poison()
  %p47 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_loaded_all_poison, i64 %v47)
  %v48 = call i64 @fadd_partial_poison_defined_lane()
  %p48 = call i32 (ptr, ...) @printf(ptr @fmt_fadd_partial_poison_defined_lane, i64 %v48)
  %v49 = call i64 @fadd_poison_constant_then_insert()
  %p49 = call i32 (ptr, ...) @printf(ptr @fmt_fadd_poison_constant_then_insert, i64 %v49)
  %v50 = call i64 @fdiv_by_poison_lane()
  %p50 = call i32 (ptr, ...) @printf(ptr @fmt_fdiv_by_poison_lane, i64 %v50)
  %v51 = call i64 @fdiv_by_poison_constant_then_insert()
  %p51 = call i32 (ptr, ...) @printf(ptr @fmt_fdiv_by_poison_constant_then_insert, i64 %v51)
  %v52 = call i64 @fcmp_partial_poison_defined_lane()
  %p52 = call i32 (ptr, ...) @printf(ptr @fmt_fcmp_partial_poison_defined_lane, i64 %v52)
  %v53 = call i64 @fcmp_poison_constant_then_insert()
  %p53 = call i32 (ptr, ...) @printf(ptr @fmt_fcmp_poison_constant_then_insert, i64 %v53)
  %v54 = call i64 @fneg_poison_constant_then_insert()
  %p54 = call i32 (ptr, ...) @printf(ptr @fmt_fneg_poison_constant_then_insert, i64 %v54)
  ret i32 0
}

; ASSERT EQ: i64 3           = call i64 @extract_defined_lane_of_partial_literal()
; ASSERT EQ: i64 5           = call i64 @insert_into_poison_constant()
; ASSERT EQ: i64 5           = call i64 @insert_into_undef_constant()
; ASSERT EQ: i64 55          = call i64 @build_vector_from_poison()
; ASSERT EQ: i64 28          = call i64 @splat_via_shuffle()
; ASSERT EQ: i64 9           = call i64 @add_poison_constant_then_insert()
; ASSERT EQ: i64 9           = call i64 @add_poison_constant_left_then_insert()
; ASSERT EQ: i64 55          = call i64 @add_partial_poison_defined_lane()
; ASSERT EQ: i64 2           = call i64 @add_nsw_overflow_one_lane()
; ASSERT EQ: i64 7           = call i64 @add_nsw_overflow_all_lanes_then_reuse()
; ASSERT EQ: i64 8           = call i64 @shl_oversized_amount_one_lane()
; ASSERT EQ: i64 11          = call i64 @bitwise_ops_on_poison_constant_then_insert()
; ASSERT EQ: i64 4           = call i64 @udiv_poison_dividend_lane()
; ASSERT EQ: i64 3           = call i64 @udiv_poison_constant_dividend_then_insert()
; ASSERT EQ: i64 1           = call i64 @icmp_partial_poison_defined_lane()
; ASSERT EQ: i64 1           = call i64 @icmp_poison_constant_then_insert()
; ASSERT EQ: i64 35          = call i64 @select_poison_condition_lane()
; ASSERT EQ: i64 20          = call i64 @select_unchosen_poison_operand()
; ASSERT EQ: i64 3           = call i64 @select_unchosen_poison_lane()
; ASSERT EQ: i64 1           = call i64 @select_scalar_condition_vector_operands()
; ASSERT EQ: i64 6           = call i64 @select_poison_constant_condition_then_insert()
; ASSERT EQ: i64 3           = call i64 @store_partial_poison_load_defined_lane()
; ASSERT EQ: i64 4           = call i64 @store_partial_poison_load_scalar()
; ASSERT EQ: i64 7           = call i64 @store_poison_vector_overwrite_lane()
; ASSERT EQ: i64 7           = call i64 @load_all_poison_add()
; ASSERT EQ: i64 7           = call i64 @load_uninitialized_add()
; ASSERT EQ: i64 8           = call i64 @store_poison_lanes_load_add()
; ASSERT EQ: i64 20          = call i64 @load_all_poison_icmp_select()
; ASSERT EQ: i64 12          = call i64 @load_all_poison_condition()
; ASSERT EQ: i64 5           = call i64 @load_all_poison_shuffle_defined_lanes()
; ASSERT EQ: i64 13          = call i64 @load_all_poison_casts_then_insert()
; ASSERT EQ: i64 14          = call i64 @load_all_poison_store_back_overwrite()
; ASSERT EQ: i64 200         = call i64 @zext_partial_poison()
; ASSERT EQ: i64 7           = call i64 @sext_partial_poison()
; ASSERT EQ: i64 2           = call i64 @trunc_partial_poison()
; ASSERT EQ: i64 15          = call i64 @zext_poison_constant_then_add()
; ASSERT EQ: i64 17179869187 = call i64 @bitcast_partial_poison_defined_lane()
; ASSERT EQ: i64 513         = call i64 @bitcast_partial_poison_bytes_to_i16_lanes()
; ASSERT EQ: i64 16          = call i64 @bitcast_scalar_poison_to_vector_then_insert()
; ASSERT EQ: i64 14          = call i64 @sitofp_fptosi_partial_poison()
; ASSERT EQ: i64 9           = call i64 @shuffle_poison_mask_element()
; ASSERT EQ: i64 4           = call i64 @shuffle_from_poison_operand()
; ASSERT EQ: i64 18          = call i64 @shuffle_widen_partial_poison()
; ASSERT EQ: i64 3           = call i64 @insert_poison_element()
; ASSERT EQ: i64 3           = call i64 @freeze_keeps_defined_lanes()
; ASSERT EQ: i64 0           = call i64 @freeze_poison_lane_is_stable()
; ASSERT EQ: i64 0           = call i64 @freeze_poison_constant()
; ASSERT EQ: i64 3           = call i64 @freeze_loaded_all_poison()
; ASSERT EQ: i64 3           = call i64 @fadd_partial_poison_defined_lane()
; ASSERT EQ: i64 17          = call i64 @fadd_poison_constant_then_insert()
; ASSERT EQ: i64 4           = call i64 @fdiv_by_poison_lane()
; ASSERT EQ: i64 18          = call i64 @fdiv_by_poison_constant_then_insert()
; ASSERT EQ: i64 1           = call i64 @fcmp_partial_poison_defined_lane()
; ASSERT EQ: i64 1           = call i64 @fcmp_poison_constant_then_insert()
; ASSERT EQ: i64 19          = call i64 @fneg_poison_constant_then_insert()
