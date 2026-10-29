; UB tests involving the `getelementptr` instruction.
;
; `getelementptr` itself never raises immediate UB: violating `inbounds`,
; `nusw`, or `nuw` makes the *result* poison (LangRef getelementptr: "If any of
; the rules are violated, the result value is a poison value"), and the UB
; happens when that poison pointer is dereferenced (load/store: "If <pointer>
; is not a well-defined value, the behavior is undefined").
;
; LangRef (getelementptr, inbounds): "The base pointer has an in bounds address
; of the allocated object that it is based on ... During the successive
; addition of offsets to the address, the resulting pointer must remain in
; bounds of the allocated object at each step."  "the only pointer in bounds of
; the null pointer in the default address space is the null pointer itself."
; LangRef (getelementptr, inrange): "loading from or storing to any pointer
; derived from the getelementptr has undefined behavior if the load or store
; would access memory outside the half-open range [Start, End)".

@arr = global [4 x i32] [i32 10, i32 11, i32 12, i32 13]

; Control: an out-of-bounds gep *without* inbounds is not poison, and merely
; computing it (without dereferencing) is fine.
define i64 @gep_oob_no_deref() {
  %p = alloca [4 x i32]
  %q = getelementptr inbounds [4 x i32], ptr %p, i64 0, i64 100
  %i = ptrtoint ptr %q to i64
  ret i64 0
}

; ASSERT SUCCEEDS: call i64 @gep_oob_no_deref()

; Control: one-past-the-end is in bounds for `inbounds`.
define i32 @gep_inbounds_one_past_end() {
  %q = getelementptr inbounds [4 x i32], ptr @arr, i64 0, i64 4
  %r = getelementptr inbounds i32, ptr %q, i64 -1
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 13 = call i32 @gep_inbounds_one_past_end()

; Going out of bounds and coming back with `inbounds` at every step: the
; intermediate result is poison, so the final pointer is poison too, even
; though its address is in bounds.
define i32 @gep_inbounds_oob_and_back() {
  %q = getelementptr inbounds i32, ptr @arr, i64 5
  %r = getelementptr inbounds i32, ptr %q, i64 -5
  %v = load i32, ptr %r                           ; <- UB @gep_inbounds_oob_and_back
  ret i32 %v
}

; ASSERT UB 47: call i32 @gep_inbounds_oob_and_back()

; Same address computation without `inbounds` is well defined.
define i32 @gep_oob_and_back() {
  %q = getelementptr i32, ptr @arr, i64 5
  %r = getelementptr i32, ptr %q, i64 -5
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 10 = call i32 @gep_oob_and_back()

; Out of bounds of a heap/stack object in a single step.
define i32 @gep_inbounds_oob_load() {
  %p = alloca [2 x i32]
  store [2 x i32] [i32 1, i32 2], ptr %p
  %q = getelementptr inbounds i32, ptr %p, i64 3
  %r = getelementptr i32, ptr %q, i64 -2
  %v = load i32, ptr %r                           ; <- UB @gep_inbounds_oob_load
  ret i32 %v
}

; ASSERT UB 69: call i32 @gep_inbounds_oob_load()

; inbounds with a non-zero offset from null is poison.  (Any access through a
; null-based pointer is UB anyway, so observe the poison by branching on a
; comparison instead.)
define i32 @gep_inbounds_null() {
entry:
  %q = getelementptr inbounds i8, ptr null, i64 8
  %c = icmp eq ptr %q, null
  br i1 %c, label %t, label %f                    ; <- UB @gep_inbounds_null
t:
  ret i32 1
f:
  ret i32 0
}

; ASSERT UB 82: call i32 @gep_inbounds_null()

define i32 @gep_null_ok() {
entry:
  %q = getelementptr i8, ptr null, i64 8
  %c = icmp eq ptr %q, null
  br i1 %c, label %t, label %f
t:
  ret i32 1
f:
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @gep_null_ok()

; `nuw` with a negative offset (wraps in the unsigned sense) is poison.
define i32 @gep_nuw_negative() {
  %q = getelementptr [4 x i32], ptr @arr, i64 0, i64 2
  %r = getelementptr nuw i32, ptr %q, i64 -1
  %v = load i32, ptr %r                           ; <- UB @gep_nuw_negative
  ret i32 %v
}

; ASSERT UB 108: call i32 @gep_nuw_negative()

define i32 @gep_negative_ok() {
  %q = getelementptr [4 x i32], ptr @arr, i64 0, i64 2
  %r = getelementptr i32, ptr %q, i64 -1
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 11 = call i32 @gep_negative_ok()

; `nusw`: the multiplication of the index by the type size overflows i64 in
; a signed sense.
define i32 @gep_nusw_mul_overflow() {
  %q = getelementptr nusw i64, ptr @arr, i64 4611686018427387904
  %r = getelementptr i64, ptr %q, i64 -4611686018427387904
  %v = load i32, ptr %r                           ; <- UB @gep_nusw_mul_overflow
  ret i32 %v
}

; ASSERT UB 128: call i32 @gep_nusw_mul_overflow()

; A poison index makes the result poison.
define i32 @gep_poison_index(i64 %i) {
  %q = getelementptr i32, ptr @arr, i64 %i
  %v = load i32, ptr %q                           ; <- UB @gep_poison_index
  ret i32 %v
}

; ASSERT UB 137: call i32 @gep_poison_index(i64 poison)
; ASSERT EQ: i32 12 = call i32 @gep_poison_index(i64 2)

; NOTE: `inrange` (constant-expression gep only) is not covered: e.g.
;   load i32, ptr getelementptr inrange(0, 4) ([4 x i32], ptr @arr, i64 0, i64 0)
; would be fine, while accessing offset 4 from that result would be UB.

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 29): ASSERT SUCCEEDS: call i64 @gep_oob_no_deref()
define i64 @ub_case_0() {
  %r = call i64 @gep_oob_no_deref()
  ret i64 %r
}

; case 1 (line 39): ASSERT EQ: i32 13 = call i32 @gep_inbounds_one_past_end()
define i32 @ub_case_1() {
  %r = call i32 @gep_inbounds_one_past_end()
  ret i32 %r
}

; case 2 (line 51): ASSERT UB 47: call i32 @gep_inbounds_oob_and_back()
define i32 @ub_case_2() {
  %r = call i32 @gep_inbounds_oob_and_back()
  ret i32 %r
}

; case 3 (line 61): ASSERT EQ: i32 10 = call i32 @gep_oob_and_back()
define i32 @ub_case_3() {
  %r = call i32 @gep_oob_and_back()
  ret i32 %r
}

; case 4 (line 73): ASSERT UB 69: call i32 @gep_inbounds_oob_load()
define i32 @ub_case_4() {
  %r = call i32 @gep_inbounds_oob_load()
  ret i32 %r
}

; case 5 (line 89): ASSERT UB 82: call i32 @gep_inbounds_null()
define i32 @ub_case_5() {
  %r = call i32 @gep_inbounds_null()
  ret i32 %r
}

; case 6 (line 102): ASSERT EQ: i32 0 = call i32 @gep_null_ok()
define i32 @ub_case_6() {
  %r = call i32 @gep_null_ok()
  ret i32 %r
}

; case 7 (line 112): ASSERT UB 108: call i32 @gep_nuw_negative()
define i32 @ub_case_7() {
  %r = call i32 @gep_nuw_negative()
  ret i32 %r
}

; case 8 (line 121): ASSERT EQ: i32 11 = call i32 @gep_negative_ok()
define i32 @ub_case_8() {
  %r = call i32 @gep_negative_ok()
  ret i32 %r
}

; case 9 (line 132): ASSERT UB 128: call i32 @gep_nusw_mul_overflow()
define i32 @ub_case_9() {
  %r = call i32 @gep_nusw_mul_overflow()
  ret i32 %r
}

; case 10 (line 141): ASSERT UB 137: call i32 @gep_poison_index(i64 poison)
define i32 @ub_case_10() {
  %r = call i32 @gep_poison_index(i64 poison)
  ret i32 %r
}

; case 11 (line 142): ASSERT EQ: i32 12 = call i32 @gep_poison_index(i64 2)
define i32 @ub_case_11() {
  %r = call i32 @gep_poison_index(i64 2)
  ret i32 %r
}

@ub_fmt_start = private unnamed_addr constant [16 x i8] c"case %d: start\0A\00"
@ub_fmt_ret = private unnamed_addr constant [18 x i8] c"case %d: returned\00"
@ub_fmt_int = private unnamed_addr constant [6 x i8] c" %lld\00"
@ub_fmt_fp = private unnamed_addr constant [4 x i8] c" %g\00"
@ub_fmt_nl = private unnamed_addr constant [2 x i8] c"\0A\00"

declare i32 @printf(ptr, ...)
declare i32 @atoi(ptr)

define i32 @main(i32 %argc, ptr %argv) {
entry:
  %has_arg = icmp sge i32 %argc, 2
  br i1 %has_arg, label %dispatch, label %bad
dispatch:
  %arg1_p = getelementptr ptr, ptr %argv, i64 1
  %arg1 = load ptr, ptr %arg1_p
  %n = call i32 @atoi(ptr %arg1)
  switch i32 %n, label %bad [
    i32 0, label %case0
    i32 1, label %case1
    i32 2, label %case2
    i32 3, label %case3
    i32 4, label %case4
    i32 5, label %case5
    i32 6, label %case6
    i32 7, label %case7
    i32 8, label %case8
    i32 9, label %case9
    i32 10, label %case10
    i32 11, label %case11
  ]
case0:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 0)
  %c0_r = call i64 @ub_case_0()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c0_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case1:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 1)
  %c1_r = call i32 @ub_case_1()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 1)
  %c1_0 = sext i32 %c1_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c1_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case2:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 2)
  %c2_r = call i32 @ub_case_2()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 2)
  %c2_0 = sext i32 %c2_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c2_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case3:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 3)
  %c3_r = call i32 @ub_case_3()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 3)
  %c3_0 = sext i32 %c3_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c3_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case4:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 4)
  %c4_r = call i32 @ub_case_4()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 4)
  %c4_0 = sext i32 %c4_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c4_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case5:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 5)
  %c5_r = call i32 @ub_case_5()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 5)
  %c5_0 = sext i32 %c5_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c5_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case6:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 6)
  %c6_r = call i32 @ub_case_6()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 6)
  %c6_0 = sext i32 %c6_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c6_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case7:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 7)
  %c7_r = call i32 @ub_case_7()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 7)
  %c7_0 = sext i32 %c7_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c7_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case8:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 8)
  %c8_r = call i32 @ub_case_8()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 8)
  %c8_0 = sext i32 %c8_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c8_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case9:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 9)
  %c9_r = call i32 @ub_case_9()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 9)
  %c9_0 = sext i32 %c9_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c9_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case10:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 10)
  %c10_r = call i32 @ub_case_10()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 10)
  %c10_0 = sext i32 %c10_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c10_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case11:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 11)
  %c11_r = call i32 @ub_case_11()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 11)
  %c11_0 = sext i32 %c11_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c11_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
bad:
  ret i32 2
}
; ---- END executable tail ----
