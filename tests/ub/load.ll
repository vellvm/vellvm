; UB tests for the `load` instruction.
;
; LangRef (load, Semantics): "If <pointer> is not a well-defined value, the
; behavior is undefined."
; LangRef (load, Arguments): "Overestimating the alignment results in undefined
; behavior."
; LangRef (load, !noundef): "If the value isn't well defined, the behavior is
; undefined.  If the !noundef metadata is combined with poison-generating
; metadata like !nonnull, violation of that metadata constraint will also
; result in undefined behavior."
; LangRef (Pointer Aliasing Rules): "Any memory access must be done through a
; pointer value associated with an address range of the memory access,
; otherwise the behavior is undefined."  A null pointer is associated with no
; address.
; LangRef (Object Lifetime): "It is undefined behavior to access an allocated
; object that isn't alive" -- except that "loading from a stack object outside
; its lifetime is not undefined behavior and returns a poison value instead."
;
; Provenance-specific load cases live in provenance.ll; loads through pointers
; produced by out-of-bounds `getelementptr` live in getelementptr.ll.

declare ptr @malloc(i64)
declare void @free(ptr)
declare void @llvm.lifetime.start.p0(ptr captures(none))
declare void @llvm.lifetime.end.p0(ptr captures(none))

define i32 @load(ptr %p) {
  %v = load i32, ptr %p                           ; <- UB @load
  ret i32 %v
}

; ASSERT UB 28: call i32 @load(ptr null)
; ASSERT UB 28: call i32 @load(ptr poison)

define i32 @load_ok() {
  %p = alloca i32
  store i32 42, ptr %p
  %v = call i32 @load(ptr %p)
  ret i32 %v
}

; ASSERT EQ: i32 42 = call i32 @load_ok()

define i32 @load_undef_ptr() {
  %v = load i32, ptr undef                        ; <- UB @load_undef_ptr
  ret i32 %v
}

; ASSERT UB 45: call i32 @load_undef_ptr()

; Volatile and atomic loads are not exempt.
define i32 @load_volatile_null() {
  %v = load volatile i32, ptr null                ; <- UB @load_volatile_null
  ret i32 %v
}

; ASSERT UB 53: call i32 @load_volatile_null()

define i32 @load_atomic_null() {
  %v = load atomic i32, ptr null seq_cst, align 4 ; <- UB @load_atomic_null
  ret i32 %v
}

; ASSERT UB 60: call i32 @load_atomic_null()

; One past the end of an alloca (address computed without `inbounds`).
define i32 @load_past_end() {
  %p = alloca i32
  store i32 1, ptr %p
  %q = getelementptr i32, ptr %p, i64 1
  %v = load i32, ptr %q                           ; <- UB @load_past_end
  ret i32 %v
}

; ASSERT UB 71: call i32 @load_past_end()

; Partially out of bounds: an 8-byte read of a 4-byte object.
define i64 @load_partially_oob() {
  %p = alloca i32
  store i32 1, ptr %p
  %v = load i64, ptr %p                           ; <- UB @load_partially_oob
  ret i64 %v
}

; ASSERT UB 81: call i64 @load_partially_oob()

; Before the start of an object.
define i32 @load_before_start() {
  %p = alloca [2 x i32]
  store [2 x i32] [i32 1, i32 2], ptr %p
  %q = getelementptr i32, ptr %p, i64 -1
  %v = load i32, ptr %q                           ; <- UB @load_before_start
  ret i32 %v
}

; ASSERT UB 92: call i32 @load_before_start()

; Dangling stack pointer: the callee's frame has been popped.
define ptr @escape_local() {
  %p = alloca i32
  store i32 7, ptr %p
  ret ptr %p
}

define i32 @load_dangling_stack() {
  %p = call ptr @escape_local()
  %v = load i32, ptr %p                           ; <- UB @load_dangling_stack
  ret i32 %v
}

; ASSERT UB 107: call i32 @load_dangling_stack()

; Use after free.
define i32 @load_after_free() {
  %p = call ptr @malloc(i64 4)
  store i32 7, ptr %p
  call void @free(ptr %p)
  %v = load i32, ptr %p                           ; <- UB @load_after_free
  ret i32 %v
}

; ASSERT UB 118: call i32 @load_after_free()

define i32 @load_before_free() {
  %p = call ptr @malloc(i64 4)
  store i32 7, ptr %p
  %v = load i32, ptr %p
  call void @free(ptr %p)
  ret i32 %v
}

; ASSERT EQ: i32 7 = call i32 @load_before_free()

; Overestimated alignment: %q is only 4-byte aligned.
define i32 @load_misaligned() {
  %p = alloca [2 x i32], align 8
  store [2 x i32] [i32 1, i32 2], ptr %p
  %q = getelementptr i8, ptr %p, i64 4
  %v = load i32, ptr %q, align 8                  ; <- UB @load_misaligned
  ret i32 %v
}

; ASSERT UB 139: call i32 @load_misaligned()

define i32 @load_aligned_ok() {
  %p = alloca [2 x i32], align 8
  store [2 x i32] [i32 1, i32 2], ptr %p
  %q = getelementptr i8, ptr %p, i64 4
  %v = load i32, ptr %q, align 4
  ret i32 %v
}

; ASSERT EQ: i32 2 = call i32 @load_aligned_ok()

; A misaligned *byte* address with align 2.
define i16 @load_misaligned_odd() {
  %p = alloca [4 x i8], align 4
  store [4 x i8] [i8 1, i8 2, i8 3, i8 4], ptr %p
  %q = getelementptr i8, ptr %p, i64 1
  %v = load i16, ptr %q, align 2                  ; <- UB @load_misaligned_odd
  ret i16 %v
}

; ASSERT UB 160: call i16 @load_misaligned_odd()

; !noundef on a load of uninitialized memory.
define i32 @load_noundef_uninit() {
  %p = alloca i32
  %v = load i32, ptr %p, !noundef !0              ; <- UB @load_noundef_uninit
  ret i32 %v
}

; ASSERT UB 169: call i32 @load_noundef_uninit()

; !noundef on a load of a stored poison value.
define i32 @load_noundef_poison() {
  %p = alloca i32
  store i32 poison, ptr %p
  %v = load i32, ptr %p, !noundef !0              ; <- UB @load_noundef_poison
  ret i32 %v
}

; ASSERT UB 179: call i32 @load_noundef_poison()

; !noundef where only one byte of the loaded value is uninitialized.
define i32 @load_noundef_partial() {
  %p = alloca i32
  store i8 1, ptr %p
  %v = load i32, ptr %p, !noundef !0              ; <- UB @load_noundef_partial
  ret i32 %v
}

; ASSERT UB 189: call i32 @load_noundef_partial()

; !noundef on an aggregate with a poison field.
define { i32, i32 } @load_noundef_aggregate() {
  %p = alloca { i32, i32 }
  store { i32, i32 } { i32 1, i32 poison }, ptr %p
  %v = load { i32, i32 }, ptr %p, !noundef !0     ; <- UB @load_noundef_aggregate
  ret { i32, i32 } %v
}

; ASSERT UB 199: call { i32, i32 } @load_noundef_aggregate()

; Controls: without !noundef these loads produce poison, not UB.
define i32 @load_uninit() {
  %p = alloca i32
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 poison = call i32 @load_uninit()

define i32 @load_noundef_ok() {
  %p = alloca i32
  store i32 5, ptr %p
  %v = load i32, ptr %p, !noundef !0
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @load_noundef_ok()

; !nonnull + !noundef with a null value is UB ...
define i32 @load_nonnull_noundef_null() {
  %p = alloca ptr
  store ptr null, ptr %p
  %v = load ptr, ptr %p, !nonnull !0, !noundef !0 ; <- UB @load_nonnull_noundef_null
  ret i32 0
}

; ASSERT UB 227: call i32 @load_nonnull_noundef_null()

; ... but !nonnull alone only makes the loaded value poison.
define i64 @load_nonnull_null() {
  %p = alloca ptr
  store ptr null, ptr %p
  %v = load ptr, ptr %p, !nonnull !0
  %i = ptrtoint ptr %v to i64
  ret i64 %i
}

; ASSERT EQ: i64 poison = call i64 @load_nonnull_null()

; ... which is UB as soon as it is branched on.
define i32 @load_nonnull_null_branch() {
entry:
  %p = alloca ptr
  store ptr null, ptr %p
  %v = load ptr, ptr %p, !nonnull !0
  %c = icmp eq ptr %v, null
  br i1 %c, label %t, label %f                    ; <- UB @load_nonnull_null_branch
t:
  ret i32 1
f:
  ret i32 0
}

; ASSERT UB 251: call i32 @load_nonnull_null_branch()

; !align + !noundef with a misaligned pointer value is UB.
define i32 @load_align_md_noundef() {
  %a = alloca [2 x i32], align 8
  %q = getelementptr i8, ptr %a, i64 4
  %p = alloca ptr
  store ptr %q, ptr %p
  %v = load ptr, ptr %p, !align !1, !noundef !0   ; <- UB @load_align_md_noundef
  ret i32 0
}

; ASSERT UB 266: call i32 @load_align_md_noundef()

; !align alone yields poison.
define i64 @load_align_md() {
  %a = alloca [2 x i32], align 8
  %q = getelementptr i8, ptr %a, i64 4
  %p = alloca ptr
  store ptr %q, ptr %p
  %v = load ptr, ptr %p, !align !1
  %i = ptrtoint ptr %v to i64
  ret i64 %i
}

; ASSERT EQ: i64 poison = call i64 @load_align_md()

; NOTE: `!dereferenceable` / `!dereferenceable_or_null` load metadata ("the
; value loaded is known to be dereferenceable at the current program point,
; otherwise the behavior is undefined") does not currently parse in Vellvm
; (`dereferenceable` is lexed as a keyword).  The test would be:
;
;   store ptr null, ptr %p
;   %v = load ptr, ptr %p, !dereferenceable !2     ; UB, with !2 = !{i64 4}

; Lifetime: a stack object is dead before llvm.lifetime.start and after
; llvm.lifetime.end.  Loads from it are poison (not UB); see store.ll for the
; UB case.
define i32 @load_after_lifetime_end() {
  %p = alloca i32
  call void @llvm.lifetime.start.p0(ptr %p)
  store i32 1, ptr %p
  call void @llvm.lifetime.end.p0(ptr %p)
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 poison = call i32 @load_after_lifetime_end()

; ... but a load from a dead *heap* object is UB.  (Covered above by
; @load_after_free.)

!0 = !{}
!1 = !{i64 8}

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 32): ASSERT UB 28: call i32 @load(ptr null)
define i32 @ub_case_0() {
  %r = call i32 @load(ptr null)
  ret i32 %r
}

; case 1 (line 33): ASSERT UB 28: call i32 @load(ptr poison)
define i32 @ub_case_1() {
  %r = call i32 @load(ptr poison)
  ret i32 %r
}

; case 2 (line 42): ASSERT EQ: i32 42 = call i32 @load_ok()
define i32 @ub_case_2() {
  %r = call i32 @load_ok()
  ret i32 %r
}

; case 3 (line 49): ASSERT UB 45: call i32 @load_undef_ptr()
define i32 @ub_case_3() {
  %r = call i32 @load_undef_ptr()
  ret i32 %r
}

; case 4 (line 57): ASSERT UB 53: call i32 @load_volatile_null()
define i32 @ub_case_4() {
  %r = call i32 @load_volatile_null()
  ret i32 %r
}

; case 5 (line 64): ASSERT UB 60: call i32 @load_atomic_null()
define i32 @ub_case_5() {
  %r = call i32 @load_atomic_null()
  ret i32 %r
}

; case 6 (line 75): ASSERT UB 71: call i32 @load_past_end()
define i32 @ub_case_6() {
  %r = call i32 @load_past_end()
  ret i32 %r
}

; case 7 (line 85): ASSERT UB 81: call i64 @load_partially_oob()
define i64 @ub_case_7() {
  %r = call i64 @load_partially_oob()
  ret i64 %r
}

; case 8 (line 96): ASSERT UB 92: call i32 @load_before_start()
define i32 @ub_case_8() {
  %r = call i32 @load_before_start()
  ret i32 %r
}

; case 9 (line 111): ASSERT UB 107: call i32 @load_dangling_stack()
define i32 @ub_case_9() {
  %r = call i32 @load_dangling_stack()
  ret i32 %r
}

; case 10 (line 122): ASSERT UB 118: call i32 @load_after_free()
define i32 @ub_case_10() {
  %r = call i32 @load_after_free()
  ret i32 %r
}

; case 11 (line 132): ASSERT EQ: i32 7 = call i32 @load_before_free()
define i32 @ub_case_11() {
  %r = call i32 @load_before_free()
  ret i32 %r
}

; case 12 (line 143): ASSERT UB 139: call i32 @load_misaligned()
define i32 @ub_case_12() {
  %r = call i32 @load_misaligned()
  ret i32 %r
}

; case 13 (line 153): ASSERT EQ: i32 2 = call i32 @load_aligned_ok()
define i32 @ub_case_13() {
  %r = call i32 @load_aligned_ok()
  ret i32 %r
}

; case 14 (line 164): ASSERT UB 160: call i16 @load_misaligned_odd()
define i16 @ub_case_14() {
  %r = call i16 @load_misaligned_odd()
  ret i16 %r
}

; case 15 (line 173): ASSERT UB 169: call i32 @load_noundef_uninit()
define i32 @ub_case_15() {
  %r = call i32 @load_noundef_uninit()
  ret i32 %r
}

; case 16 (line 183): ASSERT UB 179: call i32 @load_noundef_poison()
define i32 @ub_case_16() {
  %r = call i32 @load_noundef_poison()
  ret i32 %r
}

; case 17 (line 193): ASSERT UB 189: call i32 @load_noundef_partial()
define i32 @ub_case_17() {
  %r = call i32 @load_noundef_partial()
  ret i32 %r
}

; case 18 (line 203): ASSERT UB 199: call { i32, i32 } @load_noundef_aggregate()
define { i32, i32 } @ub_case_18() {
  %r = call { i32, i32 } @load_noundef_aggregate()
  ret { i32, i32 } %r
}

; case 19 (line 212): ASSERT EQ: i32 poison = call i32 @load_uninit()
define i32 @ub_case_19() {
  %r = call i32 @load_uninit()
  ret i32 %r
}

; case 20 (line 221): ASSERT EQ: i32 5 = call i32 @load_noundef_ok()
define i32 @ub_case_20() {
  %r = call i32 @load_noundef_ok()
  ret i32 %r
}

; case 21 (line 231): ASSERT UB 227: call i32 @load_nonnull_noundef_null()
define i32 @ub_case_21() {
  %r = call i32 @load_nonnull_noundef_null()
  ret i32 %r
}

; case 22 (line 242): ASSERT EQ: i64 poison = call i64 @load_nonnull_null()
define i64 @ub_case_22() {
  %r = call i64 @load_nonnull_null()
  ret i64 %r
}

; case 23 (line 258): ASSERT UB 251: call i32 @load_nonnull_null_branch()
define i32 @ub_case_23() {
  %r = call i32 @load_nonnull_null_branch()
  ret i32 %r
}

; case 24 (line 270): ASSERT UB 266: call i32 @load_align_md_noundef()
define i32 @ub_case_24() {
  %r = call i32 @load_align_md_noundef()
  ret i32 %r
}

; case 25 (line 283): ASSERT EQ: i64 poison = call i64 @load_align_md()
define i64 @ub_case_25() {
  %r = call i64 @load_align_md()
  ret i64 %r
}

; case 26 (line 305): ASSERT EQ: i32 poison = call i32 @load_after_lifetime_end()
define i32 @ub_case_26() {
  %r = call i32 @load_after_lifetime_end()
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
    i32 12, label %case12
    i32 13, label %case13
    i32 14, label %case14
    i32 15, label %case15
    i32 16, label %case16
    i32 17, label %case17
    i32 18, label %case18
    i32 19, label %case19
    i32 20, label %case20
    i32 21, label %case21
    i32 22, label %case22
    i32 23, label %case23
    i32 24, label %case24
    i32 25, label %case25
    i32 26, label %case26
  ]
case0:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 0)
  %c0_r = call i32 @ub_case_0()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 0)
  %c0_0 = sext i32 %c0_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c0_0)
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
  %c7_r = call i64 @ub_case_7()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 7)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c7_r)
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
case12:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 12)
  %c12_r = call i32 @ub_case_12()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 12)
  %c12_0 = sext i32 %c12_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c12_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case13:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 13)
  %c13_r = call i32 @ub_case_13()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 13)
  %c13_0 = sext i32 %c13_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c13_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case14:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 14)
  %c14_r = call i16 @ub_case_14()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 14)
  %c14_0 = sext i16 %c14_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c14_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case15:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 15)
  %c15_r = call i32 @ub_case_15()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 15)
  %c15_0 = sext i32 %c15_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c15_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case16:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 16)
  %c16_r = call i32 @ub_case_16()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 16)
  %c16_0 = sext i32 %c16_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c16_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case17:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 17)
  %c17_r = call i32 @ub_case_17()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 17)
  %c17_0 = sext i32 %c17_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c17_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case18:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 18)
  %c18_r = call { i32, i32 } @ub_case_18()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 18)
  %c18_0 = extractvalue { i32, i32 } %c18_r, 0
  %c18_1 = sext i32 %c18_0 to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c18_1)
  %c18_2 = extractvalue { i32, i32 } %c18_r, 1
  %c18_3 = sext i32 %c18_2 to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c18_3)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case19:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 19)
  %c19_r = call i32 @ub_case_19()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 19)
  %c19_0 = sext i32 %c19_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c19_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case20:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 20)
  %c20_r = call i32 @ub_case_20()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 20)
  %c20_0 = sext i32 %c20_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c20_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case21:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 21)
  %c21_r = call i32 @ub_case_21()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 21)
  %c21_0 = sext i32 %c21_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c21_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case22:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 22)
  %c22_r = call i64 @ub_case_22()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 22)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c22_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case23:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 23)
  %c23_r = call i32 @ub_case_23()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 23)
  %c23_0 = sext i32 %c23_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c23_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case24:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 24)
  %c24_r = call i32 @ub_case_24()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 24)
  %c24_0 = sext i32 %c24_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c24_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case25:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 25)
  %c25_r = call i64 @ub_case_25()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 25)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c25_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case26:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 26)
  %c26_r = call i32 @ub_case_26()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 26)
  %c26_0 = sext i32 %c26_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c26_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
bad:
  ret i32 2
}
; ---- END executable tail ----
