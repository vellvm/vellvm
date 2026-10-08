; UB tests for the `store` instruction.
;
; LangRef (store, Semantics): "If <pointer> is not a well-defined value, the
; behavior is undefined."
; LangRef (store, Arguments): "Overestimating the alignment results in
; undefined behavior."
; LangRef (Pointer Aliasing Rules): any memory access must be done through a
; pointer associated with the accessed address range.
; LangRef (Object Lifetime): accessing a dead object is UB; for stack objects
; outside their lifetime, loads return poison but "Storing to it is still
; undefined behavior."
; LangRef (Global Variables): a global `constant` "indicates that the contents
; of the variable will **never** be modified".
; LangRef (Poison Values) example: `store i32 0, ptr %poison_yet_again ;
; Undefined behavior due to store to poison.`

declare ptr @malloc(i64)
declare void @free(ptr)
declare void @llvm.lifetime.start.p0(ptr captures(none))
declare void @llvm.lifetime.end.p0(ptr captures(none))

@h = global i32 0
@k = constant i32 7

define i32 @store(ptr %p) {
  store i32 1, ptr %p                             ; <- UB @store
  ret i32 0
}

; ASSERT UB 26: call i32 @store(ptr null)
; ASSERT UB 26: call i32 @store(ptr poison)

define i32 @store_ok() {
  %p = alloca i32
  %r = call i32 @store(ptr %p)
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 1 = call i32 @store_ok()

define i32 @store_undef_ptr() {
  store i32 1, ptr undef                          ; <- UB @store_undef_ptr
  ret i32 0
}

; ASSERT UB 43: call i32 @store_undef_ptr()

; The LangRef Poison Values example: a poison index makes the address poison.
define i32 @store_poison_gep() {
  %poison = sub nuw i32 0, 1
  %still_poison = and i32 %poison, 0
  %addr = getelementptr i32, ptr @h, i32 %still_poison
  store i32 0, ptr %addr                          ; <- UB @store_poison_gep
  ret i32 0
}

; ASSERT UB 54: call i32 @store_poison_gep()

; Storing a poison *value* is fine (it is the address that matters).
define i32 @store_poison_value() {
  %poison = sub nuw i32 0, 1
  store i32 %poison, ptr @h
  %v = load i32, ptr @h
  ret i32 %v
}

; ASSERT EQ: i32 poison = call i32 @store_poison_value()

define i32 @store_volatile_null() {
  store volatile i32 1, ptr null                  ; <- UB @store_volatile_null
  ret i32 0
}

; ASSERT UB 71: call i32 @store_volatile_null()

define i32 @store_atomic_null() {
  store atomic i32 1, ptr null seq_cst, align 4   ; <- UB @store_atomic_null
  ret i32 0
}

; ASSERT UB 78: call i32 @store_atomic_null()

define i32 @store_past_end() {
  %p = alloca i32
  %q = getelementptr i32, ptr %p, i64 1
  store i32 1, ptr %q                             ; <- UB @store_past_end
  ret i32 0
}

; ASSERT UB 87: call i32 @store_past_end()

define i32 @store_partially_oob() {
  %p = alloca i32
  store i64 1, ptr %p                             ; <- UB @store_partially_oob
  ret i32 0
}

; ASSERT UB 95: call i32 @store_partially_oob()

define ptr @escape_local() {
  %p = alloca i32
  ret ptr %p
}

define i32 @store_dangling_stack() {
  %p = call ptr @escape_local()
  store i32 1, ptr %p                             ; <- UB @store_dangling_stack
  ret i32 0
}

; ASSERT UB 108: call i32 @store_dangling_stack()

define i32 @store_after_free() {
  %p = call ptr @malloc(i64 4)
  call void @free(ptr %p)
  store i32 1, ptr %p                             ; <- UB @store_after_free
  ret i32 0
}

; ASSERT UB 117: call i32 @store_after_free()

define i32 @store_misaligned() {
  %p = alloca [2 x i32], align 8
  %q = getelementptr i8, ptr %p, i64 4
  store i32 1, ptr %q, align 8                    ; <- UB @store_misaligned
  ret i32 0
}

; ASSERT UB 126: call i32 @store_misaligned()

define i32 @store_aligned_ok() {
  %p = alloca [2 x i32], align 8
  %q = getelementptr i8, ptr %p, i64 4
  store i32 1, ptr %q, align 4
  %v = load i32, ptr %q
  ret i32 %v
}

; ASSERT EQ: i32 1 = call i32 @store_aligned_ok()

; Writing to a `constant` global.
define i32 @store_to_constant_global() {
  store i32 8, ptr @k                             ; <- UB @store_to_constant_global
  ret i32 0
}

; ASSERT UB 144: call i32 @store_to_constant_global()

define i32 @load_constant_global() {
  %v = load i32, ptr @k
  ret i32 %v
}

; ASSERT EQ: i32 7 = call i32 @load_constant_global()

; Store to a stack object after llvm.lifetime.end.
define i32 @store_after_lifetime_end() {
  %p = alloca i32
  call void @llvm.lifetime.start.p0(ptr %p)
  store i32 1, ptr %p
  call void @llvm.lifetime.end.p0(ptr %p)
  store i32 2, ptr %p                             ; <- UB @store_after_lifetime_end
  ret i32 0
}

; ASSERT UB 163: call i32 @store_after_lifetime_end()

; Store to a stack object before its llvm.lifetime.start: "If the returned
; pointer is used by llvm.lifetime.start, the returned object is initially
; dead."
define i32 @store_before_lifetime_start() {
  %p = alloca i32
  store i32 2, ptr %p                             ; <- UB @store_before_lifetime_start
  call void @llvm.lifetime.start.p0(ptr %p)
  call void @llvm.lifetime.end.p0(ptr %p)
  ret i32 0
}

; ASSERT UB 174: call i32 @store_before_lifetime_start()

; Control: lifetime.start again revives the object.
define i32 @store_after_lifetime_restart() {
  %p = alloca i32
  call void @llvm.lifetime.start.p0(ptr %p)
  call void @llvm.lifetime.end.p0(ptr %p)
  call void @llvm.lifetime.start.p0(ptr %p)
  store i32 3, ptr %p
  %v = load i32, ptr %p
  call void @llvm.lifetime.end.p0(ptr %p)
  ret i32 %v
}

; ASSERT EQ: i32 3 = call i32 @store_after_lifetime_restart()

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 30): ASSERT UB 26: call i32 @store(ptr null)
define i32 @ub_case_0() {
  %r = call i32 @store(ptr null)
  ret i32 %r
}

; case 1 (line 31): ASSERT UB 26: call i32 @store(ptr poison)
define i32 @ub_case_1() {
  %r = call i32 @store(ptr poison)
  ret i32 %r
}

; case 2 (line 40): ASSERT EQ: i32 1 = call i32 @store_ok()
define i32 @ub_case_2() {
  %r = call i32 @store_ok()
  ret i32 %r
}

; case 3 (line 47): ASSERT UB 43: call i32 @store_undef_ptr()
define i32 @ub_case_3() {
  %r = call i32 @store_undef_ptr()
  ret i32 %r
}

; case 4 (line 58): ASSERT UB 54: call i32 @store_poison_gep()
define i32 @ub_case_4() {
  %r = call i32 @store_poison_gep()
  ret i32 %r
}

; case 5 (line 68): ASSERT EQ: i32 poison = call i32 @store_poison_value()
define i32 @ub_case_5() {
  %r = call i32 @store_poison_value()
  ret i32 %r
}

; case 6 (line 75): ASSERT UB 71: call i32 @store_volatile_null()
define i32 @ub_case_6() {
  %r = call i32 @store_volatile_null()
  ret i32 %r
}

; case 7 (line 82): ASSERT UB 78: call i32 @store_atomic_null()
define i32 @ub_case_7() {
  %r = call i32 @store_atomic_null()
  ret i32 %r
}

; case 8 (line 91): ASSERT UB 87: call i32 @store_past_end()
define i32 @ub_case_8() {
  %r = call i32 @store_past_end()
  ret i32 %r
}

; case 9 (line 99): ASSERT UB 95: call i32 @store_partially_oob()
define i32 @ub_case_9() {
  %r = call i32 @store_partially_oob()
  ret i32 %r
}

; case 10 (line 112): ASSERT UB 108: call i32 @store_dangling_stack()
define i32 @ub_case_10() {
  %r = call i32 @store_dangling_stack()
  ret i32 %r
}

; case 11 (line 121): ASSERT UB 117: call i32 @store_after_free()
define i32 @ub_case_11() {
  %r = call i32 @store_after_free()
  ret i32 %r
}

; case 12 (line 130): ASSERT UB 126: call i32 @store_misaligned()
define i32 @ub_case_12() {
  %r = call i32 @store_misaligned()
  ret i32 %r
}

; case 13 (line 140): ASSERT EQ: i32 1 = call i32 @store_aligned_ok()
define i32 @ub_case_13() {
  %r = call i32 @store_aligned_ok()
  ret i32 %r
}

; case 14 (line 148): ASSERT UB 144: call i32 @store_to_constant_global()
define i32 @ub_case_14() {
  %r = call i32 @store_to_constant_global()
  ret i32 %r
}

; case 15 (line 155): ASSERT EQ: i32 7 = call i32 @load_constant_global()
define i32 @ub_case_15() {
  %r = call i32 @load_constant_global()
  ret i32 %r
}

; case 16 (line 167): ASSERT UB 163: call i32 @store_after_lifetime_end()
define i32 @ub_case_16() {
  %r = call i32 @store_after_lifetime_end()
  ret i32 %r
}

; case 17 (line 180): ASSERT UB 174: call i32 @store_before_lifetime_start()
define i32 @ub_case_17() {
  %r = call i32 @store_before_lifetime_start()
  ret i32 %r
}

; case 18 (line 194): ASSERT EQ: i32 3 = call i32 @store_after_lifetime_restart()
define i32 @ub_case_18() {
  %r = call i32 @store_after_lifetime_restart()
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
  %c14_r = call i32 @ub_case_14()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 14)
  %c14_0 = sext i32 %c14_r to i64
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
  %c18_r = call i32 @ub_case_18()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 18)
  %c18_0 = sext i32 %c18_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c18_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
bad:
  ret i32 2
}
; ---- END executable tail ----
