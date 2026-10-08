; UB tests for *function* attributes (on definitions and call sites).
;
; LangRef (noreturn): "This produces undefined behavior at runtime if the
; function ever does dynamically return."
; (`nounwind`, and the noreturn-that-throws control, are in
; call-fn-attrs-unwind.ll: they use Vellvm's throw intrinsic.)
; LangRef (memory(...)): "read: The location is only read. Writing to the
; location is immediate undefined behavior. This includes the case where the
; location is read from and then the same value is written back."  "none: No
; reads or writes to the location are observed outside the function. It is
; always valid to read and write allocas, and to read global constants, even if
; memory(none) is used".  "argmem: This refers to accesses that are based on
; pointer arguments to the function."
;
; Not tested (not observable by a terminating test, or no single UB point):
; willreturn / mustprogress (non-termination), nosync, speculatable,
; norecurse (no UB stated).
;
; LangRef (nocreateundeforpoison): "the result of the function (prior to
; application of return attributes/metadata) will not be undef or poison if
; all arguments are not undef and not poison. Otherwise, it is undefined
; behavior."

@g = global i32 0
@k = constant i32 7

; ------------------------------------------------------------ noreturn

define void @noreturn_returns() noreturn {
  ret void                                        ; <- UB @call_noreturn
}

define i32 @call_noreturn() {
  call void @noreturn_returns()
  ret i32 0
}

; ASSERT UB 30: call i32 @call_noreturn()

; On the call site.
define void @returns() {
  ret void
}

define i32 @call_noreturn_callsite() {
  call void @returns() noreturn                   ; <- UB @call_noreturn_callsite
  ret i32 0
}

; ASSERT UB 46: call i32 @call_noreturn_callsite()

; ------------------------------------------------------------- memory(...)

define void @mem_none_writes_global() memory(none) {
  store i32 1, ptr @g                             ; <- UB @call_mem_none_writes_global
  ret void
}

define i32 @call_mem_none_writes_global() {
  call void @mem_none_writes_global()
  ret i32 0
}

; ASSERT UB 55: call i32 @call_mem_none_writes_global()

define void @mem_read_writes_global() memory(read) {
  store i32 1, ptr @g                             ; <- UB @call_mem_read_writes_global
  ret void
}

define i32 @call_mem_read_writes_global() {
  call void @mem_read_writes_global()
  ret i32 0
}

; ASSERT UB 67: call i32 @call_mem_read_writes_global()

; "This includes the case where the location is read from and then the same
; value is written back."
define void @mem_read_writes_same_value() memory(read) {
  %v = load i32, ptr @g
  store i32 %v, ptr @g                            ; <- UB @call_mem_read_writes_same_value
  ret void
}

define i32 @call_mem_read_writes_same_value() {
  call void @mem_read_writes_same_value()
  ret i32 0
}

; ASSERT UB 82: call i32 @call_mem_read_writes_same_value()

; memory(argmem: read): writing through the argument is UB.
define void @mem_argmem_read_writes_arg(ptr %p) memory(argmem: read) {
  store i32 1, ptr %p                             ; <- UB @call_mem_argmem_read_writes_arg
  ret void
}

define i32 @call_mem_argmem_read_writes_arg() {
  %a = alloca i32
  call void @mem_argmem_read_writes_arg(ptr %a)
  ret i32 0
}

; ASSERT UB 95: call i32 @call_mem_argmem_read_writes_arg()

; memory(argmem: readwrite) (i.e. none for other memory): writing a global
; that is not reachable through an argument.
define void @mem_argmem_only_writes_global(ptr %p) memory(argmem: readwrite) {
  store i32 1, ptr %p
  store i32 1, ptr @g                             ; <- UB @call_mem_argmem_only_writes_global
  ret void
}

define i32 @call_mem_argmem_only_writes_global() {
  %a = alloca i32
  call void @mem_argmem_only_writes_global(ptr %a)
  ret i32 0
}

; ASSERT UB 111: call i32 @call_mem_argmem_only_writes_global()

; memory(...) on the call site.
define void @writes_global() {
  store i32 1, ptr @g                             ; <- UB @call_mem_none_callsite
  ret void
}

define i32 @call_mem_none_callsite() {
  call void @writes_global() memory(none)
  ret i32 0
}

; ASSERT UB 125: call i32 @call_mem_none_callsite()

; Controls: memory(none) may use its own allocas and read constants.
define i32 @mem_none_ok() memory(none) {
  %a = alloca i32
  store i32 3, ptr %a
  %x = load i32, ptr %a
  %y = load i32, ptr @k
  %r = add i32 %x, %y
  ret i32 %r
}

; ASSERT EQ: i32 10 = call i32 @mem_none_ok()

define i32 @mem_read_ok() memory(read) {
  %v = load i32, ptr @g
  ret i32 %v
}

; ASSERT EQ: i32 0 = call i32 @mem_read_ok()

; ----------------------------------------------------- nocreateundeforpoison

define i32 @creates_poison(i32 %x) nocreateundeforpoison {
  %r = add nsw i32 %x, 1
  ret i32 %r                                      ; <- UB @creates_poison
}

; ASSERT UB 159: call i32 @creates_poison(i32 2147483647)
; ASSERT EQ: i32 3 = call i32 @creates_poison(i32 2)
; Poison in, poison out is allowed.
; ASSERT EQ: i32 poison = call i32 @creates_poison(i32 poison)

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 38): ASSERT UB 30: call i32 @call_noreturn()
define i32 @ub_case_0() {
  %r = call i32 @call_noreturn()
  ret i32 %r
}

; case 1 (line 50): ASSERT UB 46: call i32 @call_noreturn_callsite()
define i32 @ub_case_1() {
  %r = call i32 @call_noreturn_callsite()
  ret i32 %r
}

; case 2 (line 64): ASSERT UB 55: call i32 @call_mem_none_writes_global()
define i32 @ub_case_2() {
  %r = call i32 @call_mem_none_writes_global()
  ret i32 %r
}

; case 3 (line 76): ASSERT UB 67: call i32 @call_mem_read_writes_global()
define i32 @ub_case_3() {
  %r = call i32 @call_mem_read_writes_global()
  ret i32 %r
}

; case 4 (line 91): ASSERT UB 82: call i32 @call_mem_read_writes_same_value()
define i32 @ub_case_4() {
  %r = call i32 @call_mem_read_writes_same_value()
  ret i32 %r
}

; case 5 (line 105): ASSERT UB 95: call i32 @call_mem_argmem_read_writes_arg()
define i32 @ub_case_5() {
  %r = call i32 @call_mem_argmem_read_writes_arg()
  ret i32 %r
}

; case 6 (line 121): ASSERT UB 111: call i32 @call_mem_argmem_only_writes_global()
define i32 @ub_case_6() {
  %r = call i32 @call_mem_argmem_only_writes_global()
  ret i32 %r
}

; case 7 (line 134): ASSERT UB 125: call i32 @call_mem_none_callsite()
define i32 @ub_case_7() {
  %r = call i32 @call_mem_none_callsite()
  ret i32 %r
}

; case 8 (line 146): ASSERT EQ: i32 10 = call i32 @mem_none_ok()
define i32 @ub_case_8() {
  %r = call i32 @mem_none_ok()
  ret i32 %r
}

; case 9 (line 153): ASSERT EQ: i32 0 = call i32 @mem_read_ok()
define i32 @ub_case_9() {
  %r = call i32 @mem_read_ok()
  ret i32 %r
}

; case 10 (line 162): ASSERT UB 159: call i32 @creates_poison(i32 2147483647)
define i32 @ub_case_10() {
  %r = call i32 @creates_poison(i32 2147483647)
  ret i32 %r
}

; case 11 (line 163): ASSERT EQ: i32 3 = call i32 @creates_poison(i32 2)
define i32 @ub_case_11() {
  %r = call i32 @creates_poison(i32 2)
  ret i32 %r
}

; case 12 (line 165): ASSERT EQ: i32 poison = call i32 @creates_poison(i32 poison)
define i32 @ub_case_12() {
  %r = call i32 @creates_poison(i32 poison)
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
bad:
  ret i32 2
}
; ---- END executable tail ----
