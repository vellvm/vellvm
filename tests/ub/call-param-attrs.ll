; UB tests for value-constraining *parameter* attributes on `call`.
;
; The recurring pattern in LangRef: attributes such as `nonnull`, `align`,
; `range` (and `nofpclass`, see call-param-nofpclass.ll) turn a violating argument into poison; combined
; with `noundef` the violation becomes immediate UB.
;
; LangRef (noundef): "If the value representation contains any undefined or
; poison bits, the behavior is undefined."
; LangRef (Poison Values): immediate UB if poison is "The parameter operand of
; a call or invoke instruction, when the function or invoking call site has a
; noundef attribute in the corresponding position."
; LangRef (nonnull): "if the parameter or return pointer is null, poison value
; is returned or passed instead.  ...  The nonnull attribute should be
; combined with the noundef attribute to ensure a pointer is not null or
; otherwise the behavior is undefined."
; LangRef (align): "If the pointer value does not have the specified
; alignment, poison value is returned or passed instead.  The align attribute
; should be combined with the noundef attribute to ensure a pointer is
; aligned, or otherwise the behavior is undefined."
; LangRef (dereferenceable(<n>)): "The pointer should be well defined,
; otherwise it is undefined behavior.  This means dereferenceable(<n>) implies
; noundef."  It also implies nonnull in addrspace(0).
; LangRef (dereferenceable_or_null(<n>)): "a pointer is exactly one of
; dereferenceable(<n>) or null".
; LangRef (range(<ty> <a>, <b>)): "If the value is not in the specified range,
; it is converted to poison."
;
; UB is attributed to the call instruction (the point where the argument is
; passed), whether the attribute is on the callee's declaration or the call
; site.

declare ptr @malloc(i64)
declare void @free(ptr)

; ---------------------------------------------------------------- noundef

define i32 @take_noundef(i32 noundef %x) {
  ret i32 0
}

define i32 @noundef_arg(i32 %x) {
  %r = call i32 @take_noundef(i32 %x)             ; <- UB @noundef_arg
  ret i32 %r
}

; ASSERT UB 42: call i32 @noundef_arg(i32 poison)
; ASSERT EQ: i32 0 = call i32 @noundef_arg(i32 3)

define i32 @noundef_arg_undef() {
  %r = call i32 @take_noundef(i32 undef)          ; <- UB @noundef_arg_undef
  ret i32 %r
}

; ASSERT UB 50: call i32 @noundef_arg_undef()

; noundef on the call site only.
define i32 @take_plain(i32 %x) {
  ret i32 0
}

define i32 @noundef_callsite(i32 %x) {
  %r = call i32 @take_plain(i32 noundef %x)       ; <- UB @noundef_callsite
  ret i32 %r
}

; ASSERT UB 62: call i32 @noundef_callsite(i32 poison)
; ASSERT EQ: i32 0 = call i32 @noundef_callsite(i32 3)

; Control: no noundef anywhere -- passing poison is fine.
define i32 @plain_poison_arg() {
  %r = call i32 @take_plain(i32 poison)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @plain_poison_arg()

; noundef on an aggregate with one poison field.
define i32 @take_noundef_struct({ i32, i32 } noundef %s) {
  ret i32 0
}

define i32 @noundef_struct_field() {
  %r = call i32 @take_noundef_struct({ i32, i32 } { i32 1, i32 poison }) ; <- UB @noundef_struct_field
  ret i32 %r
}

; ASSERT UB 83: call i32 @noundef_struct_field()

; noundef on a vector with one poison lane.
define i32 @take_noundef_vec(<2 x i32> noundef %v) {
  ret i32 0
}

define i32 @noundef_vector_lane() {
  %r = call i32 @take_noundef_vec(<2 x i32> <i32 1, i32 poison>) ; <- UB @noundef_vector_lane
  ret i32 %r
}

; ASSERT UB 95: call i32 @noundef_vector_lane()

; noundef pointer argument that is poison.
define i32 @take_noundef_ptr(ptr noundef %p) {
  ret i32 0
}

define i32 @noundef_ptr(ptr %p) {
  %r = call i32 @take_noundef_ptr(ptr %p)         ; <- UB @noundef_ptr
  ret i32 %r
}

; ASSERT UB 107: call i32 @noundef_ptr(ptr poison)
; ASSERT EQ: i32 0 = call i32 @noundef_ptr(ptr null)

; ---------------------------------------------------------------- nonnull

define i32 @take_nonnull_noundef(ptr nonnull noundef %p) {
  ret i32 0
}

define i32 @nonnull_noundef(ptr %p) {
  %r = call i32 @take_nonnull_noundef(ptr %p)     ; <- UB @nonnull_noundef
  ret i32 %r
}

; ASSERT UB 121: call i32 @nonnull_noundef(ptr null)

define i32 @nonnull_noundef_ok() {
  %a = alloca i32
  %r = call i32 @nonnull_noundef(ptr %a)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @nonnull_noundef_ok()

; nonnull + noundef on the call site only.
define i32 @take_ptr(ptr %p) {
  ret i32 0
}

define i32 @nonnull_noundef_callsite() {
  %r = call i32 @take_ptr(ptr nonnull noundef null) ; <- UB @nonnull_noundef_callsite
  ret i32 %r
}

; ASSERT UB 141: call i32 @nonnull_noundef_callsite()

; Split across declaration (nonnull) and call site (noundef).
define i32 @take_nonnull(ptr nonnull %p) {
  ret i32 0
}

define i32 @nonnull_decl_noundef_callsite() {
  %r = call i32 @take_nonnull(ptr noundef null)   ; <- UB @nonnull_decl_noundef_callsite
  ret i32 %r
}

; ASSERT UB 153: call i32 @nonnull_decl_noundef_callsite()

; nonnull without noundef: the callee receives poison.  Merely receiving it
; is fine ...
define i32 @nonnull_only_unused() {
  %r = call i32 @take_nonnull(ptr null)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @nonnull_only_unused()

; ... the callee observes poison, not null ...
define i64 @nonnull_observe(ptr nonnull %p) {
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @nonnull_only_observed() {
  %r = call i64 @nonnull_observe(ptr null)
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @nonnull_only_observed()

; ... so testing it against null and branching is UB inside the callee.
define i32 @nonnull_check(ptr nonnull %p) {
entry:
  %c = icmp eq ptr %p, null
  br i1 %c, label %isnull, label %notnull         ; <- UB @nonnull_only_branch
isnull:
  ret i32 1
notnull:
  ret i32 0
}

define i32 @nonnull_only_branch() {
  %r = call i32 @nonnull_check(ptr null)
  ret i32 %r
}

; ASSERT UB 185: call i32 @nonnull_only_branch()

; ------------------------------------------------------------------ align

define i32 @take_align8_noundef(ptr align 8 noundef %p) {
  ret i32 0
}

define i32 @align_noundef_misaligned() {
  %a = alloca [2 x i64], align 8
  %q = getelementptr i8, ptr %a, i64 4
  %r = call i32 @take_align8_noundef(ptr %q)      ; <- UB @align_noundef_misaligned
  ret i32 %r
}

; ASSERT UB 208: call i32 @align_noundef_misaligned()

define i32 @align_noundef_ok() {
  %a = alloca [2 x i64], align 8
  %q = getelementptr i8, ptr %a, i64 8
  %r = call i32 @take_align8_noundef(ptr %q)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @align_noundef_ok()

; align without noundef: poison.
define i64 @align8_observe(ptr align 8 %p) {
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @align_only_misaligned() {
  %a = alloca [2 x i64], align 8
  %q = getelementptr i8, ptr %a, i64 4
  %r = call i64 @align8_observe(ptr %q)
  ret i64 %r
}

; ASSERT EQ: i64 poison = call i64 @align_only_misaligned()

; ------------------------------------------------------- dereferenceable(n)

define i32 @take_deref4(ptr dereferenceable(4) %p) {
  ret i32 0
}

; Null is not dereferenceable; dereferenceable implies noundef, so this is UB
; even though the attribute is "only" dereferenceable.
define i32 @deref_null() {
  %r = call i32 @take_deref4(ptr null)            ; <- UB @deref_null
  ret i32 %r
}

; ASSERT UB 247: call i32 @deref_null()

define i32 @deref_poison(ptr %p) {
  %r = call i32 @take_deref4(ptr %p)              ; <- UB @deref_poison
  ret i32 %r
}

; ASSERT UB 254: call i32 @deref_poison(ptr poison)

; Too small an object.
define i32 @deref_too_small() {
  %a = alloca i16
  %r = call i32 @take_deref4(ptr %a)              ; <- UB @deref_too_small
  ret i32 %r
}

; ASSERT UB 263: call i32 @deref_too_small()

; Freed object.
define i32 @deref_freed() {
  %p = call ptr @malloc(i64 4)
  call void @free(ptr %p)
  %r = call i32 @take_deref4(ptr %p)              ; <- UB @deref_freed
  ret i32 %r
}

; ASSERT UB 273: call i32 @deref_freed()

; Dangling stack pointer.
define ptr @escape_local() {
  %p = alloca i32
  ret ptr %p
}

define i32 @deref_dangling() {
  %p = call ptr @escape_local()
  %r = call i32 @take_deref4(ptr %p)              ; <- UB @deref_dangling
  ret i32 %r
}

; ASSERT UB 287: call i32 @deref_dangling()

; One past the end of an object: nonnull, but not dereferenceable.
define i32 @deref_one_past_end() {
  %a = alloca [2 x i32]
  %q = getelementptr [2 x i32], ptr %a, i64 1
  %r = call i32 @take_deref4(ptr %q)              ; <- UB @deref_one_past_end
  ret i32 %r
}

; ASSERT UB 297: call i32 @deref_one_past_end()

define i32 @deref_ok() {
  %a = alloca i32
  %r = call i32 @take_deref4(ptr %a)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @deref_ok()

; Call-site dereferenceable.
define i32 @deref_callsite() {
  %a = alloca i16
  %r = call i32 @take_ptr(ptr dereferenceable(4) %a) ; <- UB @deref_callsite
  ret i32 %r
}

; ASSERT UB 314: call i32 @deref_callsite()

; ----------------------------------------------- dereferenceable_or_null(n)

define i32 @take_deref_or_null4(ptr dereferenceable_or_null(4) %p) {
  ret i32 0
}

define i32 @deref_or_null_null_ok() {
  %r = call i32 @take_deref_or_null4(ptr null)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @deref_or_null_null_ok()

define i32 @deref_or_null_too_small() {
  %a = alloca i16
  %r = call i32 @take_deref_or_null4(ptr %a)      ; <- UB @deref_or_null_too_small
  ret i32 %r
}

; ASSERT UB 335: call i32 @deref_or_null_too_small()

; ------------------------------------------------------------------ range

define i32 @take_range_noundef(i32 noundef range(i32 0, 10) %x) {
  ret i32 0
}

define i32 @range_noundef(i32 %x) {
  %r = call i32 @take_range_noundef(i32 %x)       ; <- UB @range_noundef
  ret i32 %r
}

; ASSERT UB 348: call i32 @range_noundef(i32 10)
; ASSERT UB 348: call i32 @range_noundef(i32 -1)
; ASSERT EQ: i32 0 = call i32 @range_noundef(i32 9)

; A wrapping range [250, 5) on i8.
define i32 @take_range_wrap(i8 noundef range(i8 -6, 5) %x) {
  ret i32 0
}

define i32 @range_wrap(i8 %x) {
  %r = call i32 @take_range_wrap(i8 %x)           ; <- UB @range_wrap
  ret i32 %r
}

; ASSERT UB 362: call i32 @range_wrap(i8 5)
; ASSERT EQ: i32 0 = call i32 @range_wrap(i8 -6)
; ASSERT EQ: i32 0 = call i32 @range_wrap(i8 4)

; range without noundef: poison.
define i32 @range_observe(i32 range(i32 0, 10) %x) {
  ret i32 %x
}

define i32 @range_only(i32 %x) {
  %r = call i32 @range_observe(i32 %x)
  ret i32 %r
}

; ASSERT EQ: i32 poison = call i32 @range_only(i32 10)
; ASSERT EQ: i32 3 = call i32 @range_only(i32 3)

; nofpclass tests are in call-param-nofpclass.ll (Vellvm's parser does not
; accept `nofpclass` yet, so they are kept separate).

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 46): ASSERT UB 42: call i32 @noundef_arg(i32 poison)
define i32 @ub_case_0() {
  %r = call i32 @noundef_arg(i32 poison)
  ret i32 %r
}

; case 1 (line 47): ASSERT EQ: i32 0 = call i32 @noundef_arg(i32 3)
define i32 @ub_case_1() {
  %r = call i32 @noundef_arg(i32 3)
  ret i32 %r
}

; case 2 (line 54): ASSERT UB 50: call i32 @noundef_arg_undef()
define i32 @ub_case_2() {
  %r = call i32 @noundef_arg_undef()
  ret i32 %r
}

; case 3 (line 66): ASSERT UB 62: call i32 @noundef_callsite(i32 poison)
define i32 @ub_case_3() {
  %r = call i32 @noundef_callsite(i32 poison)
  ret i32 %r
}

; case 4 (line 67): ASSERT EQ: i32 0 = call i32 @noundef_callsite(i32 3)
define i32 @ub_case_4() {
  %r = call i32 @noundef_callsite(i32 3)
  ret i32 %r
}

; case 5 (line 75): ASSERT EQ: i32 0 = call i32 @plain_poison_arg()
define i32 @ub_case_5() {
  %r = call i32 @plain_poison_arg()
  ret i32 %r
}

; case 6 (line 87): ASSERT UB 83: call i32 @noundef_struct_field()
define i32 @ub_case_6() {
  %r = call i32 @noundef_struct_field()
  ret i32 %r
}

; case 7 (line 99): ASSERT UB 95: call i32 @noundef_vector_lane()
define i32 @ub_case_7() {
  %r = call i32 @noundef_vector_lane()
  ret i32 %r
}

; case 8 (line 111): ASSERT UB 107: call i32 @noundef_ptr(ptr poison)
define i32 @ub_case_8() {
  %r = call i32 @noundef_ptr(ptr poison)
  ret i32 %r
}

; case 9 (line 112): ASSERT EQ: i32 0 = call i32 @noundef_ptr(ptr null)
define i32 @ub_case_9() {
  %r = call i32 @noundef_ptr(ptr null)
  ret i32 %r
}

; case 10 (line 125): ASSERT UB 121: call i32 @nonnull_noundef(ptr null)
define i32 @ub_case_10() {
  %r = call i32 @nonnull_noundef(ptr null)
  ret i32 %r
}

; case 11 (line 133): ASSERT EQ: i32 0 = call i32 @nonnull_noundef_ok()
define i32 @ub_case_11() {
  %r = call i32 @nonnull_noundef_ok()
  ret i32 %r
}

; case 12 (line 145): ASSERT UB 141: call i32 @nonnull_noundef_callsite()
define i32 @ub_case_12() {
  %r = call i32 @nonnull_noundef_callsite()
  ret i32 %r
}

; case 13 (line 157): ASSERT UB 153: call i32 @nonnull_decl_noundef_callsite()
define i32 @ub_case_13() {
  %r = call i32 @nonnull_decl_noundef_callsite()
  ret i32 %r
}

; case 14 (line 166): ASSERT EQ: i32 0 = call i32 @nonnull_only_unused()
define i32 @ub_case_14() {
  %r = call i32 @nonnull_only_unused()
  ret i32 %r
}

; case 15 (line 179): ASSERT EQ: i64 poison = call i64 @nonnull_only_observed()
define i64 @ub_case_15() {
  %r = call i64 @nonnull_only_observed()
  ret i64 %r
}

; case 16 (line 197): ASSERT UB 185: call i32 @nonnull_only_branch()
define i32 @ub_case_16() {
  %r = call i32 @nonnull_only_branch()
  ret i32 %r
}

; case 17 (line 212): ASSERT UB 208: call i32 @align_noundef_misaligned()
define i32 @ub_case_17() {
  %r = call i32 @align_noundef_misaligned()
  ret i32 %r
}

; case 18 (line 221): ASSERT EQ: i32 0 = call i32 @align_noundef_ok()
define i32 @ub_case_18() {
  %r = call i32 @align_noundef_ok()
  ret i32 %r
}

; case 19 (line 236): ASSERT EQ: i64 poison = call i64 @align_only_misaligned()
define i64 @ub_case_19() {
  %r = call i64 @align_only_misaligned()
  ret i64 %r
}

; case 20 (line 251): ASSERT UB 247: call i32 @deref_null()
define i32 @ub_case_20() {
  %r = call i32 @deref_null()
  ret i32 %r
}

; case 21 (line 258): ASSERT UB 254: call i32 @deref_poison(ptr poison)
define i32 @ub_case_21() {
  %r = call i32 @deref_poison(ptr poison)
  ret i32 %r
}

; case 22 (line 267): ASSERT UB 263: call i32 @deref_too_small()
define i32 @ub_case_22() {
  %r = call i32 @deref_too_small()
  ret i32 %r
}

; case 23 (line 277): ASSERT UB 273: call i32 @deref_freed()
define i32 @ub_case_23() {
  %r = call i32 @deref_freed()
  ret i32 %r
}

; case 24 (line 291): ASSERT UB 287: call i32 @deref_dangling()
define i32 @ub_case_24() {
  %r = call i32 @deref_dangling()
  ret i32 %r
}

; case 25 (line 301): ASSERT UB 297: call i32 @deref_one_past_end()
define i32 @ub_case_25() {
  %r = call i32 @deref_one_past_end()
  ret i32 %r
}

; case 26 (line 309): ASSERT EQ: i32 0 = call i32 @deref_ok()
define i32 @ub_case_26() {
  %r = call i32 @deref_ok()
  ret i32 %r
}

; case 27 (line 318): ASSERT UB 314: call i32 @deref_callsite()
define i32 @ub_case_27() {
  %r = call i32 @deref_callsite()
  ret i32 %r
}

; case 28 (line 331): ASSERT EQ: i32 0 = call i32 @deref_or_null_null_ok()
define i32 @ub_case_28() {
  %r = call i32 @deref_or_null_null_ok()
  ret i32 %r
}

; case 29 (line 339): ASSERT UB 335: call i32 @deref_or_null_too_small()
define i32 @ub_case_29() {
  %r = call i32 @deref_or_null_too_small()
  ret i32 %r
}

; case 30 (line 352): ASSERT UB 348: call i32 @range_noundef(i32 10)
define i32 @ub_case_30() {
  %r = call i32 @range_noundef(i32 10)
  ret i32 %r
}

; case 31 (line 353): ASSERT UB 348: call i32 @range_noundef(i32 -1)
define i32 @ub_case_31() {
  %r = call i32 @range_noundef(i32 -1)
  ret i32 %r
}

; case 32 (line 354): ASSERT EQ: i32 0 = call i32 @range_noundef(i32 9)
define i32 @ub_case_32() {
  %r = call i32 @range_noundef(i32 9)
  ret i32 %r
}

; case 33 (line 366): ASSERT UB 362: call i32 @range_wrap(i8 5)
define i32 @ub_case_33() {
  %r = call i32 @range_wrap(i8 5)
  ret i32 %r
}

; case 34 (line 367): ASSERT EQ: i32 0 = call i32 @range_wrap(i8 -6)
define i32 @ub_case_34() {
  %r = call i32 @range_wrap(i8 -6)
  ret i32 %r
}

; case 35 (line 368): ASSERT EQ: i32 0 = call i32 @range_wrap(i8 4)
define i32 @ub_case_35() {
  %r = call i32 @range_wrap(i8 4)
  ret i32 %r
}

; case 36 (line 380): ASSERT EQ: i32 poison = call i32 @range_only(i32 10)
define i32 @ub_case_36() {
  %r = call i32 @range_only(i32 10)
  ret i32 %r
}

; case 37 (line 381): ASSERT EQ: i32 3 = call i32 @range_only(i32 3)
define i32 @ub_case_37() {
  %r = call i32 @range_only(i32 3)
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
    i32 27, label %case27
    i32 28, label %case28
    i32 29, label %case29
    i32 30, label %case30
    i32 31, label %case31
    i32 32, label %case32
    i32 33, label %case33
    i32 34, label %case34
    i32 35, label %case35
    i32 36, label %case36
    i32 37, label %case37
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
  %c15_r = call i64 @ub_case_15()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 15)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c15_r)
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
case19:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 19)
  %c19_r = call i64 @ub_case_19()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 19)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c19_r)
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
  %c22_r = call i32 @ub_case_22()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 22)
  %c22_0 = sext i32 %c22_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c22_0)
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
  %c25_r = call i32 @ub_case_25()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 25)
  %c25_0 = sext i32 %c25_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c25_0)
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
case27:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 27)
  %c27_r = call i32 @ub_case_27()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 27)
  %c27_0 = sext i32 %c27_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c27_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case28:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 28)
  %c28_r = call i32 @ub_case_28()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 28)
  %c28_0 = sext i32 %c28_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c28_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case29:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 29)
  %c29_r = call i32 @ub_case_29()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 29)
  %c29_0 = sext i32 %c29_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c29_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case30:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 30)
  %c30_r = call i32 @ub_case_30()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 30)
  %c30_0 = sext i32 %c30_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c30_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case31:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 31)
  %c31_r = call i32 @ub_case_31()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 31)
  %c31_0 = sext i32 %c31_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c31_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case32:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 32)
  %c32_r = call i32 @ub_case_32()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 32)
  %c32_0 = sext i32 %c32_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c32_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case33:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 33)
  %c33_r = call i32 @ub_case_33()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 33)
  %c33_0 = sext i32 %c33_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c33_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case34:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 34)
  %c34_r = call i32 @ub_case_34()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 34)
  %c34_0 = sext i32 %c34_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c34_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case35:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 35)
  %c35_r = call i32 @ub_case_35()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 35)
  %c35_0 = sext i32 %c35_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c35_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case36:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 36)
  %c36_r = call i32 @ub_case_36()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 36)
  %c36_0 = sext i32 %c36_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c36_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case37:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 37)
  %c37_r = call i32 @ub_case_37()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 37)
  %c37_0 = sext i32 %c37_r to i64
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c37_0)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
bad:
  ret i32 2
}
; ---- END executable tail ----
