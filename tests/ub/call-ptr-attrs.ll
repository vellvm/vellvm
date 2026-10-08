; UB tests for pointer-argument *capability* attributes: what the callee (and,
; via `captures`, the rest of the program) may do through a pointer argument.
;
; LangRef (readonly): "If a function writes to a readonly pointer argument, the
; behavior is undefined."
; LangRef (readnone): "If a function reads from or writes to a readnone
; pointer argument, the behavior is undefined."
; LangRef (captures(...)) and (Pointer Capture / Provenance capture): "If an
; argument does not capture the provenance of the pointer, accesses that are
; based on the argument and are performed after the function returns (or
; unwinds) cause undefined behavior. In the case where only read provenance is
; captured, only stores cause undefined behavior."
; LangRef (nofree): "the underlying object cannot be freed until the function
; returns (or unwinds), otherwise the behavior is undefined. ... Notably, it is
; still possible to free the underlying object through a pointer that is not
; based on the argument."
; LangRef (noalias): "memory locations accessed via pointer values based on the
; argument ... are not also accessed, during the execution of the function, via
; pointer values not based on the argument ... This guarantee only holds for
; memory locations that are modified ... If there are other accesses not based
; on the argument or return value, the behavior is undefined."
;
; LangRef (initializes((Lo, Hi), ...)): for bytes of the range not yet
; initialized by the callee, "If the byte is stored with a volatile or atomic
; write, the behavior is undefined. If the byte is loaded, return a poison
; value."
; LangRef (writable): "the first N bytes will be (non-atomically) loaded and
; stored back on entry to the function", so passing memory that must never be
; written (a `constant` global) is UB.
;
; Further pointer-attribute cases whose syntax Vellvm does not parse yet live
; in call-ptr-attrs-unparsed.ll.

declare ptr @malloc(i64)
declare void @free(ptr)

@slot = global ptr null

; ------------------------------------------------------- readonly / readnone

define void @readonly_writes(ptr readonly %p) {
  store i32 1, ptr %p                             ; <- UB @call_readonly_writes
  ret void
}

define i32 @call_readonly_writes() {
  %a = alloca i32
  call void @readonly_writes(ptr %a)
  ret i32 0
}

; ASSERT UB 42: call i32 @call_readonly_writes()

; readonly restricts writes *through the argument*, not to the memory: writing
; it via another pointer is allowed.
define void @readonly_writes_other(ptr readonly %p, ptr %q) {
  store i32 1, ptr %q
  %v = load i32, ptr %p
  ret void
}

define i32 @call_readonly_writes_other_ok() {
  %a = alloca i32
  call void @readonly_writes_other(ptr %a, ptr %a)
  %v = load i32, ptr %a
  ret i32 %v
}

; ASSERT EQ: i32 1 = call i32 @call_readonly_writes_other_ok()

; readonly on the call site.
define void @writes(ptr %p) {
  store i32 1, ptr %p                             ; <- UB @call_readonly_callsite
  ret void
}

define i32 @call_readonly_callsite() {
  %a = alloca i32
  call void @writes(ptr readonly %a)
  ret i32 0
}

; ASSERT UB 73: call i32 @call_readonly_callsite()

define i32 @readnone_reads(ptr readnone %p) {
  %v = load i32, ptr %p                           ; <- UB @call_readnone_reads
  ret i32 %v
}

define i32 @call_readnone_reads() {
  %a = alloca i32
  store i32 0, ptr %a
  %v = call i32 @readnone_reads(ptr %a)
  ret i32 %v
}

; ASSERT UB 86: call i32 @call_readnone_reads()

define void @readnone_writes(ptr readnone %p) {
  store i32 1, ptr %p                             ; <- UB @call_readnone_writes
  ret void
}

define i32 @call_readnone_writes() {
  %a = alloca i32
  call void @readnone_writes(ptr %a)
  ret i32 0
}

; ASSERT UB 100: call i32 @call_readnone_writes()

; Control: readnone allows comparing / converting the pointer.
define i64 @readnone_ptrtoint(ptr readnone %p) {
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i32 @call_readnone_ok() {
  %a = alloca i32
  %i = call i64 @readnone_ptrtoint(ptr %a)
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @call_readnone_ok()

; ------------------------------------------------------------------ captures

; Stores its argument for later use.
define void @stash(ptr %p) {
  store ptr %p, ptr @slot
  ret void
}

define void @stash_none(ptr captures(none) %p) {
  store ptr %p, ptr @slot
  ret void
}

define void @stash_address(ptr captures(address) %p) {
  store ptr %p, ptr @slot
  ret void
}

define void @stash_read(ptr captures(address, read_provenance) %p) {
  store ptr %p, ptr @slot
  ret void
}

; Control: default (captures everything).
define i32 @captures_default_ok() {
  %a = alloca i32
  store i32 5, ptr %a
  call void @stash(ptr %a)
  %p = load ptr, ptr @slot
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @captures_default_ok()

; The LangRef example: captures(address), then a load after return.
define i32 @captures_address_load() {
  %a = alloca i32
  store i32 5, ptr %a
  call void @stash_address(ptr %a)
  %p = load ptr, ptr @slot
  %v = load i32, ptr %p                           ; <- UB @captures_address_load
  ret i32 %v
}

; ASSERT UB 167: call i32 @captures_address_load()

; Using the stashed pointer only for its address is fine.
define i32 @captures_address_compare_ok() {
entry:
  %a = alloca i32
  call void @stash_address(ptr %a)
  %p = load ptr, ptr @slot
  %c = icmp eq ptr %p, %a
  br i1 %c, label %t, label %f
t:
  ret i32 1
f:
  ret i32 0
}

; ASSERT EQ: i32 1 = call i32 @captures_address_compare_ok()

define i32 @captures_none_store() {
  %a = alloca i32
  call void @stash_none(ptr %a)
  %p = load ptr, ptr @slot
  store i32 1, ptr %p                             ; <- UB @captures_none_store
  ret i32 0
}

; ASSERT UB 193: call i32 @captures_none_store()

; The LangRef example: read_provenance captured -- loads OK, stores UB.
define i32 @captures_read_provenance_load_ok() {
  %a = alloca i32
  store i32 5, ptr %a
  call void @stash_read(ptr %a)
  %p = load ptr, ptr @slot
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @captures_read_provenance_load_ok()

define i32 @captures_read_provenance_store() {
  %a = alloca i32
  call void @stash_read(ptr %a)
  %p = load ptr, ptr @slot
  store i32 0, ptr %p                             ; <- UB @captures_read_provenance_store
  ret i32 0
}

; ASSERT UB 215: call i32 @captures_read_provenance_store()

; The original pointer (not the captured copy) keeps full permissions.
define i32 @captures_original_ok() {
  %a = alloca i32
  call void @stash_none(ptr %a)
  store i32 6, ptr %a
  %v = load i32, ptr %a
  ret i32 %v
}

; ASSERT EQ: i32 6 = call i32 @captures_original_ok()

; captures on the call site.
define i32 @captures_none_callsite() {
  %a = alloca i32
  call void @stash(ptr captures(none) %a)
  %p = load ptr, ptr @slot
  store i32 1, ptr %p                             ; <- UB @captures_none_callsite
  ret i32 0
}

; ASSERT UB 237: call i32 @captures_none_callsite()

; Returning the pointer counts as a capture unless `ret:` is allowed.
define ptr @return_arg_none(ptr captures(none) %p) {
  ret ptr %p
}

define i32 @captures_none_returned() {
  %a = alloca i32
  %p = call ptr @return_arg_none(ptr %a)
  store i32 1, ptr %p                             ; <- UB @captures_none_returned
  ret i32 0
}

; ASSERT UB 251: call i32 @captures_none_returned()

; (`captures(ret: ...)` cases are in call-ptr-attrs-unparsed.ll.)

; -------------------------------------------------------------------- nofree

define void @nofree_frees(ptr nofree %p) {
  call void @free(ptr %p)                         ; <- UB @call_nofree_frees
  ret void
}

define i32 @call_nofree_frees() {
  %p = call ptr @malloc(i64 4)
  call void @nofree_frees(ptr %p)
  ret i32 0
}

; ASSERT UB 262: call i32 @call_nofree_frees()

; Freeing via a pointer *not* based on the nofree argument is allowed.
define void @nofree_frees_other(ptr nofree %p, ptr %q) {
  call void @free(ptr %q)
  ret void
}

define i32 @call_nofree_frees_other_ok() {
  %p = call ptr @malloc(i64 4)
  call void @nofree_frees_other(ptr %p, ptr %p)
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @call_nofree_frees_other_ok()

; ------------------------------------------------------------------- noalias

; %p is noalias, and the location it accesses is modified through %q.
define i32 @noalias_conflict(ptr noalias %p, ptr %q) {
  store i32 1, ptr %p
  store i32 2, ptr %q                             ; <- UB @call_noalias_conflict
  %v = load i32, ptr %p
  ret i32 %v
}

define i32 @call_noalias_conflict() {
  %a = alloca i32
  %v = call i32 @noalias_conflict(ptr %a, ptr %a)
  ret i32 %v
}

; ASSERT UB 293: call i32 @call_noalias_conflict()

define i32 @call_noalias_disjoint_ok() {
  %a = alloca i32
  %b = alloca i32
  %v = call i32 @noalias_conflict(ptr %a, ptr %b)
  ret i32 %v
}

; ASSERT EQ: i32 1 = call i32 @call_noalias_disjoint_ok()

; Only *modified* locations matter: two read-only accesses may alias.
define i32 @noalias_read_only(ptr noalias %p, ptr %q) {
  %x = load i32, ptr %p
  %y = load i32, ptr %q
  %r = add i32 %x, %y
  ret i32 %r
}

define i32 @call_noalias_read_only_ok() {
  %a = alloca i32
  store i32 2, ptr %a
  %v = call i32 @noalias_read_only(ptr %a, ptr %a)
  ret i32 %v
}

; ASSERT EQ: i32 4 = call i32 @call_noalias_read_only_ok()

; --------------------------------------------------------------- initializes

define void @init_volatile(ptr initializes((0, 4)) %p) {
  store volatile i32 1, ptr %p                    ; <- UB @call_init_volatile
  ret void
}

define i32 @call_init_volatile() {
  %a = alloca i32
  call void @init_volatile(ptr %a)
  ret i32 0
}

; ASSERT UB 335: call i32 @call_init_volatile()

define void @init_atomic(ptr initializes((0, 4)) %p) {
  store atomic i32 1, ptr %p seq_cst, align 4     ; <- UB @call_init_atomic
  ret void
}

define i32 @call_init_atomic() {
  %a = alloca i32
  call void @init_atomic(ptr %a)
  ret i32 0
}

; ASSERT UB 348: call i32 @call_init_atomic()

; Control: a volatile store *after* the initializing write is fine.
define void @init_then_volatile(ptr initializes((0, 4)) %p) {
  store i32 1, ptr %p
  store volatile i32 2, ptr %p
  ret void
}

define i32 @call_init_then_volatile_ok() {
  %a = alloca i32
  call void @init_then_volatile(ptr %a)
  %v = load i32, ptr %a
  ret i32 %v
}

; ASSERT EQ: i32 2 = call i32 @call_init_then_volatile_ok()

; Control: reading before initializing yields poison, even though the caller
; stored a value there.
define i32 @init_reads_first(ptr initializes((0, 4)) %p) {
  %v = load i32, ptr %p
  store i32 1, ptr %p
  ret i32 %v
}

define i32 @call_init_reads_first() {
  %a = alloca i32
  store i32 9, ptr %a
  %v = call i32 @init_reads_first(ptr %a)
  ret i32 %v
}

; ASSERT EQ: i32 poison = call i32 @call_init_reads_first()

; ------------------------------------------------------------------ writable

@const_word = constant i32 7

define i32 @take_writable(ptr writable dereferenceable(4) %p) {
  ret i32 0
}

define i32 @call_writable_constant() {
  %r = call i32 @take_writable(ptr @const_word)   ; <- UB @call_writable_constant
  ret i32 %r
}

; ASSERT UB 402: call i32 @call_writable_constant()

define i32 @call_writable_ok() {
  %a = alloca i32
  %r = call i32 @take_writable(ptr %a)
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @call_writable_ok()

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 52): ASSERT UB 42: call i32 @call_readonly_writes()
define i32 @ub_case_0() {
  %r = call i32 @call_readonly_writes()
  ret i32 %r
}

; case 1 (line 69): ASSERT EQ: i32 1 = call i32 @call_readonly_writes_other_ok()
define i32 @ub_case_1() {
  %r = call i32 @call_readonly_writes_other_ok()
  ret i32 %r
}

; case 2 (line 83): ASSERT UB 73: call i32 @call_readonly_callsite()
define i32 @ub_case_2() {
  %r = call i32 @call_readonly_callsite()
  ret i32 %r
}

; case 3 (line 97): ASSERT UB 86: call i32 @call_readnone_reads()
define i32 @ub_case_3() {
  %r = call i32 @call_readnone_reads()
  ret i32 %r
}

; case 4 (line 110): ASSERT UB 100: call i32 @call_readnone_writes()
define i32 @ub_case_4() {
  %r = call i32 @call_readnone_writes()
  ret i32 %r
}

; case 5 (line 124): ASSERT EQ: i32 0 = call i32 @call_readnone_ok()
define i32 @ub_case_5() {
  %r = call i32 @call_readnone_ok()
  ret i32 %r
}

; case 6 (line 159): ASSERT EQ: i32 5 = call i32 @captures_default_ok()
define i32 @ub_case_6() {
  %r = call i32 @captures_default_ok()
  ret i32 %r
}

; case 7 (line 171): ASSERT UB 167: call i32 @captures_address_load()
define i32 @ub_case_7() {
  %r = call i32 @captures_address_load()
  ret i32 %r
}

; case 8 (line 187): ASSERT EQ: i32 1 = call i32 @captures_address_compare_ok()
define i32 @ub_case_8() {
  %r = call i32 @captures_address_compare_ok()
  ret i32 %r
}

; case 9 (line 197): ASSERT UB 193: call i32 @captures_none_store()
define i32 @ub_case_9() {
  %r = call i32 @captures_none_store()
  ret i32 %r
}

; case 10 (line 209): ASSERT EQ: i32 5 = call i32 @captures_read_provenance_load_ok()
define i32 @ub_case_10() {
  %r = call i32 @captures_read_provenance_load_ok()
  ret i32 %r
}

; case 11 (line 219): ASSERT UB 215: call i32 @captures_read_provenance_store()
define i32 @ub_case_11() {
  %r = call i32 @captures_read_provenance_store()
  ret i32 %r
}

; case 12 (line 230): ASSERT EQ: i32 6 = call i32 @captures_original_ok()
define i32 @ub_case_12() {
  %r = call i32 @captures_original_ok()
  ret i32 %r
}

; case 13 (line 241): ASSERT UB 237: call i32 @captures_none_callsite()
define i32 @ub_case_13() {
  %r = call i32 @captures_none_callsite()
  ret i32 %r
}

; case 14 (line 255): ASSERT UB 251: call i32 @captures_none_returned()
define i32 @ub_case_14() {
  %r = call i32 @captures_none_returned()
  ret i32 %r
}

; case 15 (line 272): ASSERT UB 262: call i32 @call_nofree_frees()
define i32 @ub_case_15() {
  %r = call i32 @call_nofree_frees()
  ret i32 %r
}

; case 16 (line 286): ASSERT EQ: i32 0 = call i32 @call_nofree_frees_other_ok()
define i32 @ub_case_16() {
  %r = call i32 @call_nofree_frees_other_ok()
  ret i32 %r
}

; case 17 (line 304): ASSERT UB 293: call i32 @call_noalias_conflict()
define i32 @ub_case_17() {
  %r = call i32 @call_noalias_conflict()
  ret i32 %r
}

; case 18 (line 313): ASSERT EQ: i32 1 = call i32 @call_noalias_disjoint_ok()
define i32 @ub_case_18() {
  %r = call i32 @call_noalias_disjoint_ok()
  ret i32 %r
}

; case 19 (line 330): ASSERT EQ: i32 4 = call i32 @call_noalias_read_only_ok()
define i32 @ub_case_19() {
  %r = call i32 @call_noalias_read_only_ok()
  ret i32 %r
}

; case 20 (line 345): ASSERT UB 335: call i32 @call_init_volatile()
define i32 @ub_case_20() {
  %r = call i32 @call_init_volatile()
  ret i32 %r
}

; case 21 (line 358): ASSERT UB 348: call i32 @call_init_atomic()
define i32 @ub_case_21() {
  %r = call i32 @call_init_atomic()
  ret i32 %r
}

; case 22 (line 374): ASSERT EQ: i32 2 = call i32 @call_init_then_volatile_ok()
define i32 @ub_case_22() {
  %r = call i32 @call_init_then_volatile_ok()
  ret i32 %r
}

; case 23 (line 391): ASSERT EQ: i32 poison = call i32 @call_init_reads_first()
define i32 @ub_case_23() {
  %r = call i32 @call_init_reads_first()
  ret i32 %r
}

; case 24 (line 406): ASSERT UB 402: call i32 @call_writable_constant()
define i32 @ub_case_24() {
  %r = call i32 @call_writable_constant()
  ret i32 %r
}

; case 25 (line 414): ASSERT EQ: i32 0 = call i32 @call_writable_ok()
define i32 @ub_case_25() {
  %r = call i32 @call_writable_ok()
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
bad:
  ret i32 2
}
; ---- END executable tail ----
