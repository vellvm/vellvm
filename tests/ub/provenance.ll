; UB tests for the pointer provenance rules (Pointer Aliasing Rules).
;
; LangRef (Allocated Objects): "the bytes stored in the region can only be read
; or written through a pointer that is based on the allocation value. If a
; pointer that is not based on the object tries to read or write to the
; object, it is undefined behavior."
; LangRef (Pointer Aliasing Rules): "A pointer value formed from a scalar
; getelementptr operation is based on the pointer-typed operand of the
; getelementptr."  "A pointer value formed by an inttoptr is based on all
; pointer values that contribute (directly or indirectly) to the computation
; of the pointer's value."  "An integer constant other than zero ... may be
; associated with address ranges allocated through mechanisms other than those
; provided by LLVM.  Such ranges shall not overlap with any ranges of addresses
; allocated by mechanisms provided by LLVM."
; LangRef (Allocated Objects): "realloc-style operations ... create a new
; allocated object. Even if the object is at the same location as the old one,
; old pointers cannot be used to access this new object."

declare ptr @malloc(i64)
declare void @free(ptr)

@g1 = global i32 1
@g2 = global i32 2

; gep from one object lands exactly on another: the address is right, the
; provenance is wrong.
define i32 @cross_object_gep() {
  %p = alloca i32
  %q = alloca i32
  store i32 5, ptr %q
  %pi = ptrtoint ptr %p to i64
  %qi = ptrtoint ptr %q to i64
  %d = sub i64 %qi, %pi
  %r = getelementptr i8, ptr %p, i64 %d
  %v = load i32, ptr %r                           ; <- UB @cross_object_gep
  ret i32 %v
}

; ASSERT UB 35: call i32 @cross_object_gep()

define i32 @cross_object_gep_store() {
  %p = alloca i32
  %q = alloca i32
  %pi = ptrtoint ptr %p to i64
  %qi = ptrtoint ptr %q to i64
  %d = sub i64 %qi, %pi
  %r = getelementptr i8, ptr %p, i64 %d
  store i32 1, ptr %r                             ; <- UB @cross_object_gep_store
  ret i32 0
}

; ASSERT UB 48: call i32 @cross_object_gep_store()

; Same thing between two globals.
define i32 @cross_global_gep() {
  %pi = ptrtoint ptr @g1 to i64
  %qi = ptrtoint ptr @g2 to i64
  %d = sub i64 %qi, %pi
  %r = getelementptr i8, ptr @g1, i64 %d
  %v = load i32, ptr %r                           ; <- UB @cross_global_gep
  ret i32 %v
}

; ASSERT UB 60: call i32 @cross_global_gep()

; Control: a round trip through ptrtoint/inttoptr keeps the provenance of the
; only contributing pointer.
define i32 @inttoptr_roundtrip_ok() {
  %q = alloca i32
  store i32 5, ptr %q
  %qi = ptrtoint ptr %q to i64
  %r = inttoptr i64 %qi to ptr
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @inttoptr_roundtrip_ok()

; Control: inttoptr of (p + (q - p)) is based on both %p and %q (both
; contribute to the integer), so the access to %q is allowed.  Contrast with
; @cross_object_gep, where gep's result is based on %p only.
define i32 @inttoptr_multi_based_ok() {
  %p = alloca i32
  %q = alloca i32
  store i32 5, ptr %q
  %pi = ptrtoint ptr %p to i64
  %qi = ptrtoint ptr %q to i64
  %d = sub i64 %qi, %pi
  %ri = add i64 %pi, %d
  %r = inttoptr i64 %ri to ptr
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @inttoptr_multi_based_ok()

; An integer constant is associated only with memory not allocated by LLVM;
; dereferencing it is UB in an LLVM-only program.
define i32 @inttoptr_constant() {
  %r = inttoptr i64 4096 to ptr
  %v = load i32, ptr %r                           ; <- UB @inttoptr_constant
  ret i32 %v
}

; ASSERT UB 101: call i32 @inttoptr_constant()

; Address 0 is null's address, which LangRef says "is associated with no
; address", so nothing may be allocated there.  `inttoptr i64 0` has no
; specific provenance, so this load would quietly succeed if some object
; (a function, global, or alloca) had been placed at address 0, as Vellvm's
; allocator once did.
define i64 @inttoptr_zero_load() {
  %r = inttoptr i64 0 to ptr
  %v = load i64, ptr %r                           ; <- UB @inttoptr_zero_load
  ret i64 %v
}

; ASSERT UB 114: call i64 @inttoptr_zero_load()

; Control: no allocated object compares equal to null.
define i32 @objects_not_null() {
  %a = alloca i32
  %h = call ptr @malloc(i64 4)
  %c1 = icmp eq ptr @objects_not_null, null
  %c2 = icmp eq ptr @g1, null
  %c3 = icmp eq ptr %a, null
  %c4 = icmp eq ptr %h, null
  %o1 = or i1 %c1, %c2
  %o2 = or i1 %c3, %c4
  %o = or i1 %o1, %o2
  %r = zext i1 %o to i32
  ret i32 %r
}

; ASSERT EQ: i32 0 = call i32 @objects_not_null()

; Old pointers cannot access a new allocation, even at the same address.
define i32 @stale_heap_pointer() {
  %p = call ptr @malloc(i64 4)
  call void @free(ptr %p)
  %q = call ptr @malloc(i64 4)
  store i32 3, ptr %q
  %v = load i32, ptr %p                           ; <- UB @stale_heap_pointer
  ret i32 %v
}

; ASSERT UB 143: call i32 @stale_heap_pointer()

; Same for a popped stack frame whose slot is reused by a later call.
define ptr @escape_local() {
  %p = alloca i32
  ret ptr %p
}

define i32 @reuse_local(i32 %x) {
  %p = alloca i32
  store i32 %x, ptr %p
  %v = load i32, ptr %p
  ret i32 %v
}

define i32 @stale_stack_pointer() {
  %p = call ptr @escape_local()
  %u = call i32 @reuse_local(i32 9)
  store i32 1, ptr %p                             ; <- UB @stale_stack_pointer
  ret i32 0
}

; ASSERT UB 165: call i32 @stale_stack_pointer()

; Control: a pointer stored to memory and loaded back keeps its provenance.
define i32 @ptr_through_memory_ok() {
  %q = alloca i32
  store i32 5, ptr %q
  %slot = alloca ptr
  store ptr %q, ptr %slot
  %r = load ptr, ptr %slot
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @ptr_through_memory_ok()

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 39): ASSERT UB 35: call i32 @cross_object_gep()
define i32 @ub_case_0() {
  %r = call i32 @cross_object_gep()
  ret i32 %r
}

; case 1 (line 52): ASSERT UB 48: call i32 @cross_object_gep_store()
define i32 @ub_case_1() {
  %r = call i32 @cross_object_gep_store()
  ret i32 %r
}

; case 2 (line 64): ASSERT UB 60: call i32 @cross_global_gep()
define i32 @ub_case_2() {
  %r = call i32 @cross_global_gep()
  ret i32 %r
}

; case 3 (line 77): ASSERT EQ: i32 5 = call i32 @inttoptr_roundtrip_ok()
define i32 @ub_case_3() {
  %r = call i32 @inttoptr_roundtrip_ok()
  ret i32 %r
}

; case 4 (line 95): ASSERT EQ: i32 5 = call i32 @inttoptr_multi_based_ok()
define i32 @ub_case_4() {
  %r = call i32 @inttoptr_multi_based_ok()
  ret i32 %r
}

; case 5 (line 105): ASSERT UB 101: call i32 @inttoptr_constant()
define i32 @ub_case_5() {
  %r = call i32 @inttoptr_constant()
  ret i32 %r
}

; case 6 (line 118): ASSERT UB 114: call i64 @inttoptr_zero_load()
define i64 @ub_case_6() {
  %r = call i64 @inttoptr_zero_load()
  ret i64 %r
}

; case 7 (line 135): ASSERT EQ: i32 0 = call i32 @objects_not_null()
define i32 @ub_case_7() {
  %r = call i32 @objects_not_null()
  ret i32 %r
}

; case 8 (line 147): ASSERT UB 143: call i32 @stale_heap_pointer()
define i32 @ub_case_8() {
  %r = call i32 @stale_heap_pointer()
  ret i32 %r
}

; case 9 (line 169): ASSERT UB 165: call i32 @stale_stack_pointer()
define i32 @ub_case_9() {
  %r = call i32 @stale_stack_pointer()
  ret i32 %r
}

; case 10 (line 182): ASSERT EQ: i32 5 = call i32 @ptr_through_memory_ok()
define i32 @ub_case_10() {
  %r = call i32 @ptr_through_memory_ok()
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
  %c6_r = call i64 @ub_case_6()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 6)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c6_r)
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
bad:
  ret i32 2
}
; ---- END executable tail ----
