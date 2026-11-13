; UB tests: `getelementptr` into a vector whose elements are not
; byte-addressable.
;
; A vector <N x iM> is bit-packed (LangRef, vector type, "Memory Layout"):
; when M is not a multiple of 8, its elements have no addresses of their own.
; LLVM's verifier (as of LLVM 23) rejects a GEP that indexes into such a
; vector: "GEP into vector with non-byte-addressable element type".  An
; element type is byte-addressable when its size in bits equals its store
; size in bits (i8, i24, float, ptr, ... but not i1, i4, i12).
;
; So this file is NOT valid LLVM IR, and clang/llubi reject it outright; it
; runs only under Vellvm.  Since no well-formed program can perform such a
; GEP, Vellvm treats one as immediate undefined behavior, raised by the
; `getelementptr` itself, whether or not the result is used.
;
; Stepping over *whole* packed vectors (the first GEP index, or an index into
; an array of vectors) is fine; only indexing into the vector is UB.  The
; controls check that, and that byte-addressable elements (<3 x i24>,
; <4 x i8>) can still be indexed.

; ---------------------------------------------------------------- UB cases

define i64 @gep_v8i1_i64() {
  %p = alloca <8 x i1>
  %q = getelementptr <8 x i1>, ptr %p, i64 0, i64 3   ; <- UB @gep_v8i1_i64
  ret i64 0
}

; ASSERT UB 25: call i64 @gep_v8i1_i64()

; the index type does not matter
define i64 @gep_v8i1_i32() {
  %p = alloca <8 x i1>
  %q = getelementptr <8 x i1>, ptr %p, i32 0, i32 3   ; <- UB @gep_v8i1_i32
  ret i64 0
}

; ASSERT UB 34: call i64 @gep_v8i1_i32()

define i64 @gep_v8i1_i8() {
  %p = alloca <8 x i1>
  %q = getelementptr <8 x i1>, ptr %p, i8 0, i8 3     ; <- UB @gep_v8i1_i8
  ret i64 0
}

; ASSERT UB 42: call i64 @gep_v8i1_i8()

; index 0 too: the element still has no address of its own
define i64 @gep_v3i12_zero() {
  %p = alloca <3 x i12>
  %q = getelementptr <3 x i12>, ptr %p, i64 0, i64 0  ; <- UB @gep_v3i12_zero
  ret i64 0
}

; ASSERT UB 51: call i64 @gep_v3i12_zero()

; a run-time index
define i64 @gep_v4i6_dynamic(i64 %k) {
  %p = alloca <4 x i6>
  %q = getelementptr <4 x i6>, ptr %p, i64 0, i64 %k  ; <- UB @gep_v4i6_dynamic
  ret i64 0
}

; ASSERT UB 60: call i64 @gep_v4i6_dynamic(i64 2)

; a poison index is no excuse
; ASSERT UB 60: call i64 @gep_v4i6_dynamic(i64 poison)

; nested: through an array, into the vector
define i64 @gep_nested_array(i64 %k) {
  %p = alloca [2 x <4 x i6>]
  %q = getelementptr [2 x <4 x i6>], ptr %p, i64 0, i64 1, i64 %k  ; <- UB @gep_nested_array
  ret i64 0
}

; ASSERT UB 72: call i64 @gep_nested_array(i64 0)

; nested: through a struct, into the vector
%s = type { i32, <16 x i1> }

define i64 @gep_nested_struct() {
  %p = alloca %s
  %q = getelementptr %s, ptr %p, i64 0, i32 1, i32 9  ; <- UB @gep_nested_struct
  ret i64 0
}

; ASSERT UB 83: call i64 @gep_nested_struct()

; byte vectors with sub-byte width: b4 is no more addressable than i4
define i64 @gep_v2b4() {
  %p = alloca <2 x b4>
  %q = getelementptr <2 x b4>, ptr %p, i64 0, i64 1   ; <- UB @gep_v2b4
  ret i64 0
}

; ASSERT UB 92: call i64 @gep_v2b4()

; ---------------------------------------------------------------- controls

; stepping over whole <8 x i1>s is fine (alloc size 1)
define i64 @gep_over_v8i1() {
  %p = alloca [4 x <8 x i1>]
  store [4 x <8 x i1>] [<8 x i1> zeroinitializer, <8 x i1> zeroinitializer,
                        <8 x i1> <i1 1, i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0>,
                        <8 x i1> zeroinitializer], ptr %p
  %q = getelementptr <8 x i1>, ptr %p, i64 2
  %v = load <8 x i1>, ptr %q
  %b = bitcast <8 x i1> %v to i8
  %r = zext i8 %b to i64
  ret i64 %r
}

; ASSERT EQ: i64 3 = call i64 @gep_over_v8i1()

; indexing an array of packed vectors (but not into the vectors) is fine
define i64 @gep_array_of_v4i6() {
  %p = alloca [2 x <4 x i6>]
  %q = getelementptr [2 x <4 x i6>], ptr %p, i64 0, i64 1
  store <4 x i6> <i6 5, i6 0, i6 0, i6 0>, ptr %q
  %v = load <4 x i6>, ptr %q
  %e = extractelement <4 x i6> %v, i32 0
  %r = zext i6 %e to i64
  ret i64 %r
}

; ASSERT EQ: i64 5 = call i64 @gep_array_of_v4i6()

; i24 is byte-addressable (24 bits = 3 bytes), so <3 x i24> can be indexed;
; element 2 is at byte 6 (vector elements are at their store size)
define i64 @gep_into_v3i24() {
  %p = alloca <3 x i24>
  %q = getelementptr <3 x i24>, ptr %p, i64 0, i64 2
  %i = ptrtoint ptr %q to i64
  %j = ptrtoint ptr %p to i64
  %d = sub i64 %i, %j
  ret i64 %d
}

; ASSERT EQ: i64 6 = call i64 @gep_into_v3i24()

define i64 @gep_into_v4i8() {
  %p = alloca <4 x i8>
  store <4 x i8> <i8 1, i8 2, i8 3, i8 4>, ptr %p
  %q = getelementptr <4 x i8>, ptr %p, i64 0, i64 2
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; ASSERT EQ: i64 3 = call i64 @gep_into_v4i8()

; an array of i1 is not packed: [8 x i1] can be indexed
define i64 @gep_into_array_i1() {
  %p = alloca [8 x i1]
  %q = getelementptr [8 x i1], ptr %p, i64 0, i64 5
  store i1 1, ptr %q
  %v = load i1, ptr %q
  %r = zext i1 %v to i64
  ret i64 %r
}

; ASSERT EQ: i64 1 = call i64 @gep_into_array_i1()

; ---- BEGIN executable tail generated by tests/gen.py --dispatch (do not edit) ----
; `main N` runs case N alone, so UB in one case cannot mask another;
; @ub_case_N is an argument-free entry point for the same call.

; case 0 (line 29): ASSERT UB 25: call i64 @gep_v8i1_i64()
define i64 @ub_case_0() {
  %r = call i64 @gep_v8i1_i64()
  ret i64 %r
}

; case 1 (line 38): ASSERT UB 34: call i64 @gep_v8i1_i32()
define i64 @ub_case_1() {
  %r = call i64 @gep_v8i1_i32()
  ret i64 %r
}

; case 2 (line 46): ASSERT UB 42: call i64 @gep_v8i1_i8()
define i64 @ub_case_2() {
  %r = call i64 @gep_v8i1_i8()
  ret i64 %r
}

; case 3 (line 55): ASSERT UB 51: call i64 @gep_v3i12_zero()
define i64 @ub_case_3() {
  %r = call i64 @gep_v3i12_zero()
  ret i64 %r
}

; case 4 (line 64): ASSERT UB 60: call i64 @gep_v4i6_dynamic(i64 2)
define i64 @ub_case_4() {
  %r = call i64 @gep_v4i6_dynamic(i64 2)
  ret i64 %r
}

; case 5 (line 67): ASSERT UB 60: call i64 @gep_v4i6_dynamic(i64 poison)
define i64 @ub_case_5() {
  %r = call i64 @gep_v4i6_dynamic(i64 poison)
  ret i64 %r
}

; case 6 (line 76): ASSERT UB 72: call i64 @gep_nested_array(i64 0)
define i64 @ub_case_6() {
  %r = call i64 @gep_nested_array(i64 0)
  ret i64 %r
}

; case 7 (line 87): ASSERT UB 83: call i64 @gep_nested_struct()
define i64 @ub_case_7() {
  %r = call i64 @gep_nested_struct()
  ret i64 %r
}

; case 8 (line 96): ASSERT UB 92: call i64 @gep_v2b4()
define i64 @ub_case_8() {
  %r = call i64 @gep_v2b4()
  ret i64 %r
}

; case 9 (line 113): ASSERT EQ: i64 3 = call i64 @gep_over_v8i1()
define i64 @ub_case_9() {
  %r = call i64 @gep_over_v8i1()
  ret i64 %r
}

; case 10 (line 126): ASSERT EQ: i64 5 = call i64 @gep_array_of_v4i6()
define i64 @ub_case_10() {
  %r = call i64 @gep_array_of_v4i6()
  ret i64 %r
}

; case 11 (line 139): ASSERT EQ: i64 6 = call i64 @gep_into_v3i24()
define i64 @ub_case_11() {
  %r = call i64 @gep_into_v3i24()
  ret i64 %r
}

; case 12 (line 150): ASSERT EQ: i64 3 = call i64 @gep_into_v4i8()
define i64 @ub_case_12() {
  %r = call i64 @gep_into_v4i8()
  ret i64 %r
}

; case 13 (line 162): ASSERT EQ: i64 1 = call i64 @gep_into_array_i1()
define i64 @ub_case_13() {
  %r = call i64 @gep_into_array_i1()
  ret i64 %r
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
  %c1_r = call i64 @ub_case_1()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 1)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c1_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case2:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 2)
  %c2_r = call i64 @ub_case_2()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 2)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c2_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case3:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 3)
  %c3_r = call i64 @ub_case_3()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 3)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c3_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case4:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 4)
  %c4_r = call i64 @ub_case_4()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 4)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c4_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case5:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 5)
  %c5_r = call i64 @ub_case_5()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 5)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c5_r)
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
  %c7_r = call i64 @ub_case_7()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 7)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c7_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case8:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 8)
  %c8_r = call i64 @ub_case_8()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 8)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c8_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case9:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 9)
  %c9_r = call i64 @ub_case_9()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 9)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c9_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case10:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 10)
  %c10_r = call i64 @ub_case_10()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 10)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c10_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case11:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 11)
  %c11_r = call i64 @ub_case_11()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 11)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c11_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case12:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 12)
  %c12_r = call i64 @ub_case_12()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 12)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c12_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
case13:
  call i32 (ptr, ...) @printf(ptr @ub_fmt_start, i32 13)
  %c13_r = call i64 @ub_case_13()
  call i32 (ptr, ...) @printf(ptr @ub_fmt_ret, i32 13)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_int, i64 %c13_r)
  call i32 (ptr, ...) @printf(ptr @ub_fmt_nl)
  ret i32 0
bad:
  ret i32 2
}
; ---- END executable tail ----
