; fcmp.ll - Vector floating-point comparison tests.
; Covers all 16 fcmp predicates on <2 x float> vectors.
; NaN is written as float 0x7FF8000000000000 (float32 quiet NaN).
; Each function has test cases showing: typical true/false results, and NaN behaviour.


declare void @puts(i8*)

@yes_str = global [4 x i8] c"yes\00"
@no_str = global [4 x i8] c"no \00"

define void @print_test_case(i8* %name, i1 %pass) {
  call void @puts(i8 * %name)
  br i1 %pass, label %yes, label %no

yes:
  %p = getelementptr [4 x i8], [4 x i8]* @yes_str, i32 0, i32 0
  call void @puts (i8* %p)
  ret void

no:
  %q = getelementptr [4 x i8], [4 x i8]* @no_str, i32 0, i32 0
  call void @puts (i8* %q)
  ret void
}

define <2 x float> @get_zeroinitializer() {
  ret <2 x float> zeroinitializer
}


define void @test_syntax() {
  %test1  = call <2 x i1> @fcmp_false(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test2  = call <2 x i1> @fcmp_false(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)
  %test3  = call <2 x i1> @fcmp_oeq(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test4  = call <2 x i1> @fcmp_oeq(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 0x7FF8000000000000, float 2.0>)
  %test5  = call <2 x i1> @fcmp_ogt(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test6  = call <2 x i1> @fcmp_ogt(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test7  = call <2 x i1> @fcmp_oge(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test8  = call <2 x i1> @fcmp_oge(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test9  = call <2 x i1> @fcmp_oge(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test10 = call <2 x i1> @fcmp_olt(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 2.0, float 1.0>)
  %test11 = call <2 x i1> @fcmp_olt(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)
  %test12 = call <2 x i1> @fcmp_ole(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 2.0, float 1.0>)
  %test13 = call <2 x i1> @fcmp_ole(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test14 = call <2 x i1> @fcmp_ole(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)
  %test15 = call <2 x i1> @fcmp_one(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 2.0, float 1.0>)
  %test16 = call <2 x i1> @fcmp_one(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test17 = call <2 x i1> @fcmp_ord(<2 x float> <float 1.0, float 0x7FF8000000000000>, <2 x float> <float 2.0, float 1.0>)
  %test18 = call <2 x i1> @fcmp_ord(<2 x float> <float 0x7FF8000000000000, float 0x7FF8000000000000>, <2 x float> <float 1.0, float 1.0>)
  %test19 = call <2 x i1> @fcmp_ueq(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test20 = call <2 x i1> @fcmp_ueq(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test21 = call <2 x i1> @fcmp_ugt(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test22 = call <2 x i1> @fcmp_ugt(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)
  %test23 = call <2 x i1> @fcmp_uge(<2 x float> <float 2.0, float 0.0>, <2 x float> <float 1.0, float 1.0>)
  %test24 = call <2 x i1> @fcmp_uge(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test25 = call <2 x i1> @fcmp_uge(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)
  %test26 = call <2 x i1> @fcmp_ult(<2 x float> <float 0.0, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test27 = call <2 x i1> @fcmp_ult(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test28 = call <2 x i1> @fcmp_ule(<2 x float> <float 0.0, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test29 = call <2 x i1> @fcmp_ule(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test30 = call <2 x i1> @fcmp_ule(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)
  %test31 = call <2 x i1> @fcmp_une(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)
  %test32 = call <2 x i1> @fcmp_une(<2 x float> <float 1.0, float 0.0>, <2 x float> <float 1.0, float 0.0>)
  %test33 = call <2 x i1> @fcmp_une(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test34 = call <2 x i1> @fcmp_uno(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)
  %test35 = call <2 x i1> @fcmp_uno(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0x7FF8000000000000, float 1.0>)
  %test36 = call <2 x i1> @fcmp_true(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
  %test37 = call <2 x i1> @fcmp_true(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)
  ret void
}  


; ---------- false: no comparison, always returns false ----------

define <2 x i1> @fcmp_false(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp false <2 x float> %v, %w
  ret <2 x i1> %ans
}

; ASSERT EQ: <2 x i1> <i1 0, i1 0> = call <2 x i1> @fcmp_false(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; ASSERT EQ: <2 x i1> <i1 0, i1 0> = call <2 x i1> @fcmp_false(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)


; ---------- oeq: ordered and equal ----------

define <2 x i1> @fcmp_oeq(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp oeq <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0==1.0 true, 1.0==2.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_oeq(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; NaN==NaN → false (ordered requires no NaN); 2.0==2.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_oeq(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 0x7FF8000000000000, float 2.0>)


; ---------- ogt: ordered and greater than ----------

define <2 x i1> @fcmp_ogt(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ogt <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 2.0>1.0 true, 1.0>2.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ogt(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; NaN>1.0 → false; 2.0>1.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_ogt(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- oge: ordered and greater than or equal ----------

define <2 x i1> @fcmp_oge(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp oge <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 2.0>=1.0 true, 1.0>=2.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_oge(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; equal → true
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_oge(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; NaN>=1.0 → false; 2.0>=1.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_oge(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- olt: ordered and less than ----------

define <2 x i1> @fcmp_olt(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp olt <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0<2.0 true, 2.0<1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_olt(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 2.0, float 1.0>)
; NaN<1.0 → false; 0.0<1.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_olt(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- ole: ordered and less than or equal ----------

define <2 x i1> @fcmp_ole(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ole <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0<=2.0 true, 2.0<=1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ole(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 2.0, float 1.0>)
; equal → true
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_ole(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; NaN<=1.0 → false; 0.0<=1.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_ole(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- one: ordered and not equal ----------

define <2 x i1> @fcmp_one(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp one <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0!=2.0 true, 1.0!=1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_one(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 2.0, float 1.0>)
; NaN!=1.0 → false (ordered); 1.0!=2.0 → true
; ASSERT EQ: <2 x i1> <i1 0, i1 1> = call <2 x i1> @fcmp_one(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)


; ---------- ord: ordered (neither operand is NaN) ----------

define <2 x i1> @fcmp_ord(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ord <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0 ord 2.0 → true; NaN ord 1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ord(<2 x float> <float 1.0, float 0x7FF8000000000000>, <2 x float> <float 2.0, float 1.0>)
; both NaN → false
; ASSERT EQ: <2 x i1> <i1 0, i1 0> = call <2 x i1> @fcmp_ord(<2 x float> <float 0x7FF8000000000000, float 0x7FF8000000000000>, <2 x float> <float 1.0, float 1.0>)


; ---------- ueq: unordered or equal ----------

define <2 x i1> @fcmp_ueq(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ueq <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 1.0==1.0 true, 1.0==2.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ueq(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; NaN → true (unordered); 1.0==2.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ueq(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)


; ---------- ugt: unordered or greater than ----------

define <2 x i1> @fcmp_ugt(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ugt <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 2.0>1.0 true, 1.0>2.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ugt(<2 x float> <float 2.0, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; NaN → true (unordered); 0.0>1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ugt(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- uge: unordered or greater than or equal ----------

define <2 x i1> @fcmp_uge(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp uge <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 2.0>=1.0 true, 0.0>=1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_uge(<2 x float> <float 2.0, float 0.0>, <2 x float> <float 1.0, float 1.0>)
; equal → true
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_uge(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; NaN → true (unordered); 0.0>=1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_uge(<2 x float> <float 0x7FF8000000000000, float 0.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- ult: unordered or less than ----------

define <2 x i1> @fcmp_ult(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ult <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 0.0<1.0 true, 2.0<1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ult(<2 x float> <float 0.0, float 2.0>, <2 x float> <float 1.0, float 1.0>)
; NaN → true (unordered); 2.0<1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ult(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- ule: unordered or less than or equal ----------

define <2 x i1> @fcmp_ule(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp ule <2 x float> %v, %w
  ret <2 x i1> %ans
}

; 0.0<=1.0 true, 2.0<=1.0 false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ule(<2 x float> <float 0.0, float 2.0>, <2 x float> <float 1.0, float 1.0>)
; equal → true
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_ule(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; NaN → true (unordered); 2.0<=1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_ule(<2 x float> <float 0x7FF8000000000000, float 2.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- une: unordered or not equal ----------

define <2 x i1> @fcmp_une(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp une <2 x float> %v, %w
  ret <2 x i1> %ans
}

; both nonzero vs zero → true (not equal)
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_une(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)
; equal → false
; ASSERT EQ: <2 x i1> <i1 0, i1 0> = call <2 x i1> @fcmp_une(<2 x float> <float 1.0, float 0.0>, <2 x float> <float 1.0, float 0.0>)
; NaN → true (unordered); 1.0!=1.0 → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_une(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 1.0>)


; ---------- uno: unordered (either operand is NaN) ----------

define <2 x i1> @fcmp_uno(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp uno <2 x float> %v, %w
  ret <2 x i1> %ans
}

; NaN in first operand → true; both normal → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_uno(<2 x float> <float 0x7FF8000000000000, float 1.0>, <2 x float> <float 1.0, float 2.0>)
; NaN in second operand → true; both normal → false
; ASSERT EQ: <2 x i1> <i1 1, i1 0> = call <2 x i1> @fcmp_uno(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0x7FF8000000000000, float 1.0>)


; ---------- true: no comparison, always returns true ----------

define <2 x i1> @fcmp_true(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp true <2 x float> %v, %w
  ret <2 x i1> %ans
}

; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_true(<2 x float> <float 1.0, float 1.0>, <2 x float> <float 1.0, float 1.0>)
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_true(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)



; FAILING TEST:
; fcmp.ll: FAILED - <2 x i1> < i1 1, i1 0> = @fcmp_ueq(<2 x float> < float 0x7ff0000020000000, float 0x3ff0000000000000>, <2 x float> < float 0x3ff0000000000000, float 0x4000000000000000>)
; 	   ERROR: ASSERT EQ failed: 
; got:
; 	<2 x i1> < i1 0, i1 0>
; asserted:
; 	<2 x i1> < i1 1, i1 0>

; LLVM FUNCTION:

@t1_str  = global [54 x i8] c"fcmp ueq float 0x7ff0000020000000, 0x3ff0000000000000\00"
@t2_str  = global [54 x i8] c"fcmp ueq float 0x3ff0000000000000, 0x4000000000000000\00"
@t3_str  = global [54 x i8] c"fcmp ugt float 0x7ff0000020000000, 0x3ff0000000000000\00"
@t4_str  = global [39 x i8] c"fcmp ugt float 0x0, 0x3ff0000000000000\00"
@t5_str  = global [54 x i8] c"fcmp uge float 0x7ff0000020000000, 0x3ff0000000000000\00"
@t6_str  = global [39 x i8] c"fcmp uge float 0x0, 0x3ff0000000000000\00"
@t7_str  = global [54 x i8] c"fcmp ult float 0x7ff0000020000000, 0x3ff0000000000000\00"
@t8_str  = global [54 x i8] c"fcmp ult float 0x4000000000000000, 0x3ff0000000000000\00"
@t9_str  = global [54 x i8] c"fcmp ule float 0x7ff0000020000000, 0x3ff0000000000000\00"
@t10_str = global [54 x i8] c"fcmp ule float 0x4000000000000000, 0x3ff0000000000000\00"

define i64 @main(i64 %argc, i8** %argv) {
  %t1 = fcmp ueq float 0x7ff0000020000000, 0x3ff0000000000000
  %name1 = getelementptr [54 x i8], [54 x i8]* @t1_str, i32 0, i32 0
  call void @print_test_case(i8* %name1, i1 %t1)

  %t2 = fcmp ueq float 0x3ff0000000000000, 0x4000000000000000
  %name2 = getelementptr [54 x i8], [54 x i8]* @t2_str, i32 0, i32 0
  call void @print_test_case(i8* %name2, i1 %t2)

  %t3 = fcmp ugt float 0x7ff0000020000000, 0x3ff0000000000000
  %name3 = getelementptr [54 x i8], [54 x i8]* @t3_str, i32 0, i32 0
  call void @print_test_case(i8* %name3, i1 %t3)

  %t4 = fcmp ugt float 0x0, 0x3ff0000000000000
  %name4 = getelementptr [39 x i8], [39 x i8]* @t4_str, i32 0, i32 0
  call void @print_test_case(i8* %name4, i1 %t4)

  %t5 = fcmp uge float 0x7ff0000020000000, 0x3ff0000000000000
  %name5 = getelementptr [54 x i8], [54 x i8]* @t5_str, i32 0, i32 0
  call void @print_test_case(i8* %name5, i1 %t5)

  %t6 = fcmp uge float 0x0, 0x3ff0000000000000
  %name6 = getelementptr [39 x i8], [39 x i8]* @t6_str, i32 0, i32 0
  call void @print_test_case(i8* %name6, i1 %t6)

  %t7 = fcmp ult float 0x7ff0000020000000, 0x3ff0000000000000
  %name7 = getelementptr [54 x i8], [54 x i8]* @t7_str, i32 0, i32 0
  call void @print_test_case(i8* %name7, i1 %t7)

  %t8 = fcmp ult float 0x4000000000000000, 0x3ff0000000000000
  %name8 = getelementptr [54 x i8], [54 x i8]* @t8_str, i32 0, i32 0
  call void @print_test_case(i8* %name8, i1 %t8)

  %t9 = fcmp ule float 0x7ff0000020000000, 0x3ff0000000000000
  %name9 = getelementptr [54 x i8], [54 x i8]* @t9_str, i32 0, i32 0
  call void @print_test_case(i8* %name9, i1 %t9)

  %t10 = fcmp ule float 0x4000000000000000, 0x3ff0000000000000
  %name10 = getelementptr [54 x i8], [54 x i8]* @t10_str, i32 0, i32 0
  call void @print_test_case(i8* %name10, i1 %t10)

  ret i64 0
}






  
