; LANGREF: for both llvm.maxnum and llvm.minimum, "-0.0 is considered to be
; less than +0.0 for this intrinsic".  So maxnum(-0.0, +0.0) is +0.0 and
; minimum(-0.0, +0.0) is -0.0, in either argument order.
;
; Discriminates the old implementations, which decided with a bare
; `cmp Clt`: since -0.0 and +0.0 compare equal under IEEE ordering, the answer
; degenerated to "the first argument", which is right in one order and wrong in
; the other.  Results are bitcast to integers because +0.0 and -0.0 compare
; equal as floats -- the sign bit is exactly what is under test.

declare double @llvm.maxnum.f64(double, double)
declare double @llvm.minimum.f64(double, double)
declare float @llvm.minimum.f32(float, float)

define i64 @max_neg_pos() {
  %r = call double @llvm.maxnum.f64(double -0.0, double 0.0)
  %b = bitcast double %r to i64
  ret i64 %b
}

define i64 @max_pos_neg() {
  %r = call double @llvm.maxnum.f64(double 0.0, double -0.0)
  %b = bitcast double %r to i64
  ret i64 %b
}

define i64 @min_neg_pos() {
  %r = call double @llvm.minimum.f64(double -0.0, double 0.0)
  %b = bitcast double %r to i64
  ret i64 %b
}

define i64 @min_pos_neg() {
  %r = call double @llvm.minimum.f64(double 0.0, double -0.0)
  %b = bitcast double %r to i64
  ret i64 %b
}

; llvm.minimum.f32 was registered under the name "minimum.f32", without the
; "llvm." prefix, so calls to it never resolved to the intrinsic.  This
; exercises the f32 variant at all.
define i32 @min_f32_neg_pos() {
  %r = call float @llvm.minimum.f32(float -0.0, float 0.0)
  %b = bitcast float %r to i32
  ret i32 %b
}

; +0.0 is 0; -0.0 is the sign bit alone.
; ASSERT EQ: i64 0 = call i64 @max_neg_pos()
; ASSERT EQ: i64 0 = call i64 @max_pos_neg()
; ASSERT EQ: i64 -9223372036854775808 = call i64 @min_neg_pos()
; ASSERT EQ: i64 -9223372036854775808 = call i64 @min_pos_neg()
; ASSERT EQ: i32 -2147483648 = call i32 @min_f32_neg_pos()
