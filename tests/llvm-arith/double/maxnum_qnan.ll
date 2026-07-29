; LANGREF (llvm.maxnum): "If both operands are qNaNs, returns a NaN. If one
; operand is qNaN and another operand is a number, returns the number."
;
; Discriminates the old implementation, which returned a NaN as soon as either
; operand was a NaN.  Note this is not a case of NaN non-determinism: with a
; qNaN operand the LangRef fixes the answer to be the *number*.
;
; The sNaN cases are the ones the LangRef does leave non-deterministic ("return
; a NaN" or "treat the sNaN as a quiet NaN"); we resolve them by returning a
; NaN, which is what max3.ll / max4.ll pin down.

declare double @llvm.maxnum.f64(double, double)
declare float @llvm.maxnum.f32(float, float)

define double @qnan_first() {
  %r = call double @llvm.maxnum.f64(double 0x7FF8000000000000, double 2.0)
  ret double %r
}

define double @qnan_second() {
  %r = call double @llvm.maxnum.f64(double 1.0, double 0x7FF8000000000000)
  ret double %r
}

; A qNaN carrying a payload is still just a qNaN: the number wins.
define double @qnan_payload_first() {
  %r = call double @llvm.maxnum.f64(double 0x7FF8000000000123, double -3.5)
  ret double %r
}

; Both qNaN: a NaN is returned.
define i64 @qnan_both() {
  %r = call double @llvm.maxnum.f64(double 0x7FF8000000000123, double 0x7FF8000000000456)
  %b = bitcast double %r to i64
  ret i64 %b
}

; The qNaN is built by bitcast rather than written as a literal: the frontend
; does not preserve quietness when it narrows a NaN literal to float (it turns
; this qNaN into an sNaN), and an sNaN operand would take the other branch.
define float @qnan_first_f32() {
  %n = bitcast i32 2143289344 to float          ; 0x7FC00000, preferred qNaN
  %r = call float @llvm.maxnum.f32(float %n, float 2.0)
  ret float %r
}

; ASSERT EQ: double 2.0 = call double @qnan_first()
; ASSERT EQ: double 1.0 = call double @qnan_second()
; ASSERT EQ: double -3.5 = call double @qnan_payload_first()
; ASSERT EQ: i64 9221120237041090851 = call i64 @qnan_both()
; ASSERT EQ: float 2.0 = call float @qnan_first_f32()
