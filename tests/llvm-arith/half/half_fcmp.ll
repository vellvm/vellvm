; fcmp at type half.  Same shape as the float and double cases: the ordered
; predicates conjoin with "neither operand is a NaN", the unordered ones
; disjoin with its negation.

define i1 @olt() {
  %r = fcmp olt half 0xH3C00, 0xH4000
  ret i1 %r
}

define i1 @ogt() {
  %r = fcmp ogt half 0xH4000, 0xH3C00
  ret i1 %r
}

; Signed zeros compare equal.
define i1 @signed_zeros_eq() {
  %r = fcmp oeq half 0xH8000, 0xH0000
  ret i1 %r
}

; An ordered predicate is false whenever either operand is a NaN, even against
; itself.
define i1 @oeq_nan() {
  %r = fcmp oeq half 0xH7E00, 0xH7E00
  ret i1 %r
}

define i1 @uno_nan() {
  %r = fcmp uno half 0xH7E00, 0xH3C00
  ret i1 %r
}

define i1 @ord_nan() {
  %r = fcmp ord half 0xH7E00, 0xH3C00
  ret i1 %r
}

; The unordered form is true precisely because of the NaN.
define i1 @ueq_nan() {
  %r = fcmp ueq half 0xH7E00, 0xH3C00
  ret i1 %r
}

; A signaling NaN is still a NaN for comparison purposes.
define i1 @uno_snan() {
  %r = fcmp uno half 0xH7C01, 0xH3C00
  ret i1 %r
}

; Infinities order normally.
define i1 @inf_gt_max() {
  %r = fcmp ogt half 0xH7C00, 0xH7BFF
  ret i1 %r
}

define i1 @neg_inf_lt_zero() {
  %r = fcmp olt half 0xHFC00, 0xH0000
  ret i1 %r
}

; ASSERT EQ: i1 1 = call i1 @olt()
; ASSERT EQ: i1 1 = call i1 @ogt()
; ASSERT EQ: i1 1 = call i1 @signed_zeros_eq()
; ASSERT EQ: i1 0 = call i1 @oeq_nan()
; ASSERT EQ: i1 1 = call i1 @uno_nan()
; ASSERT EQ: i1 0 = call i1 @ord_nan()
; ASSERT EQ: i1 1 = call i1 @ueq_nan()
; ASSERT EQ: i1 1 = call i1 @uno_snan()
; ASSERT EQ: i1 1 = call i1 @inf_gt_max()
; ASSERT EQ: i1 1 = call i1 @neg_inf_lt_zero()
