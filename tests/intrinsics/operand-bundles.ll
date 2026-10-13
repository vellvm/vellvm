; Operand bundles belong to the call, not to the callee.  A bundle tag that
; states a guarantee on llvm.assume (here "nonnull") means nothing on a call
; to another function, so a null operand is not undefined behavior.
;
; (Kept out of tests/ub: clang -O1 and above cannot lower an assume-style
; bundle on an ordinary call, so the file would not build natively.)

define void @not_assume() {
  ret void
}

define i32 @nonnull_bundle_other_callee() {
  call void @not_assume() [ "nonnull"(ptr null) ]
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @nonnull_bundle_other_callee()

; Operands of any bundle are evaluated at the call, poison included, without
; further meaning.
define i32 @poison_bundle_operand() {
  call void @not_assume() [ "deopt"(i32 poison) ]
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @poison_bundle_operand()
