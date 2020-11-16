define double @src() {
  %t = sitofp i32 undef to double
  ret double %t
}

define double @tgt() {
  ret double undef
}

; ERROR: Value mismatch

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
