;; This example is accepted by clang version 11 but (correctly?) rejected by llc version 11
define i64 @f3(i64) {
  br label %1

  ret i64 %0    
}
