define i64 @reverse(i64 %input_x) {
  %rev = alloca i64
  store i64 0, i64* %rev

  %x = alloca i64
  store i64 %input_x, i64 %x

  br label %loop

loop:
  %x_val_to_comp = load i64, i64* %x
  %x_not_zero = icmp ne i64 %x_val_to_comp, 0
  br i1 %x_not_zero, label %yes, label %no

yes:
  %x_val = load i64, i64* %x
  %rev_val = load i64, i64* %rev

  %twice_rev = shl i64 %rev_val, 1

  %x_val_last_bit = and i64 %x_val, 1
  %twice_rev_plus_last_bit = add i64 %twice_rev, %x_val_last_bit

  %half_x_val = lshr i64 %x_val, 1
  
  store i64 %half_x_val, i64 %x
  store i64 %twice_rev_plus_last_bit, i64 %rev

  br label %loop

no:
  %ret_val_rev = load i64, i64* %rev
  ret i64 %ret_val_rev
}

define i64 @is_binary_palindrome(i64 %input_x) {
  %reversed_x = call i64 @reverse(i64 %input_x)
  %x_equals_reverse = icmp eq i64 %reversed_x, %input_x
  br i1 %x_equals_reverse, label %retyes, label %retno
retyes:
  ret i64 1
retno:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %argv) {
  %res = call i64 @is_binary_palindrome(i64 819)
  ret i64 %res
}