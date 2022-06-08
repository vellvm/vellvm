;*******************************************************************************
; Convert fp32 in IEEE 32-bit floating-point format to truncated signed integer.
;
define i64 @fp32_to_int(i64 %fp32) {
  %neg = alloca i1      ; sign bit of fp32
  %bits = alloca i64    ; bits of fp32 without the sign bit
  %exp = alloca i64     ; expoent
  %int = alloca i64     ; integer part of fp32
  %nbits = alloca i64   ; number of bits after the dot if 2^exp is applied
  %fract = alloca i64   ; mantissa of fp32

  ; neg = fp32 & 0x80000000
  %1 = and i64 %fp32, 2147483648  ; 0x80000000
  %2 = icmp ne i64 %1, 0
  store i1 %2, i1* %neg

  ; bits = fp32 & 0x7FFFFFFF
  %3 = and i64 %fp32, 2147483647  ; 0x7FFFFFFF
  store i64 %3, i64* %bits

  ; exp = bits >> 23
  %4 = load i64, i64* %bits
  %5 = lshr i64 %4, 23
  store i64 %5, i64* %exp

  ; exp -= 127
  %6 = load i64, i64* %exp
  %7 = sub i64 %6, 127
  store i64 %7, i64* %exp

  ; int = 0
  store i64 0, i64* %int

  ; bits > 0
  %8 = load i64, i64* %bits
  %9 = icmp sgt i64 %8, 0
  br i1 %9, label %check_exponent, label %check_sign

check_exponent:         ; preds = %1
  ; exp >= 0
  %10 = load i64, i64* %exp
  %11 = icmp sge i64 %10, 0
  br i1 %11, label %compute, label %check_sign

compute:                ; preds = %check_exponent
  ; nbits = 23 - exp
  %12 = load i64, i64* %exp
  %13 = sub i64 23, %12
  store i64 %13, i64* %nbits

  ; fract = bits & 0x7FFFFF
  %14 = load i64, i64* %bits
  %15 = and i64 %14, 8388607  ; 0x7FFFFF
  store i64 %15, i64* %fract

  ; fract |= 0x800000
  %16 = load i64, i64* %fract
  %17 = or i64 %16, 8388608   ; 0x800000
  store i64 %17, i64* %fract

  ; nbits > 0
  %18 = load i64, i64* %nbits
  %19 = icmp sgt i64 %18, 0
  br i1 %19, label %shift_right, label %shift_left

shift_right:            ; preds = %compute
  ; int = fract >> nbits
  %20 = load i64, i64* %fract
  %21 = load i64, i64* %nbits
  %22 = lshr i64 %20, %21
  store i64 %22, i64* %int
  br label %check_sign

shift_left:             ; preds = %compute
  ; int = fraction << -nbits
  %23 = load i64, i64* %fract
  %24 = load i64, i64* %nbits
  %25 = sub i64 0, %24
  %26 = shl i64 %23, %25
  store i64 %26, i64* %int
  br label %check_sign

check_sign:             ; preds = %shift_left, %shift_right, %check_exponent, %1
  ; neg > 0
  %27 = load i1, i1* %neg
  br i1 %27, label %negate, label %return

negate:                 ; preds = %check_sign
  ; int = -int
  %28 = load i64, i64* %int
  %29 = sub i64 0, %28
  store i64 %29, i64* %int
  br label %return

return:                 ; preds = %negate, %check_sign
  ; return int
  %30 = load i64, i64* %int
  ret i64 %30
}

define i64 @main(i64 %argc, i8** %argv) {
  %int = call i64 @fp32_to_int(i64 1132389990)  ; 0x437EE666: 254.9
  ret i64 %int
}
