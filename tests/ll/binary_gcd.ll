define i64 @binary_gcd(i64 %u, i64 %v) {
  %u_eq_v = icmp eq i64 %u, %v
  br i1 %u_eq_v, label %ret_u, label %term1

term1:
  %u_0 = icmp eq i64 0, %u
  br i1 %u_0, label %ret_v, label %term2

term2:
  %v_0 = icmp eq i64 0, %v
  br i1 %v_0, label %ret_u, label %gcd

gcd:
  %neg1 = sub i64 0, 1
  %1 = xor i64 %neg1, %u
  %2 = and i64 1, %1
  %3 = icmp ne i64 0, %2
  br i1 %3, label %u_even, label %u_odd

u_odd:
  %4 = xor i64 %neg1, %v
  %5 = and i64 1, %4
  %6 = icmp ne i64 0, %5
  br i1 %6, label %v_even, label %v_odd

v_odd:
  %7 = icmp sgt i64 %u, %v
  br i1 %7, label %u_gt, label %v_gt

v_gt:
  %8 = sub i64 %v, %u
  %9 = lshr i64 %8, 1
  %10 = call i64 @binary_gcd(i64 %9, i64 %u)
  ret i64 %10

u_gt:
  %11 = sub i64 %u, %v
  %12 = lshr i64 %11, 1
  %13 = call i64 @binary_gcd(i64 %12, i64 %v)
  ret i64 %13

v_even:
  %14 = lshr i64 %v, 1
  %15 = call i64 @binary_gcd(i64 %u, i64 %14)
  ret i64 %15

u_even:
  %16 = and i64 %v, 1
  %17 = icmp ne i64 0, %16
  br i1 %17, label %ue_vo, label %both_even

ue_vo:
  %18 = lshr i64 %u, 1
  %19 = call i64 @binary_gcd(i64 %18, i64 %v)
  ret i64 %19

both_even:
  %20 = lshr i64 %u, 1
  %21 = lshr i64 %v, 1
  %22 = call i64 @binary_gcd(i64 %20, i64 %21)
  %23 = shl i64 %22, 1
  ret i64 %23

ret_u:
  ret i64 %u

ret_v:
  ret i64 %v
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @binary_gcd(i64 21, i64 15)
  ret i64 %1
}
