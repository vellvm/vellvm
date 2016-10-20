define i64 @naive_mod(i64 %top, i64 %bottom) {
  %product_sum = alloca i64
  store i64 0, i64* %product_sum
  br label %start

start:
  %1 = load i64, i64* %product_sum
  %plus = add i64 %bottom, %1
  store i64 %plus, i64* %product_sum
  %exceeded = icmp sgt i64 %plus, %top
  br i1 %exceeded, label %final, label %start

final:
  %2 = load i64, i64* %product_sum
  %un_exceeded = sub i64 %2, %bottom
  %out = sub i64 %top, %un_exceeded
  ret i64 %out
}

define i64 @naive_prime(i64 %n) {
  %factor_attempt = alloca i64
  store i64 2, i64* %factor_attempt
  br label %loop

loop:
  %1 = load i64, i64* %factor_attempt
  %sqr = mul i64 %1, %1
  %exceed_cap = icmp sgt i64 %sqr, %n
  br i1 %exceed_cap, label %final_true, label %inc

inc:
  %2 = load i64, i64* %factor_attempt
  %plus = add i64 1, %1
  store i64 %plus, i64* %factor_attempt
  %mod_result = call i64 @naive_mod(i64 %n, i64 %2)
  %is_composite = icmp eq i64 0, %mod_result
  br i1 %is_composite, label %final_false, label %loop

final_false:
  ret i64 0

final_true:
  ret i64 1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %result = call i64 @naive_prime(i64 19)
  ret i64 %result
}
