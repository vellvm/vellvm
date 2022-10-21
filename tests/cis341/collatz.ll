define i64 @collatz(i64 %n) {
  %cmp = icmp sgt i64 %n, 1
  br i1 %cmp, label %then, label %ret0
then:
  %four = shl i64 %n, 63
  %five = ashr i64 %four, 63
  %six = icmp eq i64 %five, 0
  br i1 %six, label %even, label %odd
ret0:
  ret i64 0
even:
  %seven1 = ashr i64 %n, 1
  %eight1 = call i64 @collatz(i64 %seven1)
  %nine1 = add i64 %eight1, 1
  ret i64 %nine1
odd:
  %seven2 = mul i64 3, %n
  %eight2 = add i64 1, %seven2 
  %nine2 = call i64 @collatz(i64 %eight2)
  %one0 = add i64 1, %nine2
  ret i64 %one0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %one = call i64 @collatz(i64 7426)
  ret i64 %one
}

; ASSERT EQ: i64 70 = call i64 @main(i64 0, i8** null)
