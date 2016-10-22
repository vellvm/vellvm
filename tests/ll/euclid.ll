define i64 @gcd_rec(i64 %a, i64 %b) {
   %1 = alloca i64
   store i64 %a, i64* %1
   %cmp = icmp ne i64 %b, 0
   br i1 %cmp, label %neq0, label %eq0

eq0:
   ret i64 %a

neq0:
    %2 = load i64, i64* %1
    %3 = sub i64 %2, %b
    store i64 %3, i64* %1
    %cmp1 = icmp sgt i64 %3, %b
    br i1 %cmp1, label %neq0, label %recurse

recurse:
    %4 = call i64 @gcd_rec(i64 %b, i64 %3)
    ret i64 %4
}


define i64 @main(i64 %argc, i8** %arcv) {
    %1 = call i64 @gcd_rec(i64 424, i64 34)
    ret i64 %1
}
