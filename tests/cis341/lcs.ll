%arr1 = type [7 x i64]
%arr2 = type [6 x i64]

@str1 = global %arr1 [i64 1, i64 2, i64 3, i64 2, i64 4, i64 1, i64 2]
@str2 = global %arr2 [i64 2, i64 4, i64 3, i64 1, i64 2 , i64 1]

define i64 @lcs(i64 %m, i64 %n) {
  %1 = icmp eq i64 %m, 0
  %2 = icmp eq i64 %n, 0
  br i1 %1, label %ret0, label %interm

 interm:
 br i1 %2, label %ret0, label %then

 then:
 %m1 = sub i64 %m, 1
 %n1 = sub i64 %n, 1
 %3 = getelementptr %arr1, %arr1* @str1, i32 0, i32 %m1
 %4 = load i64, i64* %3
 %5 = getelementptr %arr2, %arr2* @str2, i32 0, i32 %n1
 %6 = load i64, i64* %5
 %7 = icmp eq i64 %4, %6
 br i1 %7, label %eq_recurse, label %not_eq_recurse

  eq_recurse:
  %ans = call i64 @lcs(i64 %m1, i64 %n1)
  %final = add i64 %ans, 1
  ret i64 %final

  not_eq_recurse:
  %ans1 = call i64 @lcs(i64 %m1, i64 %n)
  %ans2 = call i64 @lcs(i64 %m, i64 %n1)
  %10 = icmp sge i64 %ans1, %ans2                                                                        %10 = icmp sge i64 %ans1, %ans2
  br i1 %10, label %ret1, label %ret2

  ret1:
  ret i64 %ans1

  ret2:
  ret i64 %ans2

  ret0:
  ret i64 0

}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @lcs(i64 7, i64 6)
  ret i64 %1
}
