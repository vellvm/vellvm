@gbl = global [5 x i64] [ i64 2, i64 3, i64 4, i64 5, i64 6 ]

define i64 @add(i64 %x1, i64 %x2) {
    %1 = add i64 %x1, %x2
    ret i64 %1
}

define i64 @foldl(i64(i64, i64)* %f, i64 %acc, i64* %argv, i64 %argc) {
  %cmp = icmp eq i64 %argc, 0
  br i1 %cmp, label %then, label %else
then:
  ret i64 %acc
else:
  %tail = getelementptr i64, i64* %argv, i32 1
  %head = load i64, i64* %argv 
  %new_acc = call i64 %f(i64 %acc, i64 %head)
  %new_argc = sub i64 %argc, 1
  %val = call i64 @foldl(i64(i64, i64)* %f, i64 %new_acc, i64* %tail, i64 %new_argc)
  ret i64 %val
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = getelementptr [5 x i64], [5 x i64]* @gbl, i32 0, i32 0
  %2 = call i64 @foldl(i64(i64, i64)* @add, i64 0, i64* %1, i64 5)
  ret i64 %2
}
