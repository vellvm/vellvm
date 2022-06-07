define i64 @log(i64 %num) {
   %1 = icmp eq i64 %num, 1
   br i1 %1, label %then, label %else 
then:
  ret i64 0
else:
   %2 =  lshr i64 %num, 1
   %3 = call i64 @log(i64 %2)
   %4 = add i64 %3, 1
   ret i64 %4
}

define i64 @main(i64 %argc, i8** %arcv) {
   %3 = add i64 16, 0
   %1 = call i64 @log(i64 %3)
   ret i64 %1
}