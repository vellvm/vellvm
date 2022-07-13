define i64 @log(i64 %num) {
   %one = icmp eq i64 %num, 1
   br i1 %one, label %then, label %else 
then:
  ret i64 0
else:
   %two =  lshr i64 %num, 1
   %three = call i64 @log(i64 %two)
   %four = add i64 %three, 1
   ret i64 %four
}

define i64 @main(i64 %argc, i8** %arcv) {
   %three = add i64 16, 0
   %one = call i64 @log(i64 %three)
   ret i64 %one
}

; ASSERT EQ: i64 4 = call i64 @main(i64 0, i8** null)