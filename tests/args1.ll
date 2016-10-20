declare void @ll_puts(i8*)
declare i8* @ll_strcat(i8*, i8*)

@toofew = global [9 x i8] c"argc < 3\00"
@toomany = global [9 x i8] c"argc > 3\00"

define i64 @main(i64 %argc, i8** %argv) {
  %lt = icmp slt i64 %argc, 3
  br i1 %lt, label %few, label %else

few:
  %1 = getelementptr [9 x i8], [9 x i8]* @toofew, i32 0, i32 0
  call void @ll_puts(i8* %1)
  ret i64 0

else:
  %gt = icmp sgt i64 %argc, 3
  br i1 %gt, label %many, label %right

many:
  %2 = getelementptr [9 x i8], [9 x i8]* @toomany, i32 0, i32 0
  call void @ll_puts(i8* %2)
  ret i64 0

right:
  %3 = getelementptr i8*, i8** %argv, i32 1
  %4 = load i8*, i8** %3
  %5 = getelementptr i8*, i8** %argv, i32 2
  %6 = load i8*, i8** %5
  %7 = call i8* @ll_strcat(i8* %4, i8* %6)
  call void @ll_puts(i8* %7)
  ret i64 0
}

