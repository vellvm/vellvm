declare i8* @ll_malloc(i64)
declare i64 @ll_strlen(i8*)
declare i8* @ll_strncpy(i8*, i8*, i64)
declare void @ll_puts(i8*)

define i64 @main(i64 %argc, i8** %argv) {
  %p1 = getelementptr i8*, i8** %argv, i32 1
  %a1 = load i8*, i8** %p1
  %p2 = getelementptr i8*, i8** %argv, i32 2
  %a2 = load i8*, i8** %p2
  %r = call i8* @strcat(i8* %a1, i8* %a2)
  ret i64 0
}

define i8* @strcat(i8* %s1, i8* %s2) {
  %l1 = call i64 @ll_strlen(i8* %s1)
  %l2 = call i64 @ll_strlen(i8* %s2)
  %l3 = add i64 %l1, %l2
  %p = call i8* @ll_malloc(i64 %l3)
  %r1 = call i8* @ll_strncpy(i8* %p, i8* %s1, i64 0)
  %r2 = call i8* @ll_strncpy(i8* %p, i8* %s2, i64 %l1)
  call void @ll_puts(i8* %p)
  ret i8* %r2
}
