%fty = type i64 (i64, i64)

declare void @ll_puts(ptr)
declare ptr @ll_strcat(ptr, ptr)
declare i64 @ll_callback(ptr)
declare ptr @ll_ltoa(i64)

define i64 @foo(i64 %x, i64 %y) {
  %1 = alloca i64
  %2 = add i64 %x, %y
  store i64 %2, ptr %1
  %3 = load i64, ptr %1
  ret i64 %3
}

define i64 @main(i64 %argc, ptr %argv) {
  %1 = call i64 @ll_callback(ptr @foo)
  %2 = call ptr @ll_ltoa(i64 %1)
  call void @ll_puts(ptr %2)
  ret i64 0
}

