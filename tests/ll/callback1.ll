%fty = type i64 (i64, i64)

declare void @ll_puts(i8*)
declare i8* @ll_strcat(i8*, i8*)
declare i64 @ll_callback(%fty*)
declare i8* @ll_ltoa(i64)

define i64 @foo(i64 %x, i64 %y) {
  %1 = alloca i64
  %2 = add i64 %x, %y
  store i64 %2, i64* %1
  %3 = load i64, i64* %1
  ret i64 %3
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @ll_callback(%fty* @foo)
  %2 = call i8* @ll_ltoa(i64 %1)
  call void @ll_puts(i8* %2)
  ret i64 0
}

