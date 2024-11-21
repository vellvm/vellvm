declare void @ll_puts(ptr)

@gstr = global [14 x i8] c"hello, world!\00"

define i64 @main(i64 %argc, ptr %argv) {
  %1 = getelementptr [14 x i8], ptr @gstr, i32 0, i32 0
  call void @ll_puts (ptr %1)
  ret i64 0
}

