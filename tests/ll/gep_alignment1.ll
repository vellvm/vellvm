; ASSERT EQ: i64 8 = call i64 @off_i32_ptr()
define i64 @off_i32_ptr() {
  %p = alloca {i32, ptr}
  %f = getelementptr {i32, ptr}, ptr %p, i32 0, i32 1
  %a = ptrtoint ptr %p to i64
  %b = ptrtoint ptr %f to i64
  %d = sub i64 %b, %a
  ret i64 %d
}

@fmt = private unnamed_addr constant [22 x i8] c"off_i32_ptr() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v = call i64 @off_i32_ptr()
  %ignored = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v)
  ret i32 0
}
