; ASSERT EQ: i64 3 = call i64 @size_nested_i8()
define i64 @size_nested_i8() {
  %p = alloca {i8, {i8, i8}}
  %f = getelementptr {i8, {i8, i8}}, ptr %p, i32 1
  %a = ptrtoint ptr %p to i64
  %b = ptrtoint ptr %f to i64
  %d = sub i64 %b, %a
  ret i64 %d
}

@fmt = private unnamed_addr constant [25 x i8] c"size_nested_i8() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v = call i64 @size_nested_i8()
  %ignored = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v)
  ret i32 0
}
