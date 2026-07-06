declare i32 @printf(i8*, ...)

@.str = private unnamed_addr constant [7 x i8] c"Hello\0A\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 noundef %0, ptr noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca ptr, align 8
  store i32 0, ptr %3, align 4
  store i32 %0, ptr %4, align 4
  store ptr %1, ptr %5, align 8
  %6 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  ret i32 0
}

; ASSERT EQ: i32 0 = call i32 @main(i32 0, ptr null)
