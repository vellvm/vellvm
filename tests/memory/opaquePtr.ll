@a = internal global [8 x i32] zeroinitializer, align 16

define i32 @write_at(ptr noundef %0, i32 noundef %1, i32 noundef %2) #0 {
  %4 = alloca ptr, align 8
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
  store i32 %1, ptr %5, align 4
  store i32 %2, ptr %6, align 4
  %8 = load ptr, ptr %4, align 8
  %9 = load i32, ptr %5, align 4
  %10 = sext i32 %9 to i64
  %11 = getelementptr i32, ptr %8, i64 %10
  %12 = load i32, ptr %11, align 4
  store i32 %12, ptr %7, align 4
  %13 = load i32, ptr %6, align 4
  %14 = load ptr, ptr %4, align 8
  %15 = load i32, ptr %5, align 4
  %16 = sext i32 %15 to i64
  %17 = getelementptr i32, ptr %14, i64 %16
  store i32 %13, ptr %17, align 4
  %18 = load i32, ptr %7, align 4
  ret i32 %18
}

define i32 @get_a(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = sext i32 %3 to i64
  %5 = getelementptr [8 x i32], ptr @a, i64 0, i64 %4
  %6 = load i32, ptr %5, align 4
  ret i32 %6
}

define i32 @foo() #0 {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  br label %2

2:                                                ; preds = %10, %0
  %3 = load i32, ptr %1, align 4
  %4 = icmp slt i32 %3, 8
  br i1 %4, label %5, label %13

5:                                                ; preds = %2
  %6 = load i32, ptr %1, align 4
  %7 = load i32, ptr %1, align 4
  %8 = mul i32 %7, 2
  %9 = call i32 @write_at(ptr noundef @a, i32 noundef %6, i32 noundef %8)
  br label %10

10:                                               ; preds = %5
  %11 = load i32, ptr %1, align 4
  %12 = add i32 %11, 1
  store i32 %12, ptr %1, align 4
  br label %2

13:                                               ; preds = %2
  %14 = call i32 @get_a(i32 noundef 7)
  ret i32 %14
}

; ASSERT EQ: i32 14 = call i32 @foo()
