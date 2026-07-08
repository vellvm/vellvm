; ASSERT EQ: i32 0 = call i32 @main()

@main.floats = internal constant [2 x float] [float 0x41C8400000000000, float 0x41E0000000000000], align 4

define dso_local i32 @main() {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = load float, ptr @main.floats, align 4
  %3 = load float, ptr getelementptr inbounds ([2 x float], ptr @main.floats, i64 0, i64 1), align 4
  %4 = fcmp oeq float %2, %3
  %5 = zext i1 %4 to i32
  ret i32 %5
}
