@.str = private unnamed_addr constant [4 x i8] c"%f\0A\00", align 1

declare i32 @printf(ptr noundef, ...)




define void @print_floats() {
  %1 = alloca i32, align u0x4
  %x = alloca [ u0xa5 x i32 ]
  store i32 0, ptr %1, align 4
  %2 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 0.000000e+00)
  %3 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef -1.230000e+29)
  %4 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef -0.000000e+00)
  %5 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 0.25)
  %6 = fpext float 0xC5F8D6F380000000 to double
  %7 = call i32 (ptr, ...) @printf(ptr noundef @.str, double %6)
  %8 = fpext float 0x3FF3AE1480000000 to double
  %9 = call i32 (ptr, ...) @printf(ptr noundef @.str, double %8)
  %10 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 102.000000e-1)
  %11 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 102.124e-03)
  %12 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef +0.1243)
  %13 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef +120.)
  %14 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef +120.e2)
  %15 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef +120.E2)
  %16 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 0x49)
  %17 = call i32 (ptr, ...) @printf(ptr noundef @.str, double noundef 0x42faa3d700000000)
  br label %s0xa

s0xa:
  ret void
}

define i32 @main(i32 %argc, i8** %argv) {
  call void @print_floats();
  ret i32 0
}
