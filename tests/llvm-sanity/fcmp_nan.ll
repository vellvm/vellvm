
declare i32 @printf(i8*, ...)

@qnan = constant double 0x7FF8000000000000;
@snan = constant double 0x7FF0000000000001;
@fmt_lt = private unnamed_addr constant [23 x i8] c"fcmp olt %lf %lf = %d\0A\00", align 1
@fmt_ge = private unnamed_addr constant [23 x i8] c"fcmp oge %lf %lf = %d\0A\00", align 1

define void @test_fcmp(double %x, double %y) {
  %1 = fcmp olt double %x, %y
  %2 = fcmp oge double %x, %y
  %p1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @fmt_lt, i32 0, i32 0), double %x, double %y, i1 %1)
  %p2 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @fmt_ge, i32 0, i32 0), double %x, double %y, i1 %2)
  ret void
}

define i32 @main(i8 %argc, i8** %argv) {
  %qnan = load double, double* @qnan
  %snan = load double, double* @snan
  call void @test_fcmp(double 1.0, double 1.0)
  call void @test_fcmp(double 1.0, double 2.0)
  call void @test_fcmp(double 2.0, double 1.0)
  call void @test_fcmp(double 1.0, double %qnan)
  call void @test_fcmp(double 1.0, double %snan)
  call void @test_fcmp(double %qnan, double 1.0)
  call void @test_fcmp(double %snan, double 1.0)
  call void @test_fcmp(double %snan, double %snan)
  call void @test_fcmp(double %qnan, double %qnan)
  call void @test_fcmp(double %snan, double %qnan)
  call void @test_fcmp(double %qnan, double %snan)
  ret i32 0
}
