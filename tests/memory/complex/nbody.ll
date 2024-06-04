; ModuleID = 'nbody.c'
source_filename = "nbody.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.1.0"

%struct.quad = type { float, float, float, %struct.centroid* }
%struct.centroid = type { float, float, float }
%struct.qtree = type { %struct.quad*, %struct.qtree*, %struct.qtree*, %struct.qtree*, %struct.qtree* }
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @in_bounding_box(float %0, float %1, %struct.quad* %2) #0 {
  %4 = alloca i32, align 4
  %5 = alloca float, align 4
  %6 = alloca float, align 4
  %7 = alloca %struct.quad*, align 8
  store float %0, float* %5, align 4
  store float %1, float* %6, align 4
  store %struct.quad* %2, %struct.quad** %7, align 8
  %8 = load float, float* %5, align 4
  %9 = load %struct.quad*, %struct.quad** %7, align 8
  %10 = getelementptr inbounds %struct.quad, %struct.quad* %9, i32 0, i32 1
  %11 = load float, float* %10, align 4
  %12 = fcmp olt float %8, %11
  br i1 %12, label %39, label %13

13:                                               ; preds = %3
  %14 = load float, float* %5, align 4
  %15 = load %struct.quad*, %struct.quad** %7, align 8
  %16 = getelementptr inbounds %struct.quad, %struct.quad* %15, i32 0, i32 1
  %17 = load float, float* %16, align 4
  %18 = load %struct.quad*, %struct.quad** %7, align 8
  %19 = getelementptr inbounds %struct.quad, %struct.quad* %18, i32 0, i32 0
  %20 = load float, float* %19, align 8
  %21 = fadd float %17, %20
  %22 = fcmp ogt float %14, %21
  br i1 %22, label %39, label %23

23:                                               ; preds = %13
  %24 = load float, float* %6, align 4
  %25 = load %struct.quad*, %struct.quad** %7, align 8
  %26 = getelementptr inbounds %struct.quad, %struct.quad* %25, i32 0, i32 2
  %27 = load float, float* %26, align 8
  %28 = fcmp olt float %24, %27
  br i1 %28, label %39, label %29

29:                                               ; preds = %23
  %30 = load float, float* %6, align 4
  %31 = load %struct.quad*, %struct.quad** %7, align 8
  %32 = getelementptr inbounds %struct.quad, %struct.quad* %31, i32 0, i32 2
  %33 = load float, float* %32, align 8
  %34 = load %struct.quad*, %struct.quad** %7, align 8
  %35 = getelementptr inbounds %struct.quad, %struct.quad* %34, i32 0, i32 0
  %36 = load float, float* %35, align 8
  %37 = fadd float %33, %36
  %38 = fcmp ogt float %30, %37
  br i1 %38, label %39, label %40

39:                                               ; preds = %29, %23, %13, %3
  store i32 0, i32* %4, align 4
  br label %41

40:                                               ; preds = %29
  store i32 1, i32* %4, align 4
  br label %41

41:                                               ; preds = %40, %39
  %42 = load i32, i32* %4, align 4
  ret i32 %42
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @which_quad(float %0, float %1, %struct.quad* %2) #0 {
  %4 = alloca i32, align 4
  %5 = alloca float, align 4
  %6 = alloca float, align 4
  %7 = alloca %struct.quad*, align 8
  store float %0, float* %5, align 4
  store float %1, float* %6, align 4
  store %struct.quad* %2, %struct.quad** %7, align 8
  %8 = load float, float* %5, align 4
  %9 = fpext float %8 to double
  %10 = load %struct.quad*, %struct.quad** %7, align 8
  %11 = getelementptr inbounds %struct.quad, %struct.quad* %10, i32 0, i32 1
  %12 = load float, float* %11, align 4
  %13 = fpext float %12 to double
  %14 = load %struct.quad*, %struct.quad** %7, align 8
  %15 = getelementptr inbounds %struct.quad, %struct.quad* %14, i32 0, i32 0
  %16 = load float, float* %15, align 8
  %17 = fpext float %16 to double
  %18 = fdiv double %17, 2.000000e+00
  %19 = fadd double %13, %18
  %20 = fcmp ole double %9, %19
  br i1 %20, label %21, label %36

21:                                               ; preds = %3
  %22 = load float, float* %6, align 4
  %23 = fpext float %22 to double
  %24 = load %struct.quad*, %struct.quad** %7, align 8
  %25 = getelementptr inbounds %struct.quad, %struct.quad* %24, i32 0, i32 2
  %26 = load float, float* %25, align 8
  %27 = fpext float %26 to double
  %28 = load %struct.quad*, %struct.quad** %7, align 8
  %29 = getelementptr inbounds %struct.quad, %struct.quad* %28, i32 0, i32 0
  %30 = load float, float* %29, align 8
  %31 = fpext float %30 to double
  %32 = fdiv double %31, 2.000000e+00
  %33 = fadd double %27, %32
  %34 = fcmp olt double %23, %33
  br i1 %34, label %35, label %36

35:                                               ; preds = %21
  store i32 1, i32* %4, align 4
  br label %95

36:                                               ; preds = %21, %3
  %37 = load float, float* %5, align 4
  %38 = fpext float %37 to double
  %39 = load %struct.quad*, %struct.quad** %7, align 8
  %40 = getelementptr inbounds %struct.quad, %struct.quad* %39, i32 0, i32 1
  %41 = load float, float* %40, align 4
  %42 = fpext float %41 to double
  %43 = load %struct.quad*, %struct.quad** %7, align 8
  %44 = getelementptr inbounds %struct.quad, %struct.quad* %43, i32 0, i32 0
  %45 = load float, float* %44, align 8
  %46 = fpext float %45 to double
  %47 = fdiv double %46, 2.000000e+00
  %48 = fadd double %42, %47
  %49 = fcmp ogt double %38, %48
  br i1 %49, label %50, label %65

50:                                               ; preds = %36
  %51 = load float, float* %6, align 4
  %52 = fpext float %51 to double
  %53 = load %struct.quad*, %struct.quad** %7, align 8
  %54 = getelementptr inbounds %struct.quad, %struct.quad* %53, i32 0, i32 2
  %55 = load float, float* %54, align 8
  %56 = fpext float %55 to double
  %57 = load %struct.quad*, %struct.quad** %7, align 8
  %58 = getelementptr inbounds %struct.quad, %struct.quad* %57, i32 0, i32 0
  %59 = load float, float* %58, align 8
  %60 = fpext float %59 to double
  %61 = fdiv double %60, 2.000000e+00
  %62 = fadd double %56, %61
  %63 = fcmp olt double %52, %62
  br i1 %63, label %64, label %65

64:                                               ; preds = %50
  store i32 2, i32* %4, align 4
  br label %95

65:                                               ; preds = %50, %36
  %66 = load float, float* %5, align 4
  %67 = fpext float %66 to double
  %68 = load %struct.quad*, %struct.quad** %7, align 8
  %69 = getelementptr inbounds %struct.quad, %struct.quad* %68, i32 0, i32 1
  %70 = load float, float* %69, align 4
  %71 = fpext float %70 to double
  %72 = load %struct.quad*, %struct.quad** %7, align 8
  %73 = getelementptr inbounds %struct.quad, %struct.quad* %72, i32 0, i32 0
  %74 = load float, float* %73, align 8
  %75 = fpext float %74 to double
  %76 = fdiv double %75, 2.000000e+00
  %77 = fadd double %71, %76
  %78 = fcmp ole double %67, %77
  br i1 %78, label %79, label %94

79:                                               ; preds = %65
  %80 = load float, float* %6, align 4
  %81 = fpext float %80 to double
  %82 = load %struct.quad*, %struct.quad** %7, align 8
  %83 = getelementptr inbounds %struct.quad, %struct.quad* %82, i32 0, i32 2
  %84 = load float, float* %83, align 8
  %85 = fpext float %84 to double
  %86 = load %struct.quad*, %struct.quad** %7, align 8
  %87 = getelementptr inbounds %struct.quad, %struct.quad* %86, i32 0, i32 0
  %88 = load float, float* %87, align 8
  %89 = fpext float %88 to double
  %90 = fdiv double %89, 2.000000e+00
  %91 = fadd double %85, %90
  %92 = fcmp oge double %81, %91
  br i1 %92, label %93, label %94

93:                                               ; preds = %79
  store i32 3, i32* %4, align 4
  br label %95

94:                                               ; preds = %79, %65
  store i32 4, i32* %4, align 4
  br label %95

95:                                               ; preds = %94, %93, %64, %35
  %96 = load i32, i32* %4, align 4
  ret i32 %96
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define %struct.centroid* @centroid_sum(%struct.centroid* %0, %struct.centroid* %1) #0 {
  %3 = alloca %struct.centroid*, align 8
  %4 = alloca %struct.centroid*, align 8
  %5 = alloca %struct.centroid*, align 8
  %6 = alloca %struct.centroid*, align 8
  %7 = alloca float, align 4
  %8 = alloca float, align 4
  %9 = alloca float, align 4
  store %struct.centroid* %0, %struct.centroid** %4, align 8
  store %struct.centroid* %1, %struct.centroid** %5, align 8
  %10 = load %struct.centroid*, %struct.centroid** %4, align 8
  %11 = icmp eq %struct.centroid* %10, null
  br i1 %11, label %12, label %14

12:                                               ; preds = %2
  %13 = load %struct.centroid*, %struct.centroid** %5, align 8
  store %struct.centroid* %13, %struct.centroid** %3, align 8
  br label %82

14:                                               ; preds = %2
  %15 = load %struct.centroid*, %struct.centroid** %5, align 8
  %16 = icmp eq %struct.centroid* %15, null
  br i1 %16, label %17, label %19

17:                                               ; preds = %14
  %18 = load %struct.centroid*, %struct.centroid** %4, align 8
  store %struct.centroid* %18, %struct.centroid** %3, align 8
  br label %82

19:                                               ; preds = %14
  br label %20

20:                                               ; preds = %19
  %21 = call i8* @malloc(i64 12) #2
  %22 = bitcast i8* %21 to %struct.centroid*
  store %struct.centroid* %22, %struct.centroid** %6, align 8
  %23 = load %struct.centroid*, %struct.centroid** %4, align 8
  %24 = getelementptr inbounds %struct.centroid, %struct.centroid* %23, i32 0, i32 2
  %25 = load float, float* %24, align 4
  %26 = load %struct.centroid*, %struct.centroid** %5, align 8
  %27 = getelementptr inbounds %struct.centroid, %struct.centroid* %26, i32 0, i32 2
  %28 = load float, float* %27, align 4
  %29 = fadd float %25, %28
  store float %29, float* %7, align 4
  %30 = load float, float* %7, align 4
  %31 = load %struct.centroid*, %struct.centroid** %6, align 8
  %32 = getelementptr inbounds %struct.centroid, %struct.centroid* %31, i32 0, i32 2
  store float %30, float* %32, align 4
  %33 = load float, float* %7, align 4
  %34 = fpext float %33 to double
  %35 = fdiv double 1.000000e+00, %34
  %36 = load %struct.centroid*, %struct.centroid** %4, align 8
  %37 = getelementptr inbounds %struct.centroid, %struct.centroid* %36, i32 0, i32 2
  %38 = load float, float* %37, align 4
  %39 = load %struct.centroid*, %struct.centroid** %4, align 8
  %40 = getelementptr inbounds %struct.centroid, %struct.centroid* %39, i32 0, i32 0
  %41 = load float, float* %40, align 4
  %42 = fmul float %38, %41
  %43 = load %struct.centroid*, %struct.centroid** %5, align 8
  %44 = getelementptr inbounds %struct.centroid, %struct.centroid* %43, i32 0, i32 2
  %45 = load float, float* %44, align 4
  %46 = load %struct.centroid*, %struct.centroid** %5, align 8
  %47 = getelementptr inbounds %struct.centroid, %struct.centroid* %46, i32 0, i32 0
  %48 = load float, float* %47, align 4
  %49 = fmul float %45, %48
  %50 = fadd float %42, %49
  %51 = fpext float %50 to double
  %52 = fmul double %35, %51
  %53 = fptrunc double %52 to float
  store float %53, float* %8, align 4
  %54 = load float, float* %8, align 4
  %55 = load %struct.centroid*, %struct.centroid** %6, align 8
  %56 = getelementptr inbounds %struct.centroid, %struct.centroid* %55, i32 0, i32 0
  store float %54, float* %56, align 4
  %57 = load float, float* %7, align 4
  %58 = fpext float %57 to double
  %59 = fdiv double 1.000000e+00, %58
  %60 = load %struct.centroid*, %struct.centroid** %4, align 8
  %61 = getelementptr inbounds %struct.centroid, %struct.centroid* %60, i32 0, i32 2
  %62 = load float, float* %61, align 4
  %63 = load %struct.centroid*, %struct.centroid** %4, align 8
  %64 = getelementptr inbounds %struct.centroid, %struct.centroid* %63, i32 0, i32 1
  %65 = load float, float* %64, align 4
  %66 = fmul float %62, %65
  %67 = load %struct.centroid*, %struct.centroid** %5, align 8
  %68 = getelementptr inbounds %struct.centroid, %struct.centroid* %67, i32 0, i32 2
  %69 = load float, float* %68, align 4
  %70 = load %struct.centroid*, %struct.centroid** %5, align 8
  %71 = getelementptr inbounds %struct.centroid, %struct.centroid* %70, i32 0, i32 1
  %72 = load float, float* %71, align 4
  %73 = fmul float %69, %72
  %74 = fadd float %66, %73
  %75 = fpext float %74 to double
  %76 = fmul double %59, %75
  %77 = fptrunc double %76 to float
  store float %77, float* %9, align 4
  %78 = load float, float* %9, align 4
  %79 = load %struct.centroid*, %struct.centroid** %6, align 8
  %80 = getelementptr inbounds %struct.centroid, %struct.centroid* %79, i32 0, i32 1
  store float %78, float* %80, align 4
  %81 = load %struct.centroid*, %struct.centroid** %6, align 8
  store %struct.centroid* %81, %struct.centroid** %3, align 8
  br label %82

82:                                               ; preds = %20, %17, %12
  %83 = load %struct.centroid*, %struct.centroid** %3, align 8
  ret %struct.centroid* %83
}
; Function Attrs: allocsize(0)
declare i8* @malloc(i64) #1
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @compare_float(float %0, float %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca float, align 4
  %5 = alloca float, align 4
  %6 = alloca float, align 4
  store float %0, float* %4, align 4
  store float %1, float* %5, align 4
  store float 0x3EE4F8B580000000, float* %6, align 4
  %7 = load float, float* %4, align 4
  %8 = load float, float* %6, align 4
  %9 = fsub float %7, %8
  %10 = load float, float* %5, align 4
  %11 = fcmp olt float %9, %10
  br i1 %11, label %12, label %19

12:                                               ; preds = %2
  %13 = load float, float* %4, align 4
  %14 = load float, float* %6, align 4
  %15 = fadd float %13, %14
  %16 = load float, float* %5, align 4
  %17 = fcmp ogt float %15, %16
  br i1 %17, label %18, label %19

18:                                               ; preds = %12
  store i32 1, i32* %3, align 4
  br label %20

19:                                               ; preds = %12, %2
  store i32 0, i32* %3, align 4
  br label %20

20:                                               ; preds = %19, %18
  %21 = load i32, i32* %3, align 4
  ret i32 %21
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @is_in_box(%struct.qtree* %0, float %1, float %2) #0 {
  %4 = alloca i32, align 4
  %5 = alloca %struct.qtree*, align 8
  %6 = alloca float, align 4
  %7 = alloca float, align 4
  %8 = alloca i32, align 4
  store %struct.qtree* %0, %struct.qtree** %5, align 8
  store float %1, float* %6, align 4
  store float %2, float* %7, align 4
  %9 = load %struct.qtree*, %struct.qtree** %5, align 8
  %10 = getelementptr inbounds %struct.qtree, %struct.qtree* %9, i32 0, i32 0
  %11 = load %struct.quad*, %struct.quad** %10, align 8
  %12 = icmp eq %struct.quad* %11, null
  br i1 %12, label %13, label %14

13:                                               ; preds = %3
  store i32 0, i32* %4, align 4
  br label %131

14:                                               ; preds = %3
  %15 = load %struct.qtree*, %struct.qtree** %5, align 8
  %16 = getelementptr inbounds %struct.qtree, %struct.qtree* %15, i32 0, i32 1
  %17 = load %struct.qtree*, %struct.qtree** %16, align 8
  %18 = icmp eq %struct.qtree* %17, null
  br i1 %18, label %19, label %58

19:                                               ; preds = %14
  %20 = load %struct.qtree*, %struct.qtree** %5, align 8
  %21 = getelementptr inbounds %struct.qtree, %struct.qtree* %20, i32 0, i32 2
  %22 = load %struct.qtree*, %struct.qtree** %21, align 8
  %23 = icmp eq %struct.qtree* %22, null
  br i1 %23, label %24, label %58

24:                                               ; preds = %19
  %25 = load %struct.qtree*, %struct.qtree** %5, align 8
  %26 = getelementptr inbounds %struct.qtree, %struct.qtree* %25, i32 0, i32 3
  %27 = load %struct.qtree*, %struct.qtree** %26, align 8
  %28 = icmp eq %struct.qtree* %27, null
  br i1 %28, label %29, label %58

29:                                               ; preds = %24
  %30 = load %struct.qtree*, %struct.qtree** %5, align 8
  %31 = getelementptr inbounds %struct.qtree, %struct.qtree* %30, i32 0, i32 4
  %32 = load %struct.qtree*, %struct.qtree** %31, align 8
  %33 = icmp eq %struct.qtree* %32, null
  br i1 %33, label %34, label %58

34:                                               ; preds = %29
  %35 = load %struct.qtree*, %struct.qtree** %5, align 8
  %36 = getelementptr inbounds %struct.qtree, %struct.qtree* %35, i32 0, i32 0
  %37 = load %struct.quad*, %struct.quad** %36, align 8
  %38 = getelementptr inbounds %struct.quad, %struct.quad* %37, i32 0, i32 3
  %39 = load %struct.centroid*, %struct.centroid** %38, align 8
  %40 = getelementptr inbounds %struct.centroid, %struct.centroid* %39, i32 0, i32 0
  %41 = load float, float* %40, align 4
  %42 = load float, float* %6, align 4
  %43 = call i32 @compare_float(float %41, float %42)
  %44 = icmp ne i32 %43, 0
  br i1 %44, label %45, label %57

45:                                               ; preds = %34
  %46 = load %struct.qtree*, %struct.qtree** %5, align 8
  %47 = getelementptr inbounds %struct.qtree, %struct.qtree* %46, i32 0, i32 0
  %48 = load %struct.quad*, %struct.quad** %47, align 8
  %49 = getelementptr inbounds %struct.quad, %struct.quad* %48, i32 0, i32 3
  %50 = load %struct.centroid*, %struct.centroid** %49, align 8
  %51 = getelementptr inbounds %struct.centroid, %struct.centroid* %50, i32 0, i32 1
  %52 = load float, float* %51, align 4
  %53 = load float, float* %7, align 4
  %54 = call i32 @compare_float(float %52, float %53)
  %55 = icmp ne i32 %54, 0
  br i1 %55, label %56, label %57

56:                                               ; preds = %45
  store i32 1, i32* %4, align 4
  br label %131

57:                                               ; preds = %45, %34
  store i32 0, i32* %4, align 4
  br label %131

58:                                               ; preds = %29, %24, %19, %14
  %59 = load %struct.qtree*, %struct.qtree** %5, align 8
  %60 = getelementptr inbounds %struct.qtree, %struct.qtree* %59, i32 0, i32 0
  %61 = load %struct.quad*, %struct.quad** %60, align 8
  %62 = getelementptr inbounds %struct.quad, %struct.quad* %61, i32 0, i32 3
  %63 = load %struct.centroid*, %struct.centroid** %62, align 8
  %64 = getelementptr inbounds %struct.centroid, %struct.centroid* %63, i32 0, i32 0
  %65 = load float, float* %64, align 4
  %66 = load float, float* %6, align 4
  %67 = call i32 @compare_float(float %65, float %66)
  %68 = icmp ne i32 %67, 0
  br i1 %68, label %69, label %81

69:                                               ; preds = %58
  %70 = load %struct.qtree*, %struct.qtree** %5, align 8
  %71 = getelementptr inbounds %struct.qtree, %struct.qtree* %70, i32 0, i32 0
  %72 = load %struct.quad*, %struct.quad** %71, align 8
  %73 = getelementptr inbounds %struct.quad, %struct.quad* %72, i32 0, i32 3
  %74 = load %struct.centroid*, %struct.centroid** %73, align 8
  %75 = getelementptr inbounds %struct.centroid, %struct.centroid* %74, i32 0, i32 1
  %76 = load float, float* %75, align 4
  %77 = load float, float* %7, align 4
  %78 = call i32 @compare_float(float %76, float %77)
  %79 = icmp ne i32 %78, 0
  br i1 %79, label %80, label %81

80:                                               ; preds = %69
  store i32 1, i32* %4, align 4
  br label %131

81:                                               ; preds = %69, %58
  %82 = load float, float* %6, align 4
  %83 = load float, float* %7, align 4
  %84 = load %struct.qtree*, %struct.qtree** %5, align 8
  %85 = getelementptr inbounds %struct.qtree, %struct.qtree* %84, i32 0, i32 0
  %86 = load %struct.quad*, %struct.quad** %85, align 8
  %87 = call i32 @which_quad(float %82, float %83, %struct.quad* %86)
  store i32 %87, i32* %8, align 4
  %88 = load i32, i32* %8, align 4
  %89 = icmp eq i32 %88, 1
  br i1 %89, label %90, label %97

90:                                               ; preds = %81
  %91 = load %struct.qtree*, %struct.qtree** %5, align 8
  %92 = getelementptr inbounds %struct.qtree, %struct.qtree* %91, i32 0, i32 1
  %93 = load %struct.qtree*, %struct.qtree** %92, align 8
  %94 = load float, float* %6, align 4
  %95 = load float, float* %7, align 4
  %96 = call i32 @is_in_box(%struct.qtree* %93, float %94, float %95)
  store i32 %96, i32* %4, align 4
  br label %131

97:                                               ; preds = %81
  %98 = load i32, i32* %8, align 4
  %99 = icmp eq i32 %98, 2
  br i1 %99, label %100, label %107

100:                                              ; preds = %97
  %101 = load %struct.qtree*, %struct.qtree** %5, align 8
  %102 = getelementptr inbounds %struct.qtree, %struct.qtree* %101, i32 0, i32 2
  %103 = load %struct.qtree*, %struct.qtree** %102, align 8
  %104 = load float, float* %6, align 4
  %105 = load float, float* %7, align 4
  %106 = call i32 @is_in_box(%struct.qtree* %103, float %104, float %105)
  store i32 %106, i32* %4, align 4
  br label %131

107:                                              ; preds = %97
  %108 = load i32, i32* %8, align 4
  %109 = icmp eq i32 %108, 3
  br i1 %109, label %110, label %117

110:                                              ; preds = %107
  %111 = load %struct.qtree*, %struct.qtree** %5, align 8
  %112 = getelementptr inbounds %struct.qtree, %struct.qtree* %111, i32 0, i32 3
  %113 = load %struct.qtree*, %struct.qtree** %112, align 8
  %114 = load float, float* %6, align 4
  %115 = load float, float* %7, align 4
  %116 = call i32 @is_in_box(%struct.qtree* %113, float %114, float %115)
  store i32 %116, i32* %4, align 4
  br label %131

117:                                              ; preds = %107
  %118 = load i32, i32* %8, align 4
  %119 = icmp eq i32 %118, 4
  br i1 %119, label %120, label %127

120:                                              ; preds = %117
  %121 = load %struct.qtree*, %struct.qtree** %5, align 8
  %122 = getelementptr inbounds %struct.qtree, %struct.qtree* %121, i32 0, i32 4
  %123 = load %struct.qtree*, %struct.qtree** %122, align 8
  %124 = load float, float* %6, align 4
  %125 = load float, float* %7, align 4
  %126 = call i32 @is_in_box(%struct.qtree* %123, float %124, float %125)
  store i32 %126, i32* %4, align 4
  br label %131

127:                                              ; preds = %117
  br label %128

128:                                              ; preds = %127
  br label %129

129:                                              ; preds = %128
  br label %130

130:                                              ; preds = %129
  store i32 0, i32* %4, align 4
  br label %131

131:                                              ; preds = %130, %120, %110, %100, %90, %80, %57, %56, %13
  %132 = load i32, i32* %4, align 4
  ret i32 %132
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define %struct.qtree* @empty_qtree(float %0, float %1, float %2, float %3, float %4, float %5) #0 {
  %7 = alloca float, align 4
  %8 = alloca float, align 4
  %9 = alloca float, align 4
  %10 = alloca float, align 4
  %11 = alloca float, align 4
  %12 = alloca float, align 4
  %13 = alloca %struct.qtree*, align 8
  %14 = alloca %struct.quad*, align 8
  %15 = alloca %struct.centroid*, align 8
  store float %0, float* %7, align 4
  store float %1, float* %8, align 4
  store float %2, float* %9, align 4
  store float %3, float* %10, align 4
  store float %4, float* %11, align 4
  store float %5, float* %12, align 4
  %16 = call i8* @malloc(i64 40) #2
  %17 = bitcast i8* %16 to %struct.qtree*
  store %struct.qtree* %17, %struct.qtree** %13, align 8
  %18 = load %struct.qtree*, %struct.qtree** %13, align 8
  %19 = getelementptr inbounds %struct.qtree, %struct.qtree* %18, i32 0, i32 1
  store %struct.qtree* null, %struct.qtree** %19, align 8
  %20 = load %struct.qtree*, %struct.qtree** %13, align 8
  %21 = getelementptr inbounds %struct.qtree, %struct.qtree* %20, i32 0, i32 2
  store %struct.qtree* null, %struct.qtree** %21, align 8
  %22 = load %struct.qtree*, %struct.qtree** %13, align 8
  %23 = getelementptr inbounds %struct.qtree, %struct.qtree* %22, i32 0, i32 3
  store %struct.qtree* null, %struct.qtree** %23, align 8
  %24 = load %struct.qtree*, %struct.qtree** %13, align 8
  %25 = getelementptr inbounds %struct.qtree, %struct.qtree* %24, i32 0, i32 4
  store %struct.qtree* null, %struct.qtree** %25, align 8
  %26 = call i8* @malloc(i64 24) #2
  %27 = bitcast i8* %26 to %struct.quad*
  store %struct.quad* %27, %struct.quad** %14, align 8
  %28 = call i8* @malloc(i64 12) #2
  %29 = bitcast i8* %28 to %struct.centroid*
  store %struct.centroid* %29, %struct.centroid** %15, align 8
  %30 = load %struct.quad*, %struct.quad** %14, align 8
  %31 = load %struct.qtree*, %struct.qtree** %13, align 8
  %32 = getelementptr inbounds %struct.qtree, %struct.qtree* %31, i32 0, i32 0
  store %struct.quad* %30, %struct.quad** %32, align 8
  %33 = load %struct.centroid*, %struct.centroid** %15, align 8
  %34 = load %struct.qtree*, %struct.qtree** %13, align 8
  %35 = getelementptr inbounds %struct.qtree, %struct.qtree* %34, i32 0, i32 0
  %36 = load %struct.quad*, %struct.quad** %35, align 8
  %37 = getelementptr inbounds %struct.quad, %struct.quad* %36, i32 0, i32 3
  store %struct.centroid* %33, %struct.centroid** %37, align 8
  %38 = load float, float* %10, align 4
  %39 = load %struct.qtree*, %struct.qtree** %13, align 8
  %40 = getelementptr inbounds %struct.qtree, %struct.qtree* %39, i32 0, i32 0
  %41 = load %struct.quad*, %struct.quad** %40, align 8
  %42 = getelementptr inbounds %struct.quad, %struct.quad* %41, i32 0, i32 0
  store float %38, float* %42, align 8
  %43 = load float, float* %12, align 4
  %44 = load %struct.qtree*, %struct.qtree** %13, align 8
  %45 = getelementptr inbounds %struct.qtree, %struct.qtree* %44, i32 0, i32 0
  %46 = load %struct.quad*, %struct.quad** %45, align 8
  %47 = getelementptr inbounds %struct.quad, %struct.quad* %46, i32 0, i32 1
  store float %43, float* %47, align 4
  %48 = load float, float* %11, align 4
  %49 = load %struct.qtree*, %struct.qtree** %13, align 8
  %50 = getelementptr inbounds %struct.qtree, %struct.qtree* %49, i32 0, i32 0
  %51 = load %struct.quad*, %struct.quad** %50, align 8
  %52 = getelementptr inbounds %struct.quad, %struct.quad* %51, i32 0, i32 2
  store float %48, float* %52, align 8
  %53 = load float, float* %7, align 4
  %54 = load %struct.qtree*, %struct.qtree** %13, align 8
  %55 = getelementptr inbounds %struct.qtree, %struct.qtree* %54, i32 0, i32 0
  %56 = load %struct.quad*, %struct.quad** %55, align 8
  %57 = getelementptr inbounds %struct.quad, %struct.quad* %56, i32 0, i32 3
  %58 = load %struct.centroid*, %struct.centroid** %57, align 8
  %59 = getelementptr inbounds %struct.centroid, %struct.centroid* %58, i32 0, i32 0
  store float %53, float* %59, align 4
  %60 = load float, float* %8, align 4
  %61 = load %struct.qtree*, %struct.qtree** %13, align 8
  %62 = getelementptr inbounds %struct.qtree, %struct.qtree* %61, i32 0, i32 0
  %63 = load %struct.quad*, %struct.quad** %62, align 8
  %64 = getelementptr inbounds %struct.quad, %struct.quad* %63, i32 0, i32 3
  %65 = load %struct.centroid*, %struct.centroid** %64, align 8
  %66 = getelementptr inbounds %struct.centroid, %struct.centroid* %65, i32 0, i32 1
  store float %60, float* %66, align 4
  %67 = load float, float* %9, align 4
  %68 = load %struct.qtree*, %struct.qtree** %13, align 8
  %69 = getelementptr inbounds %struct.qtree, %struct.qtree* %68, i32 0, i32 0
  %70 = load %struct.quad*, %struct.quad** %69, align 8
  %71 = getelementptr inbounds %struct.quad, %struct.quad* %70, i32 0, i32 3
  %72 = load %struct.centroid*, %struct.centroid** %71, align 8
  %73 = getelementptr inbounds %struct.centroid, %struct.centroid* %72, i32 0, i32 2
  store float %67, float* %73, align 4
  %74 = load %struct.qtree*, %struct.qtree** %13, align 8
  ret %struct.qtree* %74
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define %struct.qtree* @insertPoint(float %0, float %1, %struct.qtree* %2, float %3) #0 {
  %5 = alloca float, align 4
  %6 = alloca float, align 4
  %7 = alloca %struct.qtree*, align 8
  %8 = alloca float, align 4
  %9 = alloca i32, align 4
  %10 = alloca %struct.qtree*, align 8
  %11 = alloca float, align 4
  %12 = alloca float, align 4
  %13 = alloca float, align 4
  %14 = alloca float, align 4
  %15 = alloca %struct.qtree*, align 8
  %16 = alloca float, align 4
  %17 = alloca %struct.centroid*, align 8
  %18 = alloca float, align 4
  %19 = alloca float, align 4
  %20 = alloca float, align 4
  %21 = alloca float, align 4
  %22 = alloca %struct.qtree*, align 8
  %23 = alloca float, align 4
  %24 = alloca %struct.centroid*, align 8
  %25 = alloca float, align 4
  %26 = alloca float, align 4
  %27 = alloca float, align 4
  %28 = alloca float, align 4
  %29 = alloca %struct.qtree*, align 8
  %30 = alloca float, align 4
  %31 = alloca %struct.centroid*, align 8
  %32 = alloca float, align 4
  %33 = alloca float, align 4
  %34 = alloca float, align 4
  %35 = alloca float, align 4
  %36 = alloca %struct.qtree*, align 8
  %37 = alloca float, align 4
  %38 = alloca %struct.centroid*, align 8
  %39 = alloca %struct.centroid*, align 8
  %40 = alloca %struct.centroid*, align 8
  %41 = alloca %struct.centroid*, align 8
  %42 = alloca %struct.centroid*, align 8
  store float %0, float* %5, align 4
  store float %1, float* %6, align 4
  store %struct.qtree* %2, %struct.qtree** %7, align 8
  store float %3, float* %8, align 4
  %43 = load %struct.qtree*, %struct.qtree** %7, align 8
  %44 = icmp eq %struct.qtree* %43, null
  br i1 %44, label %45, label %56

45:                                               ; preds = %4
  %46 = load float, float* %5, align 4
  %47 = load float, float* %6, align 4
  %48 = load float, float* %8, align 4
  %49 = call %struct.qtree* @empty_qtree(float %46, float %47, float %48, float 4.000000e+00, float 0.000000e+00, float 0.000000e+00)
  store %struct.qtree* %49, %struct.qtree** %7, align 8
  %50 = load float, float* %5, align 4
  %51 = load float, float* %6, align 4
  %52 = load %struct.qtree*, %struct.qtree** %7, align 8
  %53 = getelementptr inbounds %struct.qtree, %struct.qtree* %52, i32 0, i32 0
  %54 = load %struct.quad*, %struct.quad** %53, align 8
  %55 = call i32 @which_quad(float %50, float %51, %struct.quad* %54)
  store i32 %55, i32* %9, align 4
  br label %2129

56:                                               ; preds = %4
  %57 = load %struct.qtree*, %struct.qtree** %7, align 8
  %58 = getelementptr inbounds %struct.qtree, %struct.qtree* %57, i32 0, i32 0
  %59 = load %struct.quad*, %struct.quad** %58, align 8
  %60 = getelementptr inbounds %struct.quad, %struct.quad* %59, i32 0, i32 3
  %61 = load %struct.centroid*, %struct.centroid** %60, align 8
  %62 = getelementptr inbounds %struct.centroid, %struct.centroid* %61, i32 0, i32 0
  %63 = load float, float* %62, align 4
  %64 = load float, float* %5, align 4
  %65 = fcmp oeq float %63, %64
  br i1 %65, label %66, label %92

66:                                               ; preds = %56
  %67 = load %struct.qtree*, %struct.qtree** %7, align 8
  %68 = getelementptr inbounds %struct.qtree, %struct.qtree* %67, i32 0, i32 0
  %69 = load %struct.quad*, %struct.quad** %68, align 8
  %70 = getelementptr inbounds %struct.quad, %struct.quad* %69, i32 0, i32 3
  %71 = load %struct.centroid*, %struct.centroid** %70, align 8
  %72 = getelementptr inbounds %struct.centroid, %struct.centroid* %71, i32 0, i32 1
  %73 = load float, float* %72, align 4
  %74 = load float, float* %6, align 4
  %75 = fcmp oeq float %73, %74
  br i1 %75, label %76, label %92

76:                                               ; preds = %66
  %77 = load %struct.qtree*, %struct.qtree** %7, align 8
  %78 = getelementptr inbounds %struct.qtree, %struct.qtree* %77, i32 0, i32 0
  %79 = load %struct.quad*, %struct.quad** %78, align 8
  %80 = getelementptr inbounds %struct.quad, %struct.quad* %79, i32 0, i32 3
  %81 = load %struct.centroid*, %struct.centroid** %80, align 8
  %82 = getelementptr inbounds %struct.centroid, %struct.centroid* %81, i32 0, i32 2
  %83 = load float, float* %82, align 4
  %84 = load float, float* %8, align 4
  %85 = fadd float %83, %84
  %86 = load %struct.qtree*, %struct.qtree** %7, align 8
  %87 = getelementptr inbounds %struct.qtree, %struct.qtree* %86, i32 0, i32 0
  %88 = load %struct.quad*, %struct.quad** %87, align 8
  %89 = getelementptr inbounds %struct.quad, %struct.quad* %88, i32 0, i32 3
  %90 = load %struct.centroid*, %struct.centroid** %89, align 8
  %91 = getelementptr inbounds %struct.centroid, %struct.centroid* %90, i32 0, i32 2
  store float %85, float* %91, align 4
  br label %2128

92:                                               ; preds = %66, %56
  %93 = load float, float* %5, align 4
  %94 = load float, float* %6, align 4
  %95 = load %struct.qtree*, %struct.qtree** %7, align 8
  %96 = getelementptr inbounds %struct.qtree, %struct.qtree* %95, i32 0, i32 0
  %97 = load %struct.quad*, %struct.quad** %96, align 8
  %98 = call i32 @which_quad(float %93, float %94, %struct.quad* %97)
  %99 = icmp eq i32 %98, 1
  br i1 %99, label %100, label %452

100:                                              ; preds = %92
  %101 = load %struct.qtree*, %struct.qtree** %7, align 8
  %102 = getelementptr inbounds %struct.qtree, %struct.qtree* %101, i32 0, i32 1
  %103 = load %struct.qtree*, %struct.qtree** %102, align 8
  %104 = icmp eq %struct.qtree* %103, null
  br i1 %104, label %105, label %452

105:                                              ; preds = %100
  %106 = load %struct.qtree*, %struct.qtree** %7, align 8
  %107 = getelementptr inbounds %struct.qtree, %struct.qtree* %106, i32 0, i32 1
  %108 = load %struct.qtree*, %struct.qtree** %107, align 8
  %109 = icmp eq %struct.qtree* %108, null
  br i1 %109, label %110, label %289

110:                                              ; preds = %105
  %111 = load %struct.qtree*, %struct.qtree** %7, align 8
  %112 = getelementptr inbounds %struct.qtree, %struct.qtree* %111, i32 0, i32 2
  %113 = load %struct.qtree*, %struct.qtree** %112, align 8
  %114 = icmp eq %struct.qtree* %113, null
  br i1 %114, label %115, label %289

115:                                              ; preds = %110
  %116 = load %struct.qtree*, %struct.qtree** %7, align 8
  %117 = getelementptr inbounds %struct.qtree, %struct.qtree* %116, i32 0, i32 3
  %118 = load %struct.qtree*, %struct.qtree** %117, align 8
  %119 = icmp eq %struct.qtree* %118, null
  br i1 %119, label %120, label %289

120:                                              ; preds = %115
  %121 = load %struct.qtree*, %struct.qtree** %7, align 8
  %122 = getelementptr inbounds %struct.qtree, %struct.qtree* %121, i32 0, i32 4
  %123 = load %struct.qtree*, %struct.qtree** %122, align 8
  %124 = icmp eq %struct.qtree* %123, null
  br i1 %124, label %125, label %289

125:                                              ; preds = %120
  %126 = load %struct.qtree*, %struct.qtree** %7, align 8
  %127 = getelementptr inbounds %struct.qtree, %struct.qtree* %126, i32 0, i32 0
  %128 = load %struct.quad*, %struct.quad** %127, align 8
  %129 = getelementptr inbounds %struct.quad, %struct.quad* %128, i32 0, i32 3
  %130 = load %struct.centroid*, %struct.centroid** %129, align 8
  %131 = getelementptr inbounds %struct.centroid, %struct.centroid* %130, i32 0, i32 0
  %132 = load float, float* %131, align 4
  store float %132, float* %11, align 4
  %133 = load %struct.qtree*, %struct.qtree** %7, align 8
  %134 = getelementptr inbounds %struct.qtree, %struct.qtree* %133, i32 0, i32 0
  %135 = load %struct.quad*, %struct.quad** %134, align 8
  %136 = getelementptr inbounds %struct.quad, %struct.quad* %135, i32 0, i32 3
  %137 = load %struct.centroid*, %struct.centroid** %136, align 8
  %138 = getelementptr inbounds %struct.centroid, %struct.centroid* %137, i32 0, i32 1
  %139 = load float, float* %138, align 4
  store float %139, float* %12, align 4
  %140 = load %struct.qtree*, %struct.qtree** %7, align 8
  %141 = getelementptr inbounds %struct.qtree, %struct.qtree* %140, i32 0, i32 0
  %142 = load %struct.quad*, %struct.quad** %141, align 8
  %143 = getelementptr inbounds %struct.quad, %struct.quad* %142, i32 0, i32 3
  %144 = load %struct.centroid*, %struct.centroid** %143, align 8
  %145 = getelementptr inbounds %struct.centroid, %struct.centroid* %144, i32 0, i32 2
  %146 = load float, float* %145, align 4
  store float %146, float* %13, align 4
  %147 = load float, float* %11, align 4
  %148 = load float, float* %12, align 4
  %149 = load %struct.qtree*, %struct.qtree** %7, align 8
  %150 = getelementptr inbounds %struct.qtree, %struct.qtree* %149, i32 0, i32 0
  %151 = load %struct.quad*, %struct.quad** %150, align 8
  %152 = call i32 @which_quad(float %147, float %148, %struct.quad* %151)
  %153 = sitofp i32 %152 to float
  store float %153, float* %14, align 4
  %154 = load float, float* %14, align 4
  %155 = fcmp oeq float %154, 1.000000e+00
  br i1 %155, label %156, label %180

156:                                              ; preds = %125
  %157 = load float, float* %11, align 4
  %158 = load float, float* %12, align 4
  %159 = load float, float* %13, align 4
  %160 = load %struct.qtree*, %struct.qtree** %7, align 8
  %161 = getelementptr inbounds %struct.qtree, %struct.qtree* %160, i32 0, i32 0
  %162 = load %struct.quad*, %struct.quad** %161, align 8
  %163 = getelementptr inbounds %struct.quad, %struct.quad* %162, i32 0, i32 0
  %164 = load float, float* %163, align 8
  %165 = fdiv float %164, 2.000000e+00
  %166 = load %struct.qtree*, %struct.qtree** %7, align 8
  %167 = getelementptr inbounds %struct.qtree, %struct.qtree* %166, i32 0, i32 0
  %168 = load %struct.quad*, %struct.quad** %167, align 8
  %169 = getelementptr inbounds %struct.quad, %struct.quad* %168, i32 0, i32 2
  %170 = load float, float* %169, align 8
  %171 = load %struct.qtree*, %struct.qtree** %7, align 8
  %172 = getelementptr inbounds %struct.qtree, %struct.qtree* %171, i32 0, i32 0
  %173 = load %struct.quad*, %struct.quad** %172, align 8
  %174 = getelementptr inbounds %struct.quad, %struct.quad* %173, i32 0, i32 1
  %175 = load float, float* %174, align 4
  %176 = call %struct.qtree* @empty_qtree(float %157, float %158, float %159, float %165, float %170, float %175)
  store %struct.qtree* %176, %struct.qtree** %15, align 8
  %177 = load %struct.qtree*, %struct.qtree** %15, align 8
  %178 = load %struct.qtree*, %struct.qtree** %7, align 8
  %179 = getelementptr inbounds %struct.qtree, %struct.qtree* %178, i32 0, i32 1
  store %struct.qtree* %177, %struct.qtree** %179, align 8
  br label %288

180:                                              ; preds = %125
  %181 = load float, float* %14, align 4
  %182 = fcmp oeq float %181, 3.000000e+00
  br i1 %182, label %183, label %214

183:                                              ; preds = %180
  %184 = load float, float* %11, align 4
  %185 = load float, float* %12, align 4
  %186 = load float, float* %13, align 4
  %187 = load %struct.qtree*, %struct.qtree** %7, align 8
  %188 = getelementptr inbounds %struct.qtree, %struct.qtree* %187, i32 0, i32 0
  %189 = load %struct.quad*, %struct.quad** %188, align 8
  %190 = getelementptr inbounds %struct.quad, %struct.quad* %189, i32 0, i32 0
  %191 = load float, float* %190, align 8
  %192 = fdiv float %191, 2.000000e+00
  %193 = load %struct.qtree*, %struct.qtree** %7, align 8
  %194 = getelementptr inbounds %struct.qtree, %struct.qtree* %193, i32 0, i32 0
  %195 = load %struct.quad*, %struct.quad** %194, align 8
  %196 = getelementptr inbounds %struct.quad, %struct.quad* %195, i32 0, i32 2
  %197 = load float, float* %196, align 8
  %198 = load %struct.qtree*, %struct.qtree** %7, align 8
  %199 = getelementptr inbounds %struct.qtree, %struct.qtree* %198, i32 0, i32 0
  %200 = load %struct.quad*, %struct.quad** %199, align 8
  %201 = getelementptr inbounds %struct.quad, %struct.quad* %200, i32 0, i32 0
  %202 = load float, float* %201, align 8
  %203 = fdiv float %202, 2.000000e+00
  %204 = fadd float %197, %203
  %205 = load %struct.qtree*, %struct.qtree** %7, align 8
  %206 = getelementptr inbounds %struct.qtree, %struct.qtree* %205, i32 0, i32 0
  %207 = load %struct.quad*, %struct.quad** %206, align 8
  %208 = getelementptr inbounds %struct.quad, %struct.quad* %207, i32 0, i32 1
  %209 = load float, float* %208, align 4
  %210 = call %struct.qtree* @empty_qtree(float %184, float %185, float %186, float %192, float %204, float %209)
  store %struct.qtree* %210, %struct.qtree** %15, align 8
  %211 = load %struct.qtree*, %struct.qtree** %15, align 8
  %212 = load %struct.qtree*, %struct.qtree** %7, align 8
  %213 = getelementptr inbounds %struct.qtree, %struct.qtree* %212, i32 0, i32 3
  store %struct.qtree* %211, %struct.qtree** %213, align 8
  br label %287

214:                                              ; preds = %180
  %215 = load float, float* %14, align 4
  %216 = fcmp oeq float %215, 2.000000e+00
  br i1 %216, label %217, label %248

217:                                              ; preds = %214
  %218 = load float, float* %11, align 4
  %219 = load float, float* %12, align 4
  %220 = load float, float* %13, align 4
  %221 = load %struct.qtree*, %struct.qtree** %7, align 8
  %222 = getelementptr inbounds %struct.qtree, %struct.qtree* %221, i32 0, i32 0
  %223 = load %struct.quad*, %struct.quad** %222, align 8
  %224 = getelementptr inbounds %struct.quad, %struct.quad* %223, i32 0, i32 0
  %225 = load float, float* %224, align 8
  %226 = fdiv float %225, 2.000000e+00
  %227 = load %struct.qtree*, %struct.qtree** %7, align 8
  %228 = getelementptr inbounds %struct.qtree, %struct.qtree* %227, i32 0, i32 0
  %229 = load %struct.quad*, %struct.quad** %228, align 8
  %230 = getelementptr inbounds %struct.quad, %struct.quad* %229, i32 0, i32 2
  %231 = load float, float* %230, align 8
  %232 = load %struct.qtree*, %struct.qtree** %7, align 8
  %233 = getelementptr inbounds %struct.qtree, %struct.qtree* %232, i32 0, i32 0
  %234 = load %struct.quad*, %struct.quad** %233, align 8
  %235 = getelementptr inbounds %struct.quad, %struct.quad* %234, i32 0, i32 1
  %236 = load float, float* %235, align 4
  %237 = load %struct.qtree*, %struct.qtree** %7, align 8
  %238 = getelementptr inbounds %struct.qtree, %struct.qtree* %237, i32 0, i32 0
  %239 = load %struct.quad*, %struct.quad** %238, align 8
  %240 = getelementptr inbounds %struct.quad, %struct.quad* %239, i32 0, i32 0
  %241 = load float, float* %240, align 8
  %242 = fdiv float %241, 2.000000e+00
  %243 = fadd float %236, %242
  %244 = call %struct.qtree* @empty_qtree(float %218, float %219, float %220, float %226, float %231, float %243)
  store %struct.qtree* %244, %struct.qtree** %15, align 8
  %245 = load %struct.qtree*, %struct.qtree** %15, align 8
  %246 = load %struct.qtree*, %struct.qtree** %7, align 8
  %247 = getelementptr inbounds %struct.qtree, %struct.qtree* %246, i32 0, i32 2
  store %struct.qtree* %245, %struct.qtree** %247, align 8
  br label %286

248:                                              ; preds = %214
  %249 = load float, float* %11, align 4
  %250 = load float, float* %12, align 4
  %251 = load float, float* %13, align 4
  %252 = load %struct.qtree*, %struct.qtree** %7, align 8
  %253 = getelementptr inbounds %struct.qtree, %struct.qtree* %252, i32 0, i32 0
  %254 = load %struct.quad*, %struct.quad** %253, align 8
  %255 = getelementptr inbounds %struct.quad, %struct.quad* %254, i32 0, i32 0
  %256 = load float, float* %255, align 8
  %257 = fdiv float %256, 2.000000e+00
  %258 = load %struct.qtree*, %struct.qtree** %7, align 8
  %259 = getelementptr inbounds %struct.qtree, %struct.qtree* %258, i32 0, i32 0
  %260 = load %struct.quad*, %struct.quad** %259, align 8
  %261 = getelementptr inbounds %struct.quad, %struct.quad* %260, i32 0, i32 2
  %262 = load float, float* %261, align 8
  %263 = load %struct.qtree*, %struct.qtree** %7, align 8
  %264 = getelementptr inbounds %struct.qtree, %struct.qtree* %263, i32 0, i32 0
  %265 = load %struct.quad*, %struct.quad** %264, align 8
  %266 = getelementptr inbounds %struct.quad, %struct.quad* %265, i32 0, i32 0
  %267 = load float, float* %266, align 8
  %268 = fdiv float %267, 2.000000e+00
  %269 = fadd float %262, %268
  %270 = load %struct.qtree*, %struct.qtree** %7, align 8
  %271 = getelementptr inbounds %struct.qtree, %struct.qtree* %270, i32 0, i32 0
  %272 = load %struct.quad*, %struct.quad** %271, align 8
  %273 = getelementptr inbounds %struct.quad, %struct.quad* %272, i32 0, i32 1
  %274 = load float, float* %273, align 4
  %275 = load %struct.qtree*, %struct.qtree** %7, align 8
  %276 = getelementptr inbounds %struct.qtree, %struct.qtree* %275, i32 0, i32 0
  %277 = load %struct.quad*, %struct.quad** %276, align 8
  %278 = getelementptr inbounds %struct.quad, %struct.quad* %277, i32 0, i32 0
  %279 = load float, float* %278, align 8
  %280 = fdiv float %279, 2.000000e+00
  %281 = fadd float %274, %280
  %282 = call %struct.qtree* @empty_qtree(float %249, float %250, float %251, float %257, float %269, float %281)
  store %struct.qtree* %282, %struct.qtree** %15, align 8
  %283 = load %struct.qtree*, %struct.qtree** %15, align 8
  %284 = load %struct.qtree*, %struct.qtree** %7, align 8
  %285 = getelementptr inbounds %struct.qtree, %struct.qtree* %284, i32 0, i32 4
  store %struct.qtree* %283, %struct.qtree** %285, align 8
  br label %286

286:                                              ; preds = %248, %217
  br label %287

287:                                              ; preds = %286, %183
  br label %288

288:                                              ; preds = %287, %156
  br label %289

289:                                              ; preds = %288, %120, %115, %110, %105
  %290 = load %struct.qtree*, %struct.qtree** %7, align 8
  %291 = getelementptr inbounds %struct.qtree, %struct.qtree* %290, i32 0, i32 0
  %292 = load %struct.quad*, %struct.quad** %291, align 8
  %293 = getelementptr inbounds %struct.quad, %struct.quad* %292, i32 0, i32 0
  %294 = load float, float* %293, align 8
  store float %294, float* %16, align 4
  %295 = load %struct.qtree*, %struct.qtree** %7, align 8
  %296 = getelementptr inbounds %struct.qtree, %struct.qtree* %295, i32 0, i32 1
  %297 = load %struct.qtree*, %struct.qtree** %296, align 8
  %298 = icmp eq %struct.qtree* %297, null
  br i1 %298, label %299, label %320

299:                                              ; preds = %289
  %300 = load float, float* %5, align 4
  %301 = load float, float* %6, align 4
  %302 = load float, float* %8, align 4
  %303 = load float, float* %16, align 4
  %304 = fpext float %303 to double
  %305 = fdiv double %304, 2.000000e+00
  %306 = fptrunc double %305 to float
  %307 = load %struct.qtree*, %struct.qtree** %7, align 8
  %308 = getelementptr inbounds %struct.qtree, %struct.qtree* %307, i32 0, i32 0
  %309 = load %struct.quad*, %struct.quad** %308, align 8
  %310 = getelementptr inbounds %struct.quad, %struct.quad* %309, i32 0, i32 2
  %311 = load float, float* %310, align 8
  %312 = load %struct.qtree*, %struct.qtree** %7, align 8
  %313 = getelementptr inbounds %struct.qtree, %struct.qtree* %312, i32 0, i32 0
  %314 = load %struct.quad*, %struct.quad** %313, align 8
  %315 = getelementptr inbounds %struct.quad, %struct.quad* %314, i32 0, i32 1
  %316 = load float, float* %315, align 4
  %317 = call %struct.qtree* @empty_qtree(float %300, float %301, float %302, float %306, float %311, float %316)
  %318 = load %struct.qtree*, %struct.qtree** %7, align 8
  %319 = getelementptr inbounds %struct.qtree, %struct.qtree* %318, i32 0, i32 1
  store %struct.qtree* %317, %struct.qtree** %319, align 8
  br label %328

320:                                              ; preds = %289
  %321 = load float, float* %5, align 4
  %322 = load float, float* %6, align 4
  %323 = load %struct.qtree*, %struct.qtree** %7, align 8
  %324 = getelementptr inbounds %struct.qtree, %struct.qtree* %323, i32 0, i32 1
  %325 = load %struct.qtree*, %struct.qtree** %324, align 8
  %326 = load float, float* %8, align 4
  %327 = call %struct.qtree* @insertPoint(float %321, float %322, %struct.qtree* %325, float %326)
  br label %328

328:                                              ; preds = %320, %299
  %329 = load %struct.qtree*, %struct.qtree** %7, align 8
  %330 = getelementptr inbounds %struct.qtree, %struct.qtree* %329, i32 0, i32 2
  %331 = load %struct.qtree*, %struct.qtree** %330, align 8
  %332 = icmp ne %struct.qtree* %331, null
  br i1 %332, label %333, label %379

333:                                              ; preds = %328
  %334 = load %struct.qtree*, %struct.qtree** %7, align 8
  %335 = getelementptr inbounds %struct.qtree, %struct.qtree* %334, i32 0, i32 1
  %336 = load %struct.qtree*, %struct.qtree** %335, align 8
  %337 = getelementptr inbounds %struct.qtree, %struct.qtree* %336, i32 0, i32 0
  %338 = load %struct.quad*, %struct.quad** %337, align 8
  %339 = getelementptr inbounds %struct.quad, %struct.quad* %338, i32 0, i32 3
  %340 = load %struct.centroid*, %struct.centroid** %339, align 8
  %341 = load %struct.qtree*, %struct.qtree** %7, align 8
  %342 = getelementptr inbounds %struct.qtree, %struct.qtree* %341, i32 0, i32 2
  %343 = load %struct.qtree*, %struct.qtree** %342, align 8
  %344 = getelementptr inbounds %struct.qtree, %struct.qtree* %343, i32 0, i32 0
  %345 = load %struct.quad*, %struct.quad** %344, align 8
  %346 = getelementptr inbounds %struct.quad, %struct.quad* %345, i32 0, i32 3
  %347 = load %struct.centroid*, %struct.centroid** %346, align 8
  %348 = call %struct.centroid* @centroid_sum(%struct.centroid* %340, %struct.centroid* %347)
  store %struct.centroid* %348, %struct.centroid** %17, align 8
  %349 = load %struct.qtree*, %struct.qtree** %7, align 8
  %350 = getelementptr inbounds %struct.qtree, %struct.qtree* %349, i32 0, i32 4
  %351 = load %struct.qtree*, %struct.qtree** %350, align 8
  %352 = icmp ne %struct.qtree* %351, null
  br i1 %352, label %353, label %363

353:                                              ; preds = %333
  %354 = load %struct.centroid*, %struct.centroid** %17, align 8
  %355 = load %struct.qtree*, %struct.qtree** %7, align 8
  %356 = getelementptr inbounds %struct.qtree, %struct.qtree* %355, i32 0, i32 4
  %357 = load %struct.qtree*, %struct.qtree** %356, align 8
  %358 = getelementptr inbounds %struct.qtree, %struct.qtree* %357, i32 0, i32 0
  %359 = load %struct.quad*, %struct.quad** %358, align 8
  %360 = getelementptr inbounds %struct.quad, %struct.quad* %359, i32 0, i32 3
  %361 = load %struct.centroid*, %struct.centroid** %360, align 8
  %362 = call %struct.centroid* @centroid_sum(%struct.centroid* %354, %struct.centroid* %361)
  store %struct.centroid* %362, %struct.centroid** %17, align 8
  br label %363

363:                                              ; preds = %353, %333
  %364 = load %struct.qtree*, %struct.qtree** %7, align 8
  %365 = getelementptr inbounds %struct.qtree, %struct.qtree* %364, i32 0, i32 3
  %366 = load %struct.qtree*, %struct.qtree** %365, align 8
  %367 = icmp ne %struct.qtree* %366, null
  br i1 %367, label %368, label %378

368:                                              ; preds = %363
  %369 = load %struct.centroid*, %struct.centroid** %17, align 8
  %370 = load %struct.qtree*, %struct.qtree** %7, align 8
  %371 = getelementptr inbounds %struct.qtree, %struct.qtree* %370, i32 0, i32 3
  %372 = load %struct.qtree*, %struct.qtree** %371, align 8
  %373 = getelementptr inbounds %struct.qtree, %struct.qtree* %372, i32 0, i32 0
  %374 = load %struct.quad*, %struct.quad** %373, align 8
  %375 = getelementptr inbounds %struct.quad, %struct.quad* %374, i32 0, i32 3
  %376 = load %struct.centroid*, %struct.centroid** %375, align 8
  %377 = call %struct.centroid* @centroid_sum(%struct.centroid* %369, %struct.centroid* %376)
  store %struct.centroid* %377, %struct.centroid** %17, align 8
  br label %378

378:                                              ; preds = %368, %363
  br label %446

379:                                              ; preds = %328
  %380 = load %struct.qtree*, %struct.qtree** %7, align 8
  %381 = getelementptr inbounds %struct.qtree, %struct.qtree* %380, i32 0, i32 3
  %382 = load %struct.qtree*, %struct.qtree** %381, align 8
  %383 = icmp ne %struct.qtree* %382, null
  br i1 %383, label %384, label %415

384:                                              ; preds = %379
  %385 = load %struct.qtree*, %struct.qtree** %7, align 8
  %386 = getelementptr inbounds %struct.qtree, %struct.qtree* %385, i32 0, i32 1
  %387 = load %struct.qtree*, %struct.qtree** %386, align 8
  %388 = getelementptr inbounds %struct.qtree, %struct.qtree* %387, i32 0, i32 0
  %389 = load %struct.quad*, %struct.quad** %388, align 8
  %390 = getelementptr inbounds %struct.quad, %struct.quad* %389, i32 0, i32 3
  %391 = load %struct.centroid*, %struct.centroid** %390, align 8
  %392 = load %struct.qtree*, %struct.qtree** %7, align 8
  %393 = getelementptr inbounds %struct.qtree, %struct.qtree* %392, i32 0, i32 3
  %394 = load %struct.qtree*, %struct.qtree** %393, align 8
  %395 = getelementptr inbounds %struct.qtree, %struct.qtree* %394, i32 0, i32 0
  %396 = load %struct.quad*, %struct.quad** %395, align 8
  %397 = getelementptr inbounds %struct.quad, %struct.quad* %396, i32 0, i32 3
  %398 = load %struct.centroid*, %struct.centroid** %397, align 8
  %399 = call %struct.centroid* @centroid_sum(%struct.centroid* %391, %struct.centroid* %398)
  store %struct.centroid* %399, %struct.centroid** %17, align 8
  %400 = load %struct.qtree*, %struct.qtree** %7, align 8
  %401 = getelementptr inbounds %struct.qtree, %struct.qtree* %400, i32 0, i32 4
  %402 = load %struct.qtree*, %struct.qtree** %401, align 8
  %403 = icmp ne %struct.qtree* %402, null
  br i1 %403, label %404, label %414

404:                                              ; preds = %384
  %405 = load %struct.centroid*, %struct.centroid** %17, align 8
  %406 = load %struct.qtree*, %struct.qtree** %7, align 8
  %407 = getelementptr inbounds %struct.qtree, %struct.qtree* %406, i32 0, i32 4
  %408 = load %struct.qtree*, %struct.qtree** %407, align 8
  %409 = getelementptr inbounds %struct.qtree, %struct.qtree* %408, i32 0, i32 0
  %410 = load %struct.quad*, %struct.quad** %409, align 8
  %411 = getelementptr inbounds %struct.quad, %struct.quad* %410, i32 0, i32 3
  %412 = load %struct.centroid*, %struct.centroid** %411, align 8
  %413 = call %struct.centroid* @centroid_sum(%struct.centroid* %405, %struct.centroid* %412)
  store %struct.centroid* %413, %struct.centroid** %17, align 8
  br label %414

414:                                              ; preds = %404, %384
  br label %445

415:                                              ; preds = %379
  %416 = load %struct.qtree*, %struct.qtree** %7, align 8
  %417 = getelementptr inbounds %struct.qtree, %struct.qtree* %416, i32 0, i32 4
  %418 = load %struct.qtree*, %struct.qtree** %417, align 8
  %419 = icmp ne %struct.qtree* %418, null
  br i1 %419, label %420, label %436

420:                                              ; preds = %415
  %421 = load %struct.qtree*, %struct.qtree** %7, align 8
  %422 = getelementptr inbounds %struct.qtree, %struct.qtree* %421, i32 0, i32 1
  %423 = load %struct.qtree*, %struct.qtree** %422, align 8
  %424 = getelementptr inbounds %struct.qtree, %struct.qtree* %423, i32 0, i32 0
  %425 = load %struct.quad*, %struct.quad** %424, align 8
  %426 = getelementptr inbounds %struct.quad, %struct.quad* %425, i32 0, i32 3
  %427 = load %struct.centroid*, %struct.centroid** %426, align 8
  %428 = load %struct.qtree*, %struct.qtree** %7, align 8
  %429 = getelementptr inbounds %struct.qtree, %struct.qtree* %428, i32 0, i32 4
  %430 = load %struct.qtree*, %struct.qtree** %429, align 8
  %431 = getelementptr inbounds %struct.qtree, %struct.qtree* %430, i32 0, i32 0
  %432 = load %struct.quad*, %struct.quad** %431, align 8
  %433 = getelementptr inbounds %struct.quad, %struct.quad* %432, i32 0, i32 3
  %434 = load %struct.centroid*, %struct.centroid** %433, align 8
  %435 = call %struct.centroid* @centroid_sum(%struct.centroid* %427, %struct.centroid* %434)
  store %struct.centroid* %435, %struct.centroid** %17, align 8
  br label %444

436:                                              ; preds = %415
  %437 = load %struct.qtree*, %struct.qtree** %7, align 8
  %438 = getelementptr inbounds %struct.qtree, %struct.qtree* %437, i32 0, i32 1
  %439 = load %struct.qtree*, %struct.qtree** %438, align 8
  %440 = getelementptr inbounds %struct.qtree, %struct.qtree* %439, i32 0, i32 0
  %441 = load %struct.quad*, %struct.quad** %440, align 8
  %442 = getelementptr inbounds %struct.quad, %struct.quad* %441, i32 0, i32 3
  %443 = load %struct.centroid*, %struct.centroid** %442, align 8
  store %struct.centroid* %443, %struct.centroid** %17, align 8
  br label %444

444:                                              ; preds = %436, %420
  br label %445

445:                                              ; preds = %444, %414
  br label %446

446:                                              ; preds = %445, %378
  %447 = load %struct.centroid*, %struct.centroid** %17, align 8
  %448 = load %struct.qtree*, %struct.qtree** %7, align 8
  %449 = getelementptr inbounds %struct.qtree, %struct.qtree* %448, i32 0, i32 0
  %450 = load %struct.quad*, %struct.quad** %449, align 8
  %451 = getelementptr inbounds %struct.quad, %struct.quad* %450, i32 0, i32 3
  store %struct.centroid* %447, %struct.centroid** %451, align 8
  br label %2127

452:                                              ; preds = %100, %92
  %453 = load float, float* %5, align 4
  %454 = load float, float* %6, align 4
  %455 = load %struct.qtree*, %struct.qtree** %7, align 8
  %456 = getelementptr inbounds %struct.qtree, %struct.qtree* %455, i32 0, i32 0
  %457 = load %struct.quad*, %struct.quad** %456, align 8
  %458 = call i32 @which_quad(float %453, float %454, %struct.quad* %457)
  %459 = icmp eq i32 %458, 2
  br i1 %459, label %460, label %818

460:                                              ; preds = %452
  %461 = load %struct.qtree*, %struct.qtree** %7, align 8
  %462 = getelementptr inbounds %struct.qtree, %struct.qtree* %461, i32 0, i32 2
  %463 = load %struct.qtree*, %struct.qtree** %462, align 8
  %464 = icmp eq %struct.qtree* %463, null
  br i1 %464, label %465, label %818

465:                                              ; preds = %460
  %466 = load %struct.qtree*, %struct.qtree** %7, align 8
  %467 = getelementptr inbounds %struct.qtree, %struct.qtree* %466, i32 0, i32 1
  %468 = load %struct.qtree*, %struct.qtree** %467, align 8
  %469 = icmp eq %struct.qtree* %468, null
  br i1 %469, label %470, label %649

470:                                              ; preds = %465
  %471 = load %struct.qtree*, %struct.qtree** %7, align 8
  %472 = getelementptr inbounds %struct.qtree, %struct.qtree* %471, i32 0, i32 2
  %473 = load %struct.qtree*, %struct.qtree** %472, align 8
  %474 = icmp eq %struct.qtree* %473, null
  br i1 %474, label %475, label %649

475:                                              ; preds = %470
  %476 = load %struct.qtree*, %struct.qtree** %7, align 8
  %477 = getelementptr inbounds %struct.qtree, %struct.qtree* %476, i32 0, i32 3
  %478 = load %struct.qtree*, %struct.qtree** %477, align 8
  %479 = icmp eq %struct.qtree* %478, null
  br i1 %479, label %480, label %649

480:                                              ; preds = %475
  %481 = load %struct.qtree*, %struct.qtree** %7, align 8
  %482 = getelementptr inbounds %struct.qtree, %struct.qtree* %481, i32 0, i32 4
  %483 = load %struct.qtree*, %struct.qtree** %482, align 8
  %484 = icmp eq %struct.qtree* %483, null
  br i1 %484, label %485, label %649

485:                                              ; preds = %480
  %486 = load %struct.qtree*, %struct.qtree** %7, align 8
  %487 = getelementptr inbounds %struct.qtree, %struct.qtree* %486, i32 0, i32 0
  %488 = load %struct.quad*, %struct.quad** %487, align 8
  %489 = getelementptr inbounds %struct.quad, %struct.quad* %488, i32 0, i32 3
  %490 = load %struct.centroid*, %struct.centroid** %489, align 8
  %491 = getelementptr inbounds %struct.centroid, %struct.centroid* %490, i32 0, i32 0
  %492 = load float, float* %491, align 4
  store float %492, float* %18, align 4
  %493 = load %struct.qtree*, %struct.qtree** %7, align 8
  %494 = getelementptr inbounds %struct.qtree, %struct.qtree* %493, i32 0, i32 0
  %495 = load %struct.quad*, %struct.quad** %494, align 8
  %496 = getelementptr inbounds %struct.quad, %struct.quad* %495, i32 0, i32 3
  %497 = load %struct.centroid*, %struct.centroid** %496, align 8
  %498 = getelementptr inbounds %struct.centroid, %struct.centroid* %497, i32 0, i32 1
  %499 = load float, float* %498, align 4
  store float %499, float* %19, align 4
  %500 = load %struct.qtree*, %struct.qtree** %7, align 8
  %501 = getelementptr inbounds %struct.qtree, %struct.qtree* %500, i32 0, i32 0
  %502 = load %struct.quad*, %struct.quad** %501, align 8
  %503 = getelementptr inbounds %struct.quad, %struct.quad* %502, i32 0, i32 3
  %504 = load %struct.centroid*, %struct.centroid** %503, align 8
  %505 = getelementptr inbounds %struct.centroid, %struct.centroid* %504, i32 0, i32 2
  %506 = load float, float* %505, align 4
  store float %506, float* %20, align 4
  %507 = load float, float* %18, align 4
  %508 = load float, float* %19, align 4
  %509 = load %struct.qtree*, %struct.qtree** %7, align 8
  %510 = getelementptr inbounds %struct.qtree, %struct.qtree* %509, i32 0, i32 0
  %511 = load %struct.quad*, %struct.quad** %510, align 8
  %512 = call i32 @which_quad(float %507, float %508, %struct.quad* %511)
  %513 = sitofp i32 %512 to float
  store float %513, float* %21, align 4
  %514 = load float, float* %21, align 4
  %515 = fcmp oeq float %514, 1.000000e+00
  br i1 %515, label %516, label %540

516:                                              ; preds = %485
  %517 = load float, float* %18, align 4
  %518 = load float, float* %19, align 4
  %519 = load float, float* %20, align 4
  %520 = load %struct.qtree*, %struct.qtree** %7, align 8
  %521 = getelementptr inbounds %struct.qtree, %struct.qtree* %520, i32 0, i32 0
  %522 = load %struct.quad*, %struct.quad** %521, align 8
  %523 = getelementptr inbounds %struct.quad, %struct.quad* %522, i32 0, i32 0
  %524 = load float, float* %523, align 8
  %525 = fdiv float %524, 2.000000e+00
  %526 = load %struct.qtree*, %struct.qtree** %7, align 8
  %527 = getelementptr inbounds %struct.qtree, %struct.qtree* %526, i32 0, i32 0
  %528 = load %struct.quad*, %struct.quad** %527, align 8
  %529 = getelementptr inbounds %struct.quad, %struct.quad* %528, i32 0, i32 2
  %530 = load float, float* %529, align 8
  %531 = load %struct.qtree*, %struct.qtree** %7, align 8
  %532 = getelementptr inbounds %struct.qtree, %struct.qtree* %531, i32 0, i32 0
  %533 = load %struct.quad*, %struct.quad** %532, align 8
  %534 = getelementptr inbounds %struct.quad, %struct.quad* %533, i32 0, i32 1
  %535 = load float, float* %534, align 4
  %536 = call %struct.qtree* @empty_qtree(float %517, float %518, float %519, float %525, float %530, float %535)
  store %struct.qtree* %536, %struct.qtree** %22, align 8
  %537 = load %struct.qtree*, %struct.qtree** %22, align 8
  %538 = load %struct.qtree*, %struct.qtree** %7, align 8
  %539 = getelementptr inbounds %struct.qtree, %struct.qtree* %538, i32 0, i32 1
  store %struct.qtree* %537, %struct.qtree** %539, align 8
  br label %648

540:                                              ; preds = %485
  %541 = load float, float* %21, align 4
  %542 = fcmp oeq float %541, 3.000000e+00
  br i1 %542, label %543, label %574

543:                                              ; preds = %540
  %544 = load float, float* %18, align 4
  %545 = load float, float* %19, align 4
  %546 = load float, float* %20, align 4
  %547 = load %struct.qtree*, %struct.qtree** %7, align 8
  %548 = getelementptr inbounds %struct.qtree, %struct.qtree* %547, i32 0, i32 0
  %549 = load %struct.quad*, %struct.quad** %548, align 8
  %550 = getelementptr inbounds %struct.quad, %struct.quad* %549, i32 0, i32 0
  %551 = load float, float* %550, align 8
  %552 = fdiv float %551, 2.000000e+00
  %553 = load %struct.qtree*, %struct.qtree** %7, align 8
  %554 = getelementptr inbounds %struct.qtree, %struct.qtree* %553, i32 0, i32 0
  %555 = load %struct.quad*, %struct.quad** %554, align 8
  %556 = getelementptr inbounds %struct.quad, %struct.quad* %555, i32 0, i32 2
  %557 = load float, float* %556, align 8
  %558 = load %struct.qtree*, %struct.qtree** %7, align 8
  %559 = getelementptr inbounds %struct.qtree, %struct.qtree* %558, i32 0, i32 0
  %560 = load %struct.quad*, %struct.quad** %559, align 8
  %561 = getelementptr inbounds %struct.quad, %struct.quad* %560, i32 0, i32 0
  %562 = load float, float* %561, align 8
  %563 = fdiv float %562, 2.000000e+00
  %564 = fadd float %557, %563
  %565 = load %struct.qtree*, %struct.qtree** %7, align 8
  %566 = getelementptr inbounds %struct.qtree, %struct.qtree* %565, i32 0, i32 0
  %567 = load %struct.quad*, %struct.quad** %566, align 8
  %568 = getelementptr inbounds %struct.quad, %struct.quad* %567, i32 0, i32 1
  %569 = load float, float* %568, align 4
  %570 = call %struct.qtree* @empty_qtree(float %544, float %545, float %546, float %552, float %564, float %569)
  store %struct.qtree* %570, %struct.qtree** %22, align 8
  %571 = load %struct.qtree*, %struct.qtree** %22, align 8
  %572 = load %struct.qtree*, %struct.qtree** %7, align 8
  %573 = getelementptr inbounds %struct.qtree, %struct.qtree* %572, i32 0, i32 3
  store %struct.qtree* %571, %struct.qtree** %573, align 8
  br label %647

574:                                              ; preds = %540
  %575 = load float, float* %21, align 4
  %576 = fcmp oeq float %575, 2.000000e+00
  br i1 %576, label %577, label %608

577:                                              ; preds = %574
  %578 = load float, float* %18, align 4
  %579 = load float, float* %19, align 4
  %580 = load float, float* %20, align 4
  %581 = load %struct.qtree*, %struct.qtree** %7, align 8
  %582 = getelementptr inbounds %struct.qtree, %struct.qtree* %581, i32 0, i32 0
  %583 = load %struct.quad*, %struct.quad** %582, align 8
  %584 = getelementptr inbounds %struct.quad, %struct.quad* %583, i32 0, i32 0
  %585 = load float, float* %584, align 8
  %586 = fdiv float %585, 2.000000e+00
  %587 = load %struct.qtree*, %struct.qtree** %7, align 8
  %588 = getelementptr inbounds %struct.qtree, %struct.qtree* %587, i32 0, i32 0
  %589 = load %struct.quad*, %struct.quad** %588, align 8
  %590 = getelementptr inbounds %struct.quad, %struct.quad* %589, i32 0, i32 2
  %591 = load float, float* %590, align 8
  %592 = load %struct.qtree*, %struct.qtree** %7, align 8
  %593 = getelementptr inbounds %struct.qtree, %struct.qtree* %592, i32 0, i32 0
  %594 = load %struct.quad*, %struct.quad** %593, align 8
  %595 = getelementptr inbounds %struct.quad, %struct.quad* %594, i32 0, i32 1
  %596 = load float, float* %595, align 4
  %597 = load %struct.qtree*, %struct.qtree** %7, align 8
  %598 = getelementptr inbounds %struct.qtree, %struct.qtree* %597, i32 0, i32 0
  %599 = load %struct.quad*, %struct.quad** %598, align 8
  %600 = getelementptr inbounds %struct.quad, %struct.quad* %599, i32 0, i32 0
  %601 = load float, float* %600, align 8
  %602 = fdiv float %601, 2.000000e+00
  %603 = fadd float %596, %602
  %604 = call %struct.qtree* @empty_qtree(float %578, float %579, float %580, float %586, float %591, float %603)
  store %struct.qtree* %604, %struct.qtree** %22, align 8
  %605 = load %struct.qtree*, %struct.qtree** %22, align 8
  %606 = load %struct.qtree*, %struct.qtree** %7, align 8
  %607 = getelementptr inbounds %struct.qtree, %struct.qtree* %606, i32 0, i32 2
  store %struct.qtree* %605, %struct.qtree** %607, align 8
  br label %646

608:                                              ; preds = %574
  %609 = load float, float* %18, align 4
  %610 = load float, float* %19, align 4
  %611 = load float, float* %20, align 4
  %612 = load %struct.qtree*, %struct.qtree** %7, align 8
  %613 = getelementptr inbounds %struct.qtree, %struct.qtree* %612, i32 0, i32 0
  %614 = load %struct.quad*, %struct.quad** %613, align 8
  %615 = getelementptr inbounds %struct.quad, %struct.quad* %614, i32 0, i32 0
  %616 = load float, float* %615, align 8
  %617 = fdiv float %616, 2.000000e+00
  %618 = load %struct.qtree*, %struct.qtree** %7, align 8
  %619 = getelementptr inbounds %struct.qtree, %struct.qtree* %618, i32 0, i32 0
  %620 = load %struct.quad*, %struct.quad** %619, align 8
  %621 = getelementptr inbounds %struct.quad, %struct.quad* %620, i32 0, i32 2
  %622 = load float, float* %621, align 8
  %623 = load %struct.qtree*, %struct.qtree** %7, align 8
  %624 = getelementptr inbounds %struct.qtree, %struct.qtree* %623, i32 0, i32 0
  %625 = load %struct.quad*, %struct.quad** %624, align 8
  %626 = getelementptr inbounds %struct.quad, %struct.quad* %625, i32 0, i32 0
  %627 = load float, float* %626, align 8
  %628 = fdiv float %627, 2.000000e+00
  %629 = fadd float %622, %628
  %630 = load %struct.qtree*, %struct.qtree** %7, align 8
  %631 = getelementptr inbounds %struct.qtree, %struct.qtree* %630, i32 0, i32 0
  %632 = load %struct.quad*, %struct.quad** %631, align 8
  %633 = getelementptr inbounds %struct.quad, %struct.quad* %632, i32 0, i32 1
  %634 = load float, float* %633, align 4
  %635 = load %struct.qtree*, %struct.qtree** %7, align 8
  %636 = getelementptr inbounds %struct.qtree, %struct.qtree* %635, i32 0, i32 0
  %637 = load %struct.quad*, %struct.quad** %636, align 8
  %638 = getelementptr inbounds %struct.quad, %struct.quad* %637, i32 0, i32 0
  %639 = load float, float* %638, align 8
  %640 = fdiv float %639, 2.000000e+00
  %641 = fadd float %634, %640
  %642 = call %struct.qtree* @empty_qtree(float %609, float %610, float %611, float %617, float %629, float %641)
  store %struct.qtree* %642, %struct.qtree** %22, align 8
  %643 = load %struct.qtree*, %struct.qtree** %22, align 8
  %644 = load %struct.qtree*, %struct.qtree** %7, align 8
  %645 = getelementptr inbounds %struct.qtree, %struct.qtree* %644, i32 0, i32 4
  store %struct.qtree* %643, %struct.qtree** %645, align 8
  br label %646

646:                                              ; preds = %608, %577
  br label %647

647:                                              ; preds = %646, %543
  br label %648

648:                                              ; preds = %647, %516
  br label %649

649:                                              ; preds = %648, %480, %475, %470, %465
  %650 = load %struct.qtree*, %struct.qtree** %7, align 8
  %651 = getelementptr inbounds %struct.qtree, %struct.qtree* %650, i32 0, i32 0
  %652 = load %struct.quad*, %struct.quad** %651, align 8
  %653 = getelementptr inbounds %struct.quad, %struct.quad* %652, i32 0, i32 0
  %654 = load float, float* %653, align 8
  store float %654, float* %23, align 4
  %655 = load %struct.qtree*, %struct.qtree** %7, align 8
  %656 = getelementptr inbounds %struct.qtree, %struct.qtree* %655, i32 0, i32 2
  %657 = load %struct.qtree*, %struct.qtree** %656, align 8
  %658 = icmp eq %struct.qtree* %657, null
  br i1 %658, label %659, label %686

659:                                              ; preds = %649
  %660 = load float, float* %5, align 4
  %661 = load float, float* %6, align 4
  %662 = load float, float* %8, align 4
  %663 = load float, float* %23, align 4
  %664 = fpext float %663 to double
  %665 = fdiv double %664, 2.000000e+00
  %666 = fptrunc double %665 to float
  %667 = load %struct.qtree*, %struct.qtree** %7, align 8
  %668 = getelementptr inbounds %struct.qtree, %struct.qtree* %667, i32 0, i32 0
  %669 = load %struct.quad*, %struct.quad** %668, align 8
  %670 = getelementptr inbounds %struct.quad, %struct.quad* %669, i32 0, i32 2
  %671 = load float, float* %670, align 8
  %672 = load %struct.qtree*, %struct.qtree** %7, align 8
  %673 = getelementptr inbounds %struct.qtree, %struct.qtree* %672, i32 0, i32 0
  %674 = load %struct.quad*, %struct.quad** %673, align 8
  %675 = getelementptr inbounds %struct.quad, %struct.quad* %674, i32 0, i32 1
  %676 = load float, float* %675, align 4
  %677 = fpext float %676 to double
  %678 = load float, float* %23, align 4
  %679 = fpext float %678 to double
  %680 = fdiv double %679, 2.000000e+00
  %681 = fadd double %677, %680
  %682 = fptrunc double %681 to float
  %683 = call %struct.qtree* @empty_qtree(float %660, float %661, float %662, float %666, float %671, float %682)
  %684 = load %struct.qtree*, %struct.qtree** %7, align 8
  %685 = getelementptr inbounds %struct.qtree, %struct.qtree* %684, i32 0, i32 2
  store %struct.qtree* %683, %struct.qtree** %685, align 8
  br label %694

686:                                              ; preds = %649
  %687 = load float, float* %5, align 4
  %688 = load float, float* %6, align 4
  %689 = load %struct.qtree*, %struct.qtree** %7, align 8
  %690 = getelementptr inbounds %struct.qtree, %struct.qtree* %689, i32 0, i32 2
  %691 = load %struct.qtree*, %struct.qtree** %690, align 8
  %692 = load float, float* %8, align 4
  %693 = call %struct.qtree* @insertPoint(float %687, float %688, %struct.qtree* %691, float %692)
  br label %694

694:                                              ; preds = %686, %659
  %695 = load %struct.qtree*, %struct.qtree** %7, align 8
  %696 = getelementptr inbounds %struct.qtree, %struct.qtree* %695, i32 0, i32 1
  %697 = load %struct.qtree*, %struct.qtree** %696, align 8
  %698 = icmp ne %struct.qtree* %697, null
  br i1 %698, label %699, label %745

699:                                              ; preds = %694
  %700 = load %struct.qtree*, %struct.qtree** %7, align 8
  %701 = getelementptr inbounds %struct.qtree, %struct.qtree* %700, i32 0, i32 1
  %702 = load %struct.qtree*, %struct.qtree** %701, align 8
  %703 = getelementptr inbounds %struct.qtree, %struct.qtree* %702, i32 0, i32 0
  %704 = load %struct.quad*, %struct.quad** %703, align 8
  %705 = getelementptr inbounds %struct.quad, %struct.quad* %704, i32 0, i32 3
  %706 = load %struct.centroid*, %struct.centroid** %705, align 8
  %707 = load %struct.qtree*, %struct.qtree** %7, align 8
  %708 = getelementptr inbounds %struct.qtree, %struct.qtree* %707, i32 0, i32 2
  %709 = load %struct.qtree*, %struct.qtree** %708, align 8
  %710 = getelementptr inbounds %struct.qtree, %struct.qtree* %709, i32 0, i32 0
  %711 = load %struct.quad*, %struct.quad** %710, align 8
  %712 = getelementptr inbounds %struct.quad, %struct.quad* %711, i32 0, i32 3
  %713 = load %struct.centroid*, %struct.centroid** %712, align 8
  %714 = call %struct.centroid* @centroid_sum(%struct.centroid* %706, %struct.centroid* %713)
  store %struct.centroid* %714, %struct.centroid** %24, align 8
  %715 = load %struct.qtree*, %struct.qtree** %7, align 8
  %716 = getelementptr inbounds %struct.qtree, %struct.qtree* %715, i32 0, i32 4
  %717 = load %struct.qtree*, %struct.qtree** %716, align 8
  %718 = icmp ne %struct.qtree* %717, null
  br i1 %718, label %719, label %729

719:                                              ; preds = %699
  %720 = load %struct.centroid*, %struct.centroid** %24, align 8
  %721 = load %struct.qtree*, %struct.qtree** %7, align 8
  %722 = getelementptr inbounds %struct.qtree, %struct.qtree* %721, i32 0, i32 4
  %723 = load %struct.qtree*, %struct.qtree** %722, align 8
  %724 = getelementptr inbounds %struct.qtree, %struct.qtree* %723, i32 0, i32 0
  %725 = load %struct.quad*, %struct.quad** %724, align 8
  %726 = getelementptr inbounds %struct.quad, %struct.quad* %725, i32 0, i32 3
  %727 = load %struct.centroid*, %struct.centroid** %726, align 8
  %728 = call %struct.centroid* @centroid_sum(%struct.centroid* %720, %struct.centroid* %727)
  store %struct.centroid* %728, %struct.centroid** %24, align 8
  br label %729

729:                                              ; preds = %719, %699
  %730 = load %struct.qtree*, %struct.qtree** %7, align 8
  %731 = getelementptr inbounds %struct.qtree, %struct.qtree* %730, i32 0, i32 3
  %732 = load %struct.qtree*, %struct.qtree** %731, align 8
  %733 = icmp ne %struct.qtree* %732, null
  br i1 %733, label %734, label %744

734:                                              ; preds = %729
  %735 = load %struct.centroid*, %struct.centroid** %24, align 8
  %736 = load %struct.qtree*, %struct.qtree** %7, align 8
  %737 = getelementptr inbounds %struct.qtree, %struct.qtree* %736, i32 0, i32 3
  %738 = load %struct.qtree*, %struct.qtree** %737, align 8
  %739 = getelementptr inbounds %struct.qtree, %struct.qtree* %738, i32 0, i32 0
  %740 = load %struct.quad*, %struct.quad** %739, align 8
  %741 = getelementptr inbounds %struct.quad, %struct.quad* %740, i32 0, i32 3
  %742 = load %struct.centroid*, %struct.centroid** %741, align 8
  %743 = call %struct.centroid* @centroid_sum(%struct.centroid* %735, %struct.centroid* %742)
  store %struct.centroid* %743, %struct.centroid** %24, align 8
  br label %744

744:                                              ; preds = %734, %729
  br label %812

745:                                              ; preds = %694
  %746 = load %struct.qtree*, %struct.qtree** %7, align 8
  %747 = getelementptr inbounds %struct.qtree, %struct.qtree* %746, i32 0, i32 4
  %748 = load %struct.qtree*, %struct.qtree** %747, align 8
  %749 = icmp ne %struct.qtree* %748, null
  br i1 %749, label %750, label %781

750:                                              ; preds = %745
  %751 = load %struct.qtree*, %struct.qtree** %7, align 8
  %752 = getelementptr inbounds %struct.qtree, %struct.qtree* %751, i32 0, i32 2
  %753 = load %struct.qtree*, %struct.qtree** %752, align 8
  %754 = getelementptr inbounds %struct.qtree, %struct.qtree* %753, i32 0, i32 0
  %755 = load %struct.quad*, %struct.quad** %754, align 8
  %756 = getelementptr inbounds %struct.quad, %struct.quad* %755, i32 0, i32 3
  %757 = load %struct.centroid*, %struct.centroid** %756, align 8
  %758 = load %struct.qtree*, %struct.qtree** %7, align 8
  %759 = getelementptr inbounds %struct.qtree, %struct.qtree* %758, i32 0, i32 4
  %760 = load %struct.qtree*, %struct.qtree** %759, align 8
  %761 = getelementptr inbounds %struct.qtree, %struct.qtree* %760, i32 0, i32 0
  %762 = load %struct.quad*, %struct.quad** %761, align 8
  %763 = getelementptr inbounds %struct.quad, %struct.quad* %762, i32 0, i32 3
  %764 = load %struct.centroid*, %struct.centroid** %763, align 8
  %765 = call %struct.centroid* @centroid_sum(%struct.centroid* %757, %struct.centroid* %764)
  store %struct.centroid* %765, %struct.centroid** %24, align 8
  %766 = load %struct.qtree*, %struct.qtree** %7, align 8
  %767 = getelementptr inbounds %struct.qtree, %struct.qtree* %766, i32 0, i32 3
  %768 = load %struct.qtree*, %struct.qtree** %767, align 8
  %769 = icmp ne %struct.qtree* %768, null
  br i1 %769, label %770, label %780

770:                                              ; preds = %750
  %771 = load %struct.centroid*, %struct.centroid** %24, align 8
  %772 = load %struct.qtree*, %struct.qtree** %7, align 8
  %773 = getelementptr inbounds %struct.qtree, %struct.qtree* %772, i32 0, i32 3
  %774 = load %struct.qtree*, %struct.qtree** %773, align 8
  %775 = getelementptr inbounds %struct.qtree, %struct.qtree* %774, i32 0, i32 0
  %776 = load %struct.quad*, %struct.quad** %775, align 8
  %777 = getelementptr inbounds %struct.quad, %struct.quad* %776, i32 0, i32 3
  %778 = load %struct.centroid*, %struct.centroid** %777, align 8
  %779 = call %struct.centroid* @centroid_sum(%struct.centroid* %771, %struct.centroid* %778)
  store %struct.centroid* %779, %struct.centroid** %24, align 8
  br label %780

780:                                              ; preds = %770, %750
  br label %811

781:                                              ; preds = %745
  %782 = load %struct.qtree*, %struct.qtree** %7, align 8
  %783 = getelementptr inbounds %struct.qtree, %struct.qtree* %782, i32 0, i32 3
  %784 = load %struct.qtree*, %struct.qtree** %783, align 8
  %785 = icmp ne %struct.qtree* %784, null
  br i1 %785, label %786, label %802

786:                                              ; preds = %781
  %787 = load %struct.qtree*, %struct.qtree** %7, align 8
  %788 = getelementptr inbounds %struct.qtree, %struct.qtree* %787, i32 0, i32 2
  %789 = load %struct.qtree*, %struct.qtree** %788, align 8
  %790 = getelementptr inbounds %struct.qtree, %struct.qtree* %789, i32 0, i32 0
  %791 = load %struct.quad*, %struct.quad** %790, align 8
  %792 = getelementptr inbounds %struct.quad, %struct.quad* %791, i32 0, i32 3
  %793 = load %struct.centroid*, %struct.centroid** %792, align 8
  %794 = load %struct.qtree*, %struct.qtree** %7, align 8
  %795 = getelementptr inbounds %struct.qtree, %struct.qtree* %794, i32 0, i32 3
  %796 = load %struct.qtree*, %struct.qtree** %795, align 8
  %797 = getelementptr inbounds %struct.qtree, %struct.qtree* %796, i32 0, i32 0
  %798 = load %struct.quad*, %struct.quad** %797, align 8
  %799 = getelementptr inbounds %struct.quad, %struct.quad* %798, i32 0, i32 3
  %800 = load %struct.centroid*, %struct.centroid** %799, align 8
  %801 = call %struct.centroid* @centroid_sum(%struct.centroid* %793, %struct.centroid* %800)
  store %struct.centroid* %801, %struct.centroid** %24, align 8
  br label %810

802:                                              ; preds = %781
  %803 = load %struct.qtree*, %struct.qtree** %7, align 8
  %804 = getelementptr inbounds %struct.qtree, %struct.qtree* %803, i32 0, i32 2
  %805 = load %struct.qtree*, %struct.qtree** %804, align 8
  %806 = getelementptr inbounds %struct.qtree, %struct.qtree* %805, i32 0, i32 0
  %807 = load %struct.quad*, %struct.quad** %806, align 8
  %808 = getelementptr inbounds %struct.quad, %struct.quad* %807, i32 0, i32 3
  %809 = load %struct.centroid*, %struct.centroid** %808, align 8
  store %struct.centroid* %809, %struct.centroid** %24, align 8
  br label %810

810:                                              ; preds = %802, %786
  br label %811

811:                                              ; preds = %810, %780
  br label %812

812:                                              ; preds = %811, %744
  %813 = load %struct.centroid*, %struct.centroid** %24, align 8
  %814 = load %struct.qtree*, %struct.qtree** %7, align 8
  %815 = getelementptr inbounds %struct.qtree, %struct.qtree* %814, i32 0, i32 0
  %816 = load %struct.quad*, %struct.quad** %815, align 8
  %817 = getelementptr inbounds %struct.quad, %struct.quad* %816, i32 0, i32 3
  store %struct.centroid* %813, %struct.centroid** %817, align 8
  br label %2126

818:                                              ; preds = %460, %452
  %819 = load float, float* %5, align 4
  %820 = load float, float* %6, align 4
  %821 = load %struct.qtree*, %struct.qtree** %7, align 8
  %822 = getelementptr inbounds %struct.qtree, %struct.qtree* %821, i32 0, i32 0
  %823 = load %struct.quad*, %struct.quad** %822, align 8
  %824 = call i32 @which_quad(float %819, float %820, %struct.quad* %823)
  %825 = icmp eq i32 %824, 3
  br i1 %825, label %826, label %1184

826:                                              ; preds = %818
  %827 = load %struct.qtree*, %struct.qtree** %7, align 8
  %828 = getelementptr inbounds %struct.qtree, %struct.qtree* %827, i32 0, i32 3
  %829 = load %struct.qtree*, %struct.qtree** %828, align 8
  %830 = icmp eq %struct.qtree* %829, null
  br i1 %830, label %831, label %1184

831:                                              ; preds = %826
  %832 = load %struct.qtree*, %struct.qtree** %7, align 8
  %833 = getelementptr inbounds %struct.qtree, %struct.qtree* %832, i32 0, i32 1
  %834 = load %struct.qtree*, %struct.qtree** %833, align 8
  %835 = icmp eq %struct.qtree* %834, null
  br i1 %835, label %836, label %1015

836:                                              ; preds = %831
  %837 = load %struct.qtree*, %struct.qtree** %7, align 8
  %838 = getelementptr inbounds %struct.qtree, %struct.qtree* %837, i32 0, i32 2
  %839 = load %struct.qtree*, %struct.qtree** %838, align 8
  %840 = icmp eq %struct.qtree* %839, null
  br i1 %840, label %841, label %1015

841:                                              ; preds = %836
  %842 = load %struct.qtree*, %struct.qtree** %7, align 8
  %843 = getelementptr inbounds %struct.qtree, %struct.qtree* %842, i32 0, i32 3
  %844 = load %struct.qtree*, %struct.qtree** %843, align 8
  %845 = icmp eq %struct.qtree* %844, null
  br i1 %845, label %846, label %1015

846:                                              ; preds = %841
  %847 = load %struct.qtree*, %struct.qtree** %7, align 8
  %848 = getelementptr inbounds %struct.qtree, %struct.qtree* %847, i32 0, i32 4
  %849 = load %struct.qtree*, %struct.qtree** %848, align 8
  %850 = icmp eq %struct.qtree* %849, null
  br i1 %850, label %851, label %1015

851:                                              ; preds = %846
  %852 = load %struct.qtree*, %struct.qtree** %7, align 8
  %853 = getelementptr inbounds %struct.qtree, %struct.qtree* %852, i32 0, i32 0
  %854 = load %struct.quad*, %struct.quad** %853, align 8
  %855 = getelementptr inbounds %struct.quad, %struct.quad* %854, i32 0, i32 3
  %856 = load %struct.centroid*, %struct.centroid** %855, align 8
  %857 = getelementptr inbounds %struct.centroid, %struct.centroid* %856, i32 0, i32 0
  %858 = load float, float* %857, align 4
  store float %858, float* %25, align 4
  %859 = load %struct.qtree*, %struct.qtree** %7, align 8
  %860 = getelementptr inbounds %struct.qtree, %struct.qtree* %859, i32 0, i32 0
  %861 = load %struct.quad*, %struct.quad** %860, align 8
  %862 = getelementptr inbounds %struct.quad, %struct.quad* %861, i32 0, i32 3
  %863 = load %struct.centroid*, %struct.centroid** %862, align 8
  %864 = getelementptr inbounds %struct.centroid, %struct.centroid* %863, i32 0, i32 1
  %865 = load float, float* %864, align 4
  store float %865, float* %26, align 4
  %866 = load %struct.qtree*, %struct.qtree** %7, align 8
  %867 = getelementptr inbounds %struct.qtree, %struct.qtree* %866, i32 0, i32 0
  %868 = load %struct.quad*, %struct.quad** %867, align 8
  %869 = getelementptr inbounds %struct.quad, %struct.quad* %868, i32 0, i32 3
  %870 = load %struct.centroid*, %struct.centroid** %869, align 8
  %871 = getelementptr inbounds %struct.centroid, %struct.centroid* %870, i32 0, i32 2
  %872 = load float, float* %871, align 4
  store float %872, float* %27, align 4
  %873 = load float, float* %25, align 4
  %874 = load float, float* %26, align 4
  %875 = load %struct.qtree*, %struct.qtree** %7, align 8
  %876 = getelementptr inbounds %struct.qtree, %struct.qtree* %875, i32 0, i32 0
  %877 = load %struct.quad*, %struct.quad** %876, align 8
  %878 = call i32 @which_quad(float %873, float %874, %struct.quad* %877)
  %879 = sitofp i32 %878 to float
  store float %879, float* %28, align 4
  %880 = load float, float* %28, align 4
  %881 = fcmp oeq float %880, 1.000000e+00
  br i1 %881, label %882, label %906

882:                                              ; preds = %851
  %883 = load float, float* %25, align 4
  %884 = load float, float* %26, align 4
  %885 = load float, float* %27, align 4
  %886 = load %struct.qtree*, %struct.qtree** %7, align 8
  %887 = getelementptr inbounds %struct.qtree, %struct.qtree* %886, i32 0, i32 0
  %888 = load %struct.quad*, %struct.quad** %887, align 8
  %889 = getelementptr inbounds %struct.quad, %struct.quad* %888, i32 0, i32 0
  %890 = load float, float* %889, align 8
  %891 = fdiv float %890, 2.000000e+00
  %892 = load %struct.qtree*, %struct.qtree** %7, align 8
  %893 = getelementptr inbounds %struct.qtree, %struct.qtree* %892, i32 0, i32 0
  %894 = load %struct.quad*, %struct.quad** %893, align 8
  %895 = getelementptr inbounds %struct.quad, %struct.quad* %894, i32 0, i32 2
  %896 = load float, float* %895, align 8
  %897 = load %struct.qtree*, %struct.qtree** %7, align 8
  %898 = getelementptr inbounds %struct.qtree, %struct.qtree* %897, i32 0, i32 0
  %899 = load %struct.quad*, %struct.quad** %898, align 8
  %900 = getelementptr inbounds %struct.quad, %struct.quad* %899, i32 0, i32 1
  %901 = load float, float* %900, align 4
  %902 = call %struct.qtree* @empty_qtree(float %883, float %884, float %885, float %891, float %896, float %901)
  store %struct.qtree* %902, %struct.qtree** %29, align 8
  %903 = load %struct.qtree*, %struct.qtree** %29, align 8
  %904 = load %struct.qtree*, %struct.qtree** %7, align 8
  %905 = getelementptr inbounds %struct.qtree, %struct.qtree* %904, i32 0, i32 1
  store %struct.qtree* %903, %struct.qtree** %905, align 8
  br label %1014

906:                                              ; preds = %851
  %907 = load float, float* %28, align 4
  %908 = fcmp oeq float %907, 3.000000e+00
  br i1 %908, label %909, label %940

909:                                              ; preds = %906
  %910 = load float, float* %25, align 4
  %911 = load float, float* %26, align 4
  %912 = load float, float* %27, align 4
  %913 = load %struct.qtree*, %struct.qtree** %7, align 8
  %914 = getelementptr inbounds %struct.qtree, %struct.qtree* %913, i32 0, i32 0
  %915 = load %struct.quad*, %struct.quad** %914, align 8
  %916 = getelementptr inbounds %struct.quad, %struct.quad* %915, i32 0, i32 0
  %917 = load float, float* %916, align 8
  %918 = fdiv float %917, 2.000000e+00
  %919 = load %struct.qtree*, %struct.qtree** %7, align 8
  %920 = getelementptr inbounds %struct.qtree, %struct.qtree* %919, i32 0, i32 0
  %921 = load %struct.quad*, %struct.quad** %920, align 8
  %922 = getelementptr inbounds %struct.quad, %struct.quad* %921, i32 0, i32 2
  %923 = load float, float* %922, align 8
  %924 = load %struct.qtree*, %struct.qtree** %7, align 8
  %925 = getelementptr inbounds %struct.qtree, %struct.qtree* %924, i32 0, i32 0
  %926 = load %struct.quad*, %struct.quad** %925, align 8
  %927 = getelementptr inbounds %struct.quad, %struct.quad* %926, i32 0, i32 0
  %928 = load float, float* %927, align 8
  %929 = fdiv float %928, 2.000000e+00
  %930 = fadd float %923, %929
  %931 = load %struct.qtree*, %struct.qtree** %7, align 8
  %932 = getelementptr inbounds %struct.qtree, %struct.qtree* %931, i32 0, i32 0
  %933 = load %struct.quad*, %struct.quad** %932, align 8
  %934 = getelementptr inbounds %struct.quad, %struct.quad* %933, i32 0, i32 1
  %935 = load float, float* %934, align 4
  %936 = call %struct.qtree* @empty_qtree(float %910, float %911, float %912, float %918, float %930, float %935)
  store %struct.qtree* %936, %struct.qtree** %29, align 8
  %937 = load %struct.qtree*, %struct.qtree** %29, align 8
  %938 = load %struct.qtree*, %struct.qtree** %7, align 8
  %939 = getelementptr inbounds %struct.qtree, %struct.qtree* %938, i32 0, i32 3
  store %struct.qtree* %937, %struct.qtree** %939, align 8
  br label %1013

940:                                              ; preds = %906
  %941 = load float, float* %28, align 4
  %942 = fcmp oeq float %941, 2.000000e+00
  br i1 %942, label %943, label %974

943:                                              ; preds = %940
  %944 = load float, float* %25, align 4
  %945 = load float, float* %26, align 4
  %946 = load float, float* %27, align 4
  %947 = load %struct.qtree*, %struct.qtree** %7, align 8
  %948 = getelementptr inbounds %struct.qtree, %struct.qtree* %947, i32 0, i32 0
  %949 = load %struct.quad*, %struct.quad** %948, align 8
  %950 = getelementptr inbounds %struct.quad, %struct.quad* %949, i32 0, i32 0
  %951 = load float, float* %950, align 8
  %952 = fdiv float %951, 2.000000e+00
  %953 = load %struct.qtree*, %struct.qtree** %7, align 8
  %954 = getelementptr inbounds %struct.qtree, %struct.qtree* %953, i32 0, i32 0
  %955 = load %struct.quad*, %struct.quad** %954, align 8
  %956 = getelementptr inbounds %struct.quad, %struct.quad* %955, i32 0, i32 2
  %957 = load float, float* %956, align 8
  %958 = load %struct.qtree*, %struct.qtree** %7, align 8
  %959 = getelementptr inbounds %struct.qtree, %struct.qtree* %958, i32 0, i32 0
  %960 = load %struct.quad*, %struct.quad** %959, align 8
  %961 = getelementptr inbounds %struct.quad, %struct.quad* %960, i32 0, i32 1
  %962 = load float, float* %961, align 4
  %963 = load %struct.qtree*, %struct.qtree** %7, align 8
  %964 = getelementptr inbounds %struct.qtree, %struct.qtree* %963, i32 0, i32 0
  %965 = load %struct.quad*, %struct.quad** %964, align 8
  %966 = getelementptr inbounds %struct.quad, %struct.quad* %965, i32 0, i32 0
  %967 = load float, float* %966, align 8
  %968 = fdiv float %967, 2.000000e+00
  %969 = fadd float %962, %968
  %970 = call %struct.qtree* @empty_qtree(float %944, float %945, float %946, float %952, float %957, float %969)
  store %struct.qtree* %970, %struct.qtree** %29, align 8
  %971 = load %struct.qtree*, %struct.qtree** %29, align 8
  %972 = load %struct.qtree*, %struct.qtree** %7, align 8
  %973 = getelementptr inbounds %struct.qtree, %struct.qtree* %972, i32 0, i32 2
  store %struct.qtree* %971, %struct.qtree** %973, align 8
  br label %1012

974:                                              ; preds = %940
  %975 = load float, float* %25, align 4
  %976 = load float, float* %26, align 4
  %977 = load float, float* %27, align 4
  %978 = load %struct.qtree*, %struct.qtree** %7, align 8
  %979 = getelementptr inbounds %struct.qtree, %struct.qtree* %978, i32 0, i32 0
  %980 = load %struct.quad*, %struct.quad** %979, align 8
  %981 = getelementptr inbounds %struct.quad, %struct.quad* %980, i32 0, i32 0
  %982 = load float, float* %981, align 8
  %983 = fdiv float %982, 2.000000e+00
  %984 = load %struct.qtree*, %struct.qtree** %7, align 8
  %985 = getelementptr inbounds %struct.qtree, %struct.qtree* %984, i32 0, i32 0
  %986 = load %struct.quad*, %struct.quad** %985, align 8
  %987 = getelementptr inbounds %struct.quad, %struct.quad* %986, i32 0, i32 2
  %988 = load float, float* %987, align 8
  %989 = load %struct.qtree*, %struct.qtree** %7, align 8
  %990 = getelementptr inbounds %struct.qtree, %struct.qtree* %989, i32 0, i32 0
  %991 = load %struct.quad*, %struct.quad** %990, align 8
  %992 = getelementptr inbounds %struct.quad, %struct.quad* %991, i32 0, i32 0
  %993 = load float, float* %992, align 8
  %994 = fdiv float %993, 2.000000e+00
  %995 = fadd float %988, %994
  %996 = load %struct.qtree*, %struct.qtree** %7, align 8
  %997 = getelementptr inbounds %struct.qtree, %struct.qtree* %996, i32 0, i32 0
  %998 = load %struct.quad*, %struct.quad** %997, align 8
  %999 = getelementptr inbounds %struct.quad, %struct.quad* %998, i32 0, i32 1
  %1000 = load float, float* %999, align 4
  %1001 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1002 = getelementptr inbounds %struct.qtree, %struct.qtree* %1001, i32 0, i32 0
  %1003 = load %struct.quad*, %struct.quad** %1002, align 8
  %1004 = getelementptr inbounds %struct.quad, %struct.quad* %1003, i32 0, i32 0
  %1005 = load float, float* %1004, align 8
  %1006 = fdiv float %1005, 2.000000e+00
  %1007 = fadd float %1000, %1006
  %1008 = call %struct.qtree* @empty_qtree(float %975, float %976, float %977, float %983, float %995, float %1007)
  store %struct.qtree* %1008, %struct.qtree** %29, align 8
  %1009 = load %struct.qtree*, %struct.qtree** %29, align 8
  %1010 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1011 = getelementptr inbounds %struct.qtree, %struct.qtree* %1010, i32 0, i32 4
  store %struct.qtree* %1009, %struct.qtree** %1011, align 8
  br label %1012

1012:                                             ; preds = %974, %943
  br label %1013

1013:                                             ; preds = %1012, %909
  br label %1014

1014:                                             ; preds = %1013, %882
  br label %1015

1015:                                             ; preds = %1014, %846, %841, %836, %831
  %1016 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1017 = getelementptr inbounds %struct.qtree, %struct.qtree* %1016, i32 0, i32 0
  %1018 = load %struct.quad*, %struct.quad** %1017, align 8
  %1019 = getelementptr inbounds %struct.quad, %struct.quad* %1018, i32 0, i32 0
  %1020 = load float, float* %1019, align 8
  store float %1020, float* %30, align 4
  %1021 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1022 = getelementptr inbounds %struct.qtree, %struct.qtree* %1021, i32 0, i32 3
  %1023 = load %struct.qtree*, %struct.qtree** %1022, align 8
  %1024 = icmp eq %struct.qtree* %1023, null
  br i1 %1024, label %1025, label %1052

1025:                                             ; preds = %1015
  %1026 = load float, float* %5, align 4
  %1027 = load float, float* %6, align 4
  %1028 = load float, float* %8, align 4
  %1029 = load float, float* %30, align 4
  %1030 = fpext float %1029 to double
  %1031 = fdiv double %1030, 2.000000e+00
  %1032 = fptrunc double %1031 to float
  %1033 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1034 = getelementptr inbounds %struct.qtree, %struct.qtree* %1033, i32 0, i32 0
  %1035 = load %struct.quad*, %struct.quad** %1034, align 8
  %1036 = getelementptr inbounds %struct.quad, %struct.quad* %1035, i32 0, i32 2
  %1037 = load float, float* %1036, align 8
  %1038 = fpext float %1037 to double
  %1039 = load float, float* %30, align 4
  %1040 = fpext float %1039 to double
  %1041 = fdiv double %1040, 2.000000e+00
  %1042 = fadd double %1038, %1041
  %1043 = fptrunc double %1042 to float
  %1044 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1045 = getelementptr inbounds %struct.qtree, %struct.qtree* %1044, i32 0, i32 0
  %1046 = load %struct.quad*, %struct.quad** %1045, align 8
  %1047 = getelementptr inbounds %struct.quad, %struct.quad* %1046, i32 0, i32 1
  %1048 = load float, float* %1047, align 4
  %1049 = call %struct.qtree* @empty_qtree(float %1026, float %1027, float %1028, float %1032, float %1043, float %1048)
  %1050 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1051 = getelementptr inbounds %struct.qtree, %struct.qtree* %1050, i32 0, i32 3
  store %struct.qtree* %1049, %struct.qtree** %1051, align 8
  br label %1060

1052:                                             ; preds = %1015
  %1053 = load float, float* %5, align 4
  %1054 = load float, float* %6, align 4
  %1055 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1056 = getelementptr inbounds %struct.qtree, %struct.qtree* %1055, i32 0, i32 3
  %1057 = load %struct.qtree*, %struct.qtree** %1056, align 8
  %1058 = load float, float* %8, align 4
  %1059 = call %struct.qtree* @insertPoint(float %1053, float %1054, %struct.qtree* %1057, float %1058)
  br label %1060

1060:                                             ; preds = %1052, %1025
  %1061 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1062 = getelementptr inbounds %struct.qtree, %struct.qtree* %1061, i32 0, i32 1
  %1063 = load %struct.qtree*, %struct.qtree** %1062, align 8
  %1064 = icmp ne %struct.qtree* %1063, null
  br i1 %1064, label %1065, label %1111

1065:                                             ; preds = %1060
  %1066 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1067 = getelementptr inbounds %struct.qtree, %struct.qtree* %1066, i32 0, i32 1
  %1068 = load %struct.qtree*, %struct.qtree** %1067, align 8
  %1069 = getelementptr inbounds %struct.qtree, %struct.qtree* %1068, i32 0, i32 0
  %1070 = load %struct.quad*, %struct.quad** %1069, align 8
  %1071 = getelementptr inbounds %struct.quad, %struct.quad* %1070, i32 0, i32 3
  %1072 = load %struct.centroid*, %struct.centroid** %1071, align 8
  %1073 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1074 = getelementptr inbounds %struct.qtree, %struct.qtree* %1073, i32 0, i32 3
  %1075 = load %struct.qtree*, %struct.qtree** %1074, align 8
  %1076 = getelementptr inbounds %struct.qtree, %struct.qtree* %1075, i32 0, i32 0
  %1077 = load %struct.quad*, %struct.quad** %1076, align 8
  %1078 = getelementptr inbounds %struct.quad, %struct.quad* %1077, i32 0, i32 3
  %1079 = load %struct.centroid*, %struct.centroid** %1078, align 8
  %1080 = call %struct.centroid* @centroid_sum(%struct.centroid* %1072, %struct.centroid* %1079)
  store %struct.centroid* %1080, %struct.centroid** %31, align 8
  %1081 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1082 = getelementptr inbounds %struct.qtree, %struct.qtree* %1081, i32 0, i32 2
  %1083 = load %struct.qtree*, %struct.qtree** %1082, align 8
  %1084 = icmp ne %struct.qtree* %1083, null
  br i1 %1084, label %1085, label %1095

1085:                                             ; preds = %1065
  %1086 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1087 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1088 = getelementptr inbounds %struct.qtree, %struct.qtree* %1087, i32 0, i32 2
  %1089 = load %struct.qtree*, %struct.qtree** %1088, align 8
  %1090 = getelementptr inbounds %struct.qtree, %struct.qtree* %1089, i32 0, i32 0
  %1091 = load %struct.quad*, %struct.quad** %1090, align 8
  %1092 = getelementptr inbounds %struct.quad, %struct.quad* %1091, i32 0, i32 3
  %1093 = load %struct.centroid*, %struct.centroid** %1092, align 8
  %1094 = call %struct.centroid* @centroid_sum(%struct.centroid* %1086, %struct.centroid* %1093)
  store %struct.centroid* %1094, %struct.centroid** %31, align 8
  br label %1095

1095:                                             ; preds = %1085, %1065
  %1096 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1097 = getelementptr inbounds %struct.qtree, %struct.qtree* %1096, i32 0, i32 4
  %1098 = load %struct.qtree*, %struct.qtree** %1097, align 8
  %1099 = icmp ne %struct.qtree* %1098, null
  br i1 %1099, label %1100, label %1110

1100:                                             ; preds = %1095
  %1101 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1102 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1103 = getelementptr inbounds %struct.qtree, %struct.qtree* %1102, i32 0, i32 4
  %1104 = load %struct.qtree*, %struct.qtree** %1103, align 8
  %1105 = getelementptr inbounds %struct.qtree, %struct.qtree* %1104, i32 0, i32 0
  %1106 = load %struct.quad*, %struct.quad** %1105, align 8
  %1107 = getelementptr inbounds %struct.quad, %struct.quad* %1106, i32 0, i32 3
  %1108 = load %struct.centroid*, %struct.centroid** %1107, align 8
  %1109 = call %struct.centroid* @centroid_sum(%struct.centroid* %1101, %struct.centroid* %1108)
  store %struct.centroid* %1109, %struct.centroid** %31, align 8
  br label %1110

1110:                                             ; preds = %1100, %1095
  br label %1178

1111:                                             ; preds = %1060
  %1112 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1113 = getelementptr inbounds %struct.qtree, %struct.qtree* %1112, i32 0, i32 2
  %1114 = load %struct.qtree*, %struct.qtree** %1113, align 8
  %1115 = icmp ne %struct.qtree* %1114, null
  br i1 %1115, label %1116, label %1147

1116:                                             ; preds = %1111
  %1117 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1118 = getelementptr inbounds %struct.qtree, %struct.qtree* %1117, i32 0, i32 2
  %1119 = load %struct.qtree*, %struct.qtree** %1118, align 8
  %1120 = getelementptr inbounds %struct.qtree, %struct.qtree* %1119, i32 0, i32 0
  %1121 = load %struct.quad*, %struct.quad** %1120, align 8
  %1122 = getelementptr inbounds %struct.quad, %struct.quad* %1121, i32 0, i32 3
  %1123 = load %struct.centroid*, %struct.centroid** %1122, align 8
  %1124 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1125 = getelementptr inbounds %struct.qtree, %struct.qtree* %1124, i32 0, i32 3
  %1126 = load %struct.qtree*, %struct.qtree** %1125, align 8
  %1127 = getelementptr inbounds %struct.qtree, %struct.qtree* %1126, i32 0, i32 0
  %1128 = load %struct.quad*, %struct.quad** %1127, align 8
  %1129 = getelementptr inbounds %struct.quad, %struct.quad* %1128, i32 0, i32 3
  %1130 = load %struct.centroid*, %struct.centroid** %1129, align 8
  %1131 = call %struct.centroid* @centroid_sum(%struct.centroid* %1123, %struct.centroid* %1130)
  store %struct.centroid* %1131, %struct.centroid** %31, align 8
  %1132 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1133 = getelementptr inbounds %struct.qtree, %struct.qtree* %1132, i32 0, i32 4
  %1134 = load %struct.qtree*, %struct.qtree** %1133, align 8
  %1135 = icmp ne %struct.qtree* %1134, null
  br i1 %1135, label %1136, label %1146

1136:                                             ; preds = %1116
  %1137 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1138 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1139 = getelementptr inbounds %struct.qtree, %struct.qtree* %1138, i32 0, i32 4
  %1140 = load %struct.qtree*, %struct.qtree** %1139, align 8
  %1141 = getelementptr inbounds %struct.qtree, %struct.qtree* %1140, i32 0, i32 0
  %1142 = load %struct.quad*, %struct.quad** %1141, align 8
  %1143 = getelementptr inbounds %struct.quad, %struct.quad* %1142, i32 0, i32 3
  %1144 = load %struct.centroid*, %struct.centroid** %1143, align 8
  %1145 = call %struct.centroid* @centroid_sum(%struct.centroid* %1137, %struct.centroid* %1144)
  store %struct.centroid* %1145, %struct.centroid** %31, align 8
  br label %1146

1146:                                             ; preds = %1136, %1116
  br label %1177

1147:                                             ; preds = %1111
  %1148 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1149 = getelementptr inbounds %struct.qtree, %struct.qtree* %1148, i32 0, i32 4
  %1150 = load %struct.qtree*, %struct.qtree** %1149, align 8
  %1151 = icmp ne %struct.qtree* %1150, null
  br i1 %1151, label %1152, label %1168

1152:                                             ; preds = %1147
  %1153 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1154 = getelementptr inbounds %struct.qtree, %struct.qtree* %1153, i32 0, i32 3
  %1155 = load %struct.qtree*, %struct.qtree** %1154, align 8
  %1156 = getelementptr inbounds %struct.qtree, %struct.qtree* %1155, i32 0, i32 0
  %1157 = load %struct.quad*, %struct.quad** %1156, align 8
  %1158 = getelementptr inbounds %struct.quad, %struct.quad* %1157, i32 0, i32 3
  %1159 = load %struct.centroid*, %struct.centroid** %1158, align 8
  %1160 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1161 = getelementptr inbounds %struct.qtree, %struct.qtree* %1160, i32 0, i32 4
  %1162 = load %struct.qtree*, %struct.qtree** %1161, align 8
  %1163 = getelementptr inbounds %struct.qtree, %struct.qtree* %1162, i32 0, i32 0
  %1164 = load %struct.quad*, %struct.quad** %1163, align 8
  %1165 = getelementptr inbounds %struct.quad, %struct.quad* %1164, i32 0, i32 3
  %1166 = load %struct.centroid*, %struct.centroid** %1165, align 8
  %1167 = call %struct.centroid* @centroid_sum(%struct.centroid* %1159, %struct.centroid* %1166)
  store %struct.centroid* %1167, %struct.centroid** %31, align 8
  br label %1176

1168:                                             ; preds = %1147
  %1169 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1170 = getelementptr inbounds %struct.qtree, %struct.qtree* %1169, i32 0, i32 3
  %1171 = load %struct.qtree*, %struct.qtree** %1170, align 8
  %1172 = getelementptr inbounds %struct.qtree, %struct.qtree* %1171, i32 0, i32 0
  %1173 = load %struct.quad*, %struct.quad** %1172, align 8
  %1174 = getelementptr inbounds %struct.quad, %struct.quad* %1173, i32 0, i32 3
  %1175 = load %struct.centroid*, %struct.centroid** %1174, align 8
  store %struct.centroid* %1175, %struct.centroid** %31, align 8
  br label %1176

1176:                                             ; preds = %1168, %1152
  br label %1177

1177:                                             ; preds = %1176, %1146
  br label %1178

1178:                                             ; preds = %1177, %1110
  %1179 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1180 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1181 = getelementptr inbounds %struct.qtree, %struct.qtree* %1180, i32 0, i32 0
  %1182 = load %struct.quad*, %struct.quad** %1181, align 8
  %1183 = getelementptr inbounds %struct.quad, %struct.quad* %1182, i32 0, i32 3
  store %struct.centroid* %1179, %struct.centroid** %1183, align 8
  br label %2125

1184:                                             ; preds = %826, %818
  %1185 = load float, float* %5, align 4
  %1186 = load float, float* %6, align 4
  %1187 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1188 = getelementptr inbounds %struct.qtree, %struct.qtree* %1187, i32 0, i32 0
  %1189 = load %struct.quad*, %struct.quad** %1188, align 8
  %1190 = call i32 @which_quad(float %1185, float %1186, %struct.quad* %1189)
  %1191 = icmp eq i32 %1190, 4
  br i1 %1191, label %1192, label %1556

1192:                                             ; preds = %1184
  %1193 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1194 = getelementptr inbounds %struct.qtree, %struct.qtree* %1193, i32 0, i32 4
  %1195 = load %struct.qtree*, %struct.qtree** %1194, align 8
  %1196 = icmp eq %struct.qtree* %1195, null
  br i1 %1196, label %1197, label %1556

1197:                                             ; preds = %1192
  %1198 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1199 = getelementptr inbounds %struct.qtree, %struct.qtree* %1198, i32 0, i32 1
  %1200 = load %struct.qtree*, %struct.qtree** %1199, align 8
  %1201 = icmp eq %struct.qtree* %1200, null
  br i1 %1201, label %1202, label %1381

1202:                                             ; preds = %1197
  %1203 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1204 = getelementptr inbounds %struct.qtree, %struct.qtree* %1203, i32 0, i32 2
  %1205 = load %struct.qtree*, %struct.qtree** %1204, align 8
  %1206 = icmp eq %struct.qtree* %1205, null
  br i1 %1206, label %1207, label %1381

1207:                                             ; preds = %1202
  %1208 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1209 = getelementptr inbounds %struct.qtree, %struct.qtree* %1208, i32 0, i32 3
  %1210 = load %struct.qtree*, %struct.qtree** %1209, align 8
  %1211 = icmp eq %struct.qtree* %1210, null
  br i1 %1211, label %1212, label %1381

1212:                                             ; preds = %1207
  %1213 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1214 = getelementptr inbounds %struct.qtree, %struct.qtree* %1213, i32 0, i32 4
  %1215 = load %struct.qtree*, %struct.qtree** %1214, align 8
  %1216 = icmp eq %struct.qtree* %1215, null
  br i1 %1216, label %1217, label %1381

1217:                                             ; preds = %1212
  %1218 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1219 = getelementptr inbounds %struct.qtree, %struct.qtree* %1218, i32 0, i32 0
  %1220 = load %struct.quad*, %struct.quad** %1219, align 8
  %1221 = getelementptr inbounds %struct.quad, %struct.quad* %1220, i32 0, i32 3
  %1222 = load %struct.centroid*, %struct.centroid** %1221, align 8
  %1223 = getelementptr inbounds %struct.centroid, %struct.centroid* %1222, i32 0, i32 0
  %1224 = load float, float* %1223, align 4
  store float %1224, float* %32, align 4
  %1225 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1226 = getelementptr inbounds %struct.qtree, %struct.qtree* %1225, i32 0, i32 0
  %1227 = load %struct.quad*, %struct.quad** %1226, align 8
  %1228 = getelementptr inbounds %struct.quad, %struct.quad* %1227, i32 0, i32 3
  %1229 = load %struct.centroid*, %struct.centroid** %1228, align 8
  %1230 = getelementptr inbounds %struct.centroid, %struct.centroid* %1229, i32 0, i32 1
  %1231 = load float, float* %1230, align 4
  store float %1231, float* %33, align 4
  %1232 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1233 = getelementptr inbounds %struct.qtree, %struct.qtree* %1232, i32 0, i32 0
  %1234 = load %struct.quad*, %struct.quad** %1233, align 8
  %1235 = getelementptr inbounds %struct.quad, %struct.quad* %1234, i32 0, i32 3
  %1236 = load %struct.centroid*, %struct.centroid** %1235, align 8
  %1237 = getelementptr inbounds %struct.centroid, %struct.centroid* %1236, i32 0, i32 2
  %1238 = load float, float* %1237, align 4
  store float %1238, float* %34, align 4
  %1239 = load float, float* %32, align 4
  %1240 = load float, float* %33, align 4
  %1241 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1242 = getelementptr inbounds %struct.qtree, %struct.qtree* %1241, i32 0, i32 0
  %1243 = load %struct.quad*, %struct.quad** %1242, align 8
  %1244 = call i32 @which_quad(float %1239, float %1240, %struct.quad* %1243)
  %1245 = sitofp i32 %1244 to float
  store float %1245, float* %35, align 4
  %1246 = load float, float* %35, align 4
  %1247 = fcmp oeq float %1246, 1.000000e+00
  br i1 %1247, label %1248, label %1272

1248:                                             ; preds = %1217
  %1249 = load float, float* %32, align 4
  %1250 = load float, float* %33, align 4
  %1251 = load float, float* %34, align 4
  %1252 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1253 = getelementptr inbounds %struct.qtree, %struct.qtree* %1252, i32 0, i32 0
  %1254 = load %struct.quad*, %struct.quad** %1253, align 8
  %1255 = getelementptr inbounds %struct.quad, %struct.quad* %1254, i32 0, i32 0
  %1256 = load float, float* %1255, align 8
  %1257 = fdiv float %1256, 2.000000e+00
  %1258 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1259 = getelementptr inbounds %struct.qtree, %struct.qtree* %1258, i32 0, i32 0
  %1260 = load %struct.quad*, %struct.quad** %1259, align 8
  %1261 = getelementptr inbounds %struct.quad, %struct.quad* %1260, i32 0, i32 2
  %1262 = load float, float* %1261, align 8
  %1263 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1264 = getelementptr inbounds %struct.qtree, %struct.qtree* %1263, i32 0, i32 0
  %1265 = load %struct.quad*, %struct.quad** %1264, align 8
  %1266 = getelementptr inbounds %struct.quad, %struct.quad* %1265, i32 0, i32 1
  %1267 = load float, float* %1266, align 4
  %1268 = call %struct.qtree* @empty_qtree(float %1249, float %1250, float %1251, float %1257, float %1262, float %1267)
  store %struct.qtree* %1268, %struct.qtree** %36, align 8
  %1269 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1270 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1271 = getelementptr inbounds %struct.qtree, %struct.qtree* %1270, i32 0, i32 1
  store %struct.qtree* %1269, %struct.qtree** %1271, align 8
  br label %1380

1272:                                             ; preds = %1217
  %1273 = load float, float* %35, align 4
  %1274 = fcmp oeq float %1273, 3.000000e+00
  br i1 %1274, label %1275, label %1306

1275:                                             ; preds = %1272
  %1276 = load float, float* %32, align 4
  %1277 = load float, float* %33, align 4
  %1278 = load float, float* %34, align 4
  %1279 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1280 = getelementptr inbounds %struct.qtree, %struct.qtree* %1279, i32 0, i32 0
  %1281 = load %struct.quad*, %struct.quad** %1280, align 8
  %1282 = getelementptr inbounds %struct.quad, %struct.quad* %1281, i32 0, i32 0
  %1283 = load float, float* %1282, align 8
  %1284 = fdiv float %1283, 2.000000e+00
  %1285 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1286 = getelementptr inbounds %struct.qtree, %struct.qtree* %1285, i32 0, i32 0
  %1287 = load %struct.quad*, %struct.quad** %1286, align 8
  %1288 = getelementptr inbounds %struct.quad, %struct.quad* %1287, i32 0, i32 2
  %1289 = load float, float* %1288, align 8
  %1290 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1291 = getelementptr inbounds %struct.qtree, %struct.qtree* %1290, i32 0, i32 0
  %1292 = load %struct.quad*, %struct.quad** %1291, align 8
  %1293 = getelementptr inbounds %struct.quad, %struct.quad* %1292, i32 0, i32 0
  %1294 = load float, float* %1293, align 8
  %1295 = fdiv float %1294, 2.000000e+00
  %1296 = fadd float %1289, %1295
  %1297 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1298 = getelementptr inbounds %struct.qtree, %struct.qtree* %1297, i32 0, i32 0
  %1299 = load %struct.quad*, %struct.quad** %1298, align 8
  %1300 = getelementptr inbounds %struct.quad, %struct.quad* %1299, i32 0, i32 1
  %1301 = load float, float* %1300, align 4
  %1302 = call %struct.qtree* @empty_qtree(float %1276, float %1277, float %1278, float %1284, float %1296, float %1301)
  store %struct.qtree* %1302, %struct.qtree** %36, align 8
  %1303 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1304 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1305 = getelementptr inbounds %struct.qtree, %struct.qtree* %1304, i32 0, i32 3
  store %struct.qtree* %1303, %struct.qtree** %1305, align 8
  br label %1379

1306:                                             ; preds = %1272
  %1307 = load float, float* %35, align 4
  %1308 = fcmp oeq float %1307, 2.000000e+00
  br i1 %1308, label %1309, label %1340

1309:                                             ; preds = %1306
  %1310 = load float, float* %32, align 4
  %1311 = load float, float* %33, align 4
  %1312 = load float, float* %34, align 4
  %1313 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1314 = getelementptr inbounds %struct.qtree, %struct.qtree* %1313, i32 0, i32 0
  %1315 = load %struct.quad*, %struct.quad** %1314, align 8
  %1316 = getelementptr inbounds %struct.quad, %struct.quad* %1315, i32 0, i32 0
  %1317 = load float, float* %1316, align 8
  %1318 = fdiv float %1317, 2.000000e+00
  %1319 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1320 = getelementptr inbounds %struct.qtree, %struct.qtree* %1319, i32 0, i32 0
  %1321 = load %struct.quad*, %struct.quad** %1320, align 8
  %1322 = getelementptr inbounds %struct.quad, %struct.quad* %1321, i32 0, i32 2
  %1323 = load float, float* %1322, align 8
  %1324 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1325 = getelementptr inbounds %struct.qtree, %struct.qtree* %1324, i32 0, i32 0
  %1326 = load %struct.quad*, %struct.quad** %1325, align 8
  %1327 = getelementptr inbounds %struct.quad, %struct.quad* %1326, i32 0, i32 1
  %1328 = load float, float* %1327, align 4
  %1329 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1330 = getelementptr inbounds %struct.qtree, %struct.qtree* %1329, i32 0, i32 0
  %1331 = load %struct.quad*, %struct.quad** %1330, align 8
  %1332 = getelementptr inbounds %struct.quad, %struct.quad* %1331, i32 0, i32 0
  %1333 = load float, float* %1332, align 8
  %1334 = fdiv float %1333, 2.000000e+00
  %1335 = fadd float %1328, %1334
  %1336 = call %struct.qtree* @empty_qtree(float %1310, float %1311, float %1312, float %1318, float %1323, float %1335)
  store %struct.qtree* %1336, %struct.qtree** %36, align 8
  %1337 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1338 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1339 = getelementptr inbounds %struct.qtree, %struct.qtree* %1338, i32 0, i32 2
  store %struct.qtree* %1337, %struct.qtree** %1339, align 8
  br label %1378

1340:                                             ; preds = %1306
  %1341 = load float, float* %32, align 4
  %1342 = load float, float* %33, align 4
  %1343 = load float, float* %34, align 4
  %1344 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1345 = getelementptr inbounds %struct.qtree, %struct.qtree* %1344, i32 0, i32 0
  %1346 = load %struct.quad*, %struct.quad** %1345, align 8
  %1347 = getelementptr inbounds %struct.quad, %struct.quad* %1346, i32 0, i32 0
  %1348 = load float, float* %1347, align 8
  %1349 = fdiv float %1348, 2.000000e+00
  %1350 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1351 = getelementptr inbounds %struct.qtree, %struct.qtree* %1350, i32 0, i32 0
  %1352 = load %struct.quad*, %struct.quad** %1351, align 8
  %1353 = getelementptr inbounds %struct.quad, %struct.quad* %1352, i32 0, i32 2
  %1354 = load float, float* %1353, align 8
  %1355 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1356 = getelementptr inbounds %struct.qtree, %struct.qtree* %1355, i32 0, i32 0
  %1357 = load %struct.quad*, %struct.quad** %1356, align 8
  %1358 = getelementptr inbounds %struct.quad, %struct.quad* %1357, i32 0, i32 0
  %1359 = load float, float* %1358, align 8
  %1360 = fdiv float %1359, 2.000000e+00
  %1361 = fadd float %1354, %1360
  %1362 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1363 = getelementptr inbounds %struct.qtree, %struct.qtree* %1362, i32 0, i32 0
  %1364 = load %struct.quad*, %struct.quad** %1363, align 8
  %1365 = getelementptr inbounds %struct.quad, %struct.quad* %1364, i32 0, i32 1
  %1366 = load float, float* %1365, align 4
  %1367 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1368 = getelementptr inbounds %struct.qtree, %struct.qtree* %1367, i32 0, i32 0
  %1369 = load %struct.quad*, %struct.quad** %1368, align 8
  %1370 = getelementptr inbounds %struct.quad, %struct.quad* %1369, i32 0, i32 0
  %1371 = load float, float* %1370, align 8
  %1372 = fdiv float %1371, 2.000000e+00
  %1373 = fadd float %1366, %1372
  %1374 = call %struct.qtree* @empty_qtree(float %1341, float %1342, float %1343, float %1349, float %1361, float %1373)
  store %struct.qtree* %1374, %struct.qtree** %36, align 8
  %1375 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1376 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1377 = getelementptr inbounds %struct.qtree, %struct.qtree* %1376, i32 0, i32 4
  store %struct.qtree* %1375, %struct.qtree** %1377, align 8
  br label %1378

1378:                                             ; preds = %1340, %1309
  br label %1379

1379:                                             ; preds = %1378, %1275
  br label %1380

1380:                                             ; preds = %1379, %1248
  br label %1381

1381:                                             ; preds = %1380, %1212, %1207, %1202, %1197
  %1382 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1383 = getelementptr inbounds %struct.qtree, %struct.qtree* %1382, i32 0, i32 0
  %1384 = load %struct.quad*, %struct.quad** %1383, align 8
  %1385 = getelementptr inbounds %struct.quad, %struct.quad* %1384, i32 0, i32 0
  %1386 = load float, float* %1385, align 8
  store float %1386, float* %37, align 4
  %1387 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1388 = getelementptr inbounds %struct.qtree, %struct.qtree* %1387, i32 0, i32 4
  %1389 = load %struct.qtree*, %struct.qtree** %1388, align 8
  %1390 = icmp eq %struct.qtree* %1389, null
  br i1 %1390, label %1391, label %1424

1391:                                             ; preds = %1381
  %1392 = load float, float* %5, align 4
  %1393 = load float, float* %6, align 4
  %1394 = load float, float* %8, align 4
  %1395 = load float, float* %37, align 4
  %1396 = fpext float %1395 to double
  %1397 = fdiv double %1396, 2.000000e+00
  %1398 = fptrunc double %1397 to float
  %1399 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1400 = getelementptr inbounds %struct.qtree, %struct.qtree* %1399, i32 0, i32 0
  %1401 = load %struct.quad*, %struct.quad** %1400, align 8
  %1402 = getelementptr inbounds %struct.quad, %struct.quad* %1401, i32 0, i32 2
  %1403 = load float, float* %1402, align 8
  %1404 = fpext float %1403 to double
  %1405 = load float, float* %37, align 4
  %1406 = fpext float %1405 to double
  %1407 = fdiv double %1406, 2.000000e+00
  %1408 = fadd double %1404, %1407
  %1409 = fptrunc double %1408 to float
  %1410 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1411 = getelementptr inbounds %struct.qtree, %struct.qtree* %1410, i32 0, i32 0
  %1412 = load %struct.quad*, %struct.quad** %1411, align 8
  %1413 = getelementptr inbounds %struct.quad, %struct.quad* %1412, i32 0, i32 1
  %1414 = load float, float* %1413, align 4
  %1415 = fpext float %1414 to double
  %1416 = load float, float* %37, align 4
  %1417 = fpext float %1416 to double
  %1418 = fdiv double %1417, 2.000000e+00
  %1419 = fadd double %1415, %1418
  %1420 = fptrunc double %1419 to float
  %1421 = call %struct.qtree* @empty_qtree(float %1392, float %1393, float %1394, float %1398, float %1409, float %1420)
  %1422 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1423 = getelementptr inbounds %struct.qtree, %struct.qtree* %1422, i32 0, i32 4
  store %struct.qtree* %1421, %struct.qtree** %1423, align 8
  br label %1432

1424:                                             ; preds = %1381
  %1425 = load float, float* %5, align 4
  %1426 = load float, float* %6, align 4
  %1427 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1428 = getelementptr inbounds %struct.qtree, %struct.qtree* %1427, i32 0, i32 4
  %1429 = load %struct.qtree*, %struct.qtree** %1428, align 8
  %1430 = load float, float* %8, align 4
  %1431 = call %struct.qtree* @insertPoint(float %1425, float %1426, %struct.qtree* %1429, float %1430)
  br label %1432

1432:                                             ; preds = %1424, %1391
  %1433 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1434 = getelementptr inbounds %struct.qtree, %struct.qtree* %1433, i32 0, i32 1
  %1435 = load %struct.qtree*, %struct.qtree** %1434, align 8
  %1436 = icmp ne %struct.qtree* %1435, null
  br i1 %1436, label %1437, label %1483

1437:                                             ; preds = %1432
  %1438 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1439 = getelementptr inbounds %struct.qtree, %struct.qtree* %1438, i32 0, i32 1
  %1440 = load %struct.qtree*, %struct.qtree** %1439, align 8
  %1441 = getelementptr inbounds %struct.qtree, %struct.qtree* %1440, i32 0, i32 0
  %1442 = load %struct.quad*, %struct.quad** %1441, align 8
  %1443 = getelementptr inbounds %struct.quad, %struct.quad* %1442, i32 0, i32 3
  %1444 = load %struct.centroid*, %struct.centroid** %1443, align 8
  %1445 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1446 = getelementptr inbounds %struct.qtree, %struct.qtree* %1445, i32 0, i32 4
  %1447 = load %struct.qtree*, %struct.qtree** %1446, align 8
  %1448 = getelementptr inbounds %struct.qtree, %struct.qtree* %1447, i32 0, i32 0
  %1449 = load %struct.quad*, %struct.quad** %1448, align 8
  %1450 = getelementptr inbounds %struct.quad, %struct.quad* %1449, i32 0, i32 3
  %1451 = load %struct.centroid*, %struct.centroid** %1450, align 8
  %1452 = call %struct.centroid* @centroid_sum(%struct.centroid* %1444, %struct.centroid* %1451)
  store %struct.centroid* %1452, %struct.centroid** %38, align 8
  %1453 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1454 = getelementptr inbounds %struct.qtree, %struct.qtree* %1453, i32 0, i32 2
  %1455 = load %struct.qtree*, %struct.qtree** %1454, align 8
  %1456 = icmp ne %struct.qtree* %1455, null
  br i1 %1456, label %1457, label %1467

1457:                                             ; preds = %1437
  %1458 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1459 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1460 = getelementptr inbounds %struct.qtree, %struct.qtree* %1459, i32 0, i32 2
  %1461 = load %struct.qtree*, %struct.qtree** %1460, align 8
  %1462 = getelementptr inbounds %struct.qtree, %struct.qtree* %1461, i32 0, i32 0
  %1463 = load %struct.quad*, %struct.quad** %1462, align 8
  %1464 = getelementptr inbounds %struct.quad, %struct.quad* %1463, i32 0, i32 3
  %1465 = load %struct.centroid*, %struct.centroid** %1464, align 8
  %1466 = call %struct.centroid* @centroid_sum(%struct.centroid* %1458, %struct.centroid* %1465)
  store %struct.centroid* %1466, %struct.centroid** %38, align 8
  br label %1467

1467:                                             ; preds = %1457, %1437
  %1468 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1469 = getelementptr inbounds %struct.qtree, %struct.qtree* %1468, i32 0, i32 3
  %1470 = load %struct.qtree*, %struct.qtree** %1469, align 8
  %1471 = icmp ne %struct.qtree* %1470, null
  br i1 %1471, label %1472, label %1482

1472:                                             ; preds = %1467
  %1473 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1474 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1475 = getelementptr inbounds %struct.qtree, %struct.qtree* %1474, i32 0, i32 3
  %1476 = load %struct.qtree*, %struct.qtree** %1475, align 8
  %1477 = getelementptr inbounds %struct.qtree, %struct.qtree* %1476, i32 0, i32 0
  %1478 = load %struct.quad*, %struct.quad** %1477, align 8
  %1479 = getelementptr inbounds %struct.quad, %struct.quad* %1478, i32 0, i32 3
  %1480 = load %struct.centroid*, %struct.centroid** %1479, align 8
  %1481 = call %struct.centroid* @centroid_sum(%struct.centroid* %1473, %struct.centroid* %1480)
  store %struct.centroid* %1481, %struct.centroid** %38, align 8
  br label %1482

1482:                                             ; preds = %1472, %1467
  br label %1550

1483:                                             ; preds = %1432
  %1484 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1485 = getelementptr inbounds %struct.qtree, %struct.qtree* %1484, i32 0, i32 2
  %1486 = load %struct.qtree*, %struct.qtree** %1485, align 8
  %1487 = icmp ne %struct.qtree* %1486, null
  br i1 %1487, label %1488, label %1519

1488:                                             ; preds = %1483
  %1489 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1490 = getelementptr inbounds %struct.qtree, %struct.qtree* %1489, i32 0, i32 2
  %1491 = load %struct.qtree*, %struct.qtree** %1490, align 8
  %1492 = getelementptr inbounds %struct.qtree, %struct.qtree* %1491, i32 0, i32 0
  %1493 = load %struct.quad*, %struct.quad** %1492, align 8
  %1494 = getelementptr inbounds %struct.quad, %struct.quad* %1493, i32 0, i32 3
  %1495 = load %struct.centroid*, %struct.centroid** %1494, align 8
  %1496 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1497 = getelementptr inbounds %struct.qtree, %struct.qtree* %1496, i32 0, i32 4
  %1498 = load %struct.qtree*, %struct.qtree** %1497, align 8
  %1499 = getelementptr inbounds %struct.qtree, %struct.qtree* %1498, i32 0, i32 0
  %1500 = load %struct.quad*, %struct.quad** %1499, align 8
  %1501 = getelementptr inbounds %struct.quad, %struct.quad* %1500, i32 0, i32 3
  %1502 = load %struct.centroid*, %struct.centroid** %1501, align 8
  %1503 = call %struct.centroid* @centroid_sum(%struct.centroid* %1495, %struct.centroid* %1502)
  store %struct.centroid* %1503, %struct.centroid** %38, align 8
  %1504 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1505 = getelementptr inbounds %struct.qtree, %struct.qtree* %1504, i32 0, i32 3
  %1506 = load %struct.qtree*, %struct.qtree** %1505, align 8
  %1507 = icmp ne %struct.qtree* %1506, null
  br i1 %1507, label %1508, label %1518

1508:                                             ; preds = %1488
  %1509 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1510 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1511 = getelementptr inbounds %struct.qtree, %struct.qtree* %1510, i32 0, i32 3
  %1512 = load %struct.qtree*, %struct.qtree** %1511, align 8
  %1513 = getelementptr inbounds %struct.qtree, %struct.qtree* %1512, i32 0, i32 0
  %1514 = load %struct.quad*, %struct.quad** %1513, align 8
  %1515 = getelementptr inbounds %struct.quad, %struct.quad* %1514, i32 0, i32 3
  %1516 = load %struct.centroid*, %struct.centroid** %1515, align 8
  %1517 = call %struct.centroid* @centroid_sum(%struct.centroid* %1509, %struct.centroid* %1516)
  store %struct.centroid* %1517, %struct.centroid** %38, align 8
  br label %1518

1518:                                             ; preds = %1508, %1488
  br label %1549

1519:                                             ; preds = %1483
  %1520 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1521 = getelementptr inbounds %struct.qtree, %struct.qtree* %1520, i32 0, i32 3
  %1522 = load %struct.qtree*, %struct.qtree** %1521, align 8
  %1523 = icmp ne %struct.qtree* %1522, null
  br i1 %1523, label %1524, label %1540

1524:                                             ; preds = %1519
  %1525 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1526 = getelementptr inbounds %struct.qtree, %struct.qtree* %1525, i32 0, i32 3
  %1527 = load %struct.qtree*, %struct.qtree** %1526, align 8
  %1528 = getelementptr inbounds %struct.qtree, %struct.qtree* %1527, i32 0, i32 0
  %1529 = load %struct.quad*, %struct.quad** %1528, align 8
  %1530 = getelementptr inbounds %struct.quad, %struct.quad* %1529, i32 0, i32 3
  %1531 = load %struct.centroid*, %struct.centroid** %1530, align 8
  %1532 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1533 = getelementptr inbounds %struct.qtree, %struct.qtree* %1532, i32 0, i32 4
  %1534 = load %struct.qtree*, %struct.qtree** %1533, align 8
  %1535 = getelementptr inbounds %struct.qtree, %struct.qtree* %1534, i32 0, i32 0
  %1536 = load %struct.quad*, %struct.quad** %1535, align 8
  %1537 = getelementptr inbounds %struct.quad, %struct.quad* %1536, i32 0, i32 3
  %1538 = load %struct.centroid*, %struct.centroid** %1537, align 8
  %1539 = call %struct.centroid* @centroid_sum(%struct.centroid* %1531, %struct.centroid* %1538)
  store %struct.centroid* %1539, %struct.centroid** %38, align 8
  br label %1548

1540:                                             ; preds = %1519
  %1541 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1542 = getelementptr inbounds %struct.qtree, %struct.qtree* %1541, i32 0, i32 4
  %1543 = load %struct.qtree*, %struct.qtree** %1542, align 8
  %1544 = getelementptr inbounds %struct.qtree, %struct.qtree* %1543, i32 0, i32 0
  %1545 = load %struct.quad*, %struct.quad** %1544, align 8
  %1546 = getelementptr inbounds %struct.quad, %struct.quad* %1545, i32 0, i32 3
  %1547 = load %struct.centroid*, %struct.centroid** %1546, align 8
  store %struct.centroid* %1547, %struct.centroid** %38, align 8
  br label %1548

1548:                                             ; preds = %1540, %1524
  br label %1549

1549:                                             ; preds = %1548, %1518
  br label %1550

1550:                                             ; preds = %1549, %1482
  %1551 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1552 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1553 = getelementptr inbounds %struct.qtree, %struct.qtree* %1552, i32 0, i32 0
  %1554 = load %struct.quad*, %struct.quad** %1553, align 8
  %1555 = getelementptr inbounds %struct.quad, %struct.quad* %1554, i32 0, i32 3
  store %struct.centroid* %1551, %struct.centroid** %1555, align 8
  br label %2124

1556:                                             ; preds = %1192, %1184
  %1557 = load float, float* %5, align 4
  %1558 = load float, float* %6, align 4
  %1559 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1560 = getelementptr inbounds %struct.qtree, %struct.qtree* %1559, i32 0, i32 0
  %1561 = load %struct.quad*, %struct.quad** %1560, align 8
  %1562 = call i32 @which_quad(float %1557, float %1558, %struct.quad* %1561)
  %1563 = icmp eq i32 %1562, 1
  br i1 %1563, label %1564, label %1697

1564:                                             ; preds = %1556
  %1565 = load float, float* %5, align 4
  %1566 = load float, float* %6, align 4
  %1567 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1568 = getelementptr inbounds %struct.qtree, %struct.qtree* %1567, i32 0, i32 1
  %1569 = load %struct.qtree*, %struct.qtree** %1568, align 8
  %1570 = load float, float* %8, align 4
  %1571 = call %struct.qtree* @insertPoint(float %1565, float %1566, %struct.qtree* %1569, float %1570)
  %1572 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1573 = getelementptr inbounds %struct.qtree, %struct.qtree* %1572, i32 0, i32 1
  store %struct.qtree* %1571, %struct.qtree** %1573, align 8
  %1574 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1575 = getelementptr inbounds %struct.qtree, %struct.qtree* %1574, i32 0, i32 2
  %1576 = load %struct.qtree*, %struct.qtree** %1575, align 8
  %1577 = icmp ne %struct.qtree* %1576, null
  br i1 %1577, label %1578, label %1624

1578:                                             ; preds = %1564
  %1579 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1580 = getelementptr inbounds %struct.qtree, %struct.qtree* %1579, i32 0, i32 1
  %1581 = load %struct.qtree*, %struct.qtree** %1580, align 8
  %1582 = getelementptr inbounds %struct.qtree, %struct.qtree* %1581, i32 0, i32 0
  %1583 = load %struct.quad*, %struct.quad** %1582, align 8
  %1584 = getelementptr inbounds %struct.quad, %struct.quad* %1583, i32 0, i32 3
  %1585 = load %struct.centroid*, %struct.centroid** %1584, align 8
  %1586 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1587 = getelementptr inbounds %struct.qtree, %struct.qtree* %1586, i32 0, i32 2
  %1588 = load %struct.qtree*, %struct.qtree** %1587, align 8
  %1589 = getelementptr inbounds %struct.qtree, %struct.qtree* %1588, i32 0, i32 0
  %1590 = load %struct.quad*, %struct.quad** %1589, align 8
  %1591 = getelementptr inbounds %struct.quad, %struct.quad* %1590, i32 0, i32 3
  %1592 = load %struct.centroid*, %struct.centroid** %1591, align 8
  %1593 = call %struct.centroid* @centroid_sum(%struct.centroid* %1585, %struct.centroid* %1592)
  store %struct.centroid* %1593, %struct.centroid** %39, align 8
  %1594 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1595 = getelementptr inbounds %struct.qtree, %struct.qtree* %1594, i32 0, i32 4
  %1596 = load %struct.qtree*, %struct.qtree** %1595, align 8
  %1597 = icmp ne %struct.qtree* %1596, null
  br i1 %1597, label %1598, label %1608

1598:                                             ; preds = %1578
  %1599 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1600 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1601 = getelementptr inbounds %struct.qtree, %struct.qtree* %1600, i32 0, i32 4
  %1602 = load %struct.qtree*, %struct.qtree** %1601, align 8
  %1603 = getelementptr inbounds %struct.qtree, %struct.qtree* %1602, i32 0, i32 0
  %1604 = load %struct.quad*, %struct.quad** %1603, align 8
  %1605 = getelementptr inbounds %struct.quad, %struct.quad* %1604, i32 0, i32 3
  %1606 = load %struct.centroid*, %struct.centroid** %1605, align 8
  %1607 = call %struct.centroid* @centroid_sum(%struct.centroid* %1599, %struct.centroid* %1606)
  store %struct.centroid* %1607, %struct.centroid** %39, align 8
  br label %1608

1608:                                             ; preds = %1598, %1578
  %1609 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1610 = getelementptr inbounds %struct.qtree, %struct.qtree* %1609, i32 0, i32 3
  %1611 = load %struct.qtree*, %struct.qtree** %1610, align 8
  %1612 = icmp ne %struct.qtree* %1611, null
  br i1 %1612, label %1613, label %1623

1613:                                             ; preds = %1608
  %1614 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1615 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1616 = getelementptr inbounds %struct.qtree, %struct.qtree* %1615, i32 0, i32 3
  %1617 = load %struct.qtree*, %struct.qtree** %1616, align 8
  %1618 = getelementptr inbounds %struct.qtree, %struct.qtree* %1617, i32 0, i32 0
  %1619 = load %struct.quad*, %struct.quad** %1618, align 8
  %1620 = getelementptr inbounds %struct.quad, %struct.quad* %1619, i32 0, i32 3
  %1621 = load %struct.centroid*, %struct.centroid** %1620, align 8
  %1622 = call %struct.centroid* @centroid_sum(%struct.centroid* %1614, %struct.centroid* %1621)
  store %struct.centroid* %1622, %struct.centroid** %39, align 8
  br label %1623

1623:                                             ; preds = %1613, %1608
  br label %1691

1624:                                             ; preds = %1564
  %1625 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1626 = getelementptr inbounds %struct.qtree, %struct.qtree* %1625, i32 0, i32 3
  %1627 = load %struct.qtree*, %struct.qtree** %1626, align 8
  %1628 = icmp ne %struct.qtree* %1627, null
  br i1 %1628, label %1629, label %1660

1629:                                             ; preds = %1624
  %1630 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1631 = getelementptr inbounds %struct.qtree, %struct.qtree* %1630, i32 0, i32 1
  %1632 = load %struct.qtree*, %struct.qtree** %1631, align 8
  %1633 = getelementptr inbounds %struct.qtree, %struct.qtree* %1632, i32 0, i32 0
  %1634 = load %struct.quad*, %struct.quad** %1633, align 8
  %1635 = getelementptr inbounds %struct.quad, %struct.quad* %1634, i32 0, i32 3
  %1636 = load %struct.centroid*, %struct.centroid** %1635, align 8
  %1637 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1638 = getelementptr inbounds %struct.qtree, %struct.qtree* %1637, i32 0, i32 3
  %1639 = load %struct.qtree*, %struct.qtree** %1638, align 8
  %1640 = getelementptr inbounds %struct.qtree, %struct.qtree* %1639, i32 0, i32 0
  %1641 = load %struct.quad*, %struct.quad** %1640, align 8
  %1642 = getelementptr inbounds %struct.quad, %struct.quad* %1641, i32 0, i32 3
  %1643 = load %struct.centroid*, %struct.centroid** %1642, align 8
  %1644 = call %struct.centroid* @centroid_sum(%struct.centroid* %1636, %struct.centroid* %1643)
  store %struct.centroid* %1644, %struct.centroid** %39, align 8
  %1645 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1646 = getelementptr inbounds %struct.qtree, %struct.qtree* %1645, i32 0, i32 4
  %1647 = load %struct.qtree*, %struct.qtree** %1646, align 8
  %1648 = icmp ne %struct.qtree* %1647, null
  br i1 %1648, label %1649, label %1659

1649:                                             ; preds = %1629
  %1650 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1651 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1652 = getelementptr inbounds %struct.qtree, %struct.qtree* %1651, i32 0, i32 4
  %1653 = load %struct.qtree*, %struct.qtree** %1652, align 8
  %1654 = getelementptr inbounds %struct.qtree, %struct.qtree* %1653, i32 0, i32 0
  %1655 = load %struct.quad*, %struct.quad** %1654, align 8
  %1656 = getelementptr inbounds %struct.quad, %struct.quad* %1655, i32 0, i32 3
  %1657 = load %struct.centroid*, %struct.centroid** %1656, align 8
  %1658 = call %struct.centroid* @centroid_sum(%struct.centroid* %1650, %struct.centroid* %1657)
  store %struct.centroid* %1658, %struct.centroid** %39, align 8
  br label %1659

1659:                                             ; preds = %1649, %1629
  br label %1690

1660:                                             ; preds = %1624
  %1661 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1662 = getelementptr inbounds %struct.qtree, %struct.qtree* %1661, i32 0, i32 4
  %1663 = load %struct.qtree*, %struct.qtree** %1662, align 8
  %1664 = icmp ne %struct.qtree* %1663, null
  br i1 %1664, label %1665, label %1681

1665:                                             ; preds = %1660
  %1666 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1667 = getelementptr inbounds %struct.qtree, %struct.qtree* %1666, i32 0, i32 1
  %1668 = load %struct.qtree*, %struct.qtree** %1667, align 8
  %1669 = getelementptr inbounds %struct.qtree, %struct.qtree* %1668, i32 0, i32 0
  %1670 = load %struct.quad*, %struct.quad** %1669, align 8
  %1671 = getelementptr inbounds %struct.quad, %struct.quad* %1670, i32 0, i32 3
  %1672 = load %struct.centroid*, %struct.centroid** %1671, align 8
  %1673 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1674 = getelementptr inbounds %struct.qtree, %struct.qtree* %1673, i32 0, i32 4
  %1675 = load %struct.qtree*, %struct.qtree** %1674, align 8
  %1676 = getelementptr inbounds %struct.qtree, %struct.qtree* %1675, i32 0, i32 0
  %1677 = load %struct.quad*, %struct.quad** %1676, align 8
  %1678 = getelementptr inbounds %struct.quad, %struct.quad* %1677, i32 0, i32 3
  %1679 = load %struct.centroid*, %struct.centroid** %1678, align 8
  %1680 = call %struct.centroid* @centroid_sum(%struct.centroid* %1672, %struct.centroid* %1679)
  store %struct.centroid* %1680, %struct.centroid** %39, align 8
  br label %1689

1681:                                             ; preds = %1660
  %1682 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1683 = getelementptr inbounds %struct.qtree, %struct.qtree* %1682, i32 0, i32 1
  %1684 = load %struct.qtree*, %struct.qtree** %1683, align 8
  %1685 = getelementptr inbounds %struct.qtree, %struct.qtree* %1684, i32 0, i32 0
  %1686 = load %struct.quad*, %struct.quad** %1685, align 8
  %1687 = getelementptr inbounds %struct.quad, %struct.quad* %1686, i32 0, i32 3
  %1688 = load %struct.centroid*, %struct.centroid** %1687, align 8
  store %struct.centroid* %1688, %struct.centroid** %39, align 8
  br label %1689

1689:                                             ; preds = %1681, %1665
  br label %1690

1690:                                             ; preds = %1689, %1659
  br label %1691

1691:                                             ; preds = %1690, %1623
  %1692 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1693 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1694 = getelementptr inbounds %struct.qtree, %struct.qtree* %1693, i32 0, i32 0
  %1695 = load %struct.quad*, %struct.quad** %1694, align 8
  %1696 = getelementptr inbounds %struct.quad, %struct.quad* %1695, i32 0, i32 3
  store %struct.centroid* %1692, %struct.centroid** %1696, align 8
  br label %2123

1697:                                             ; preds = %1556
  %1698 = load float, float* %5, align 4
  %1699 = load float, float* %6, align 4
  %1700 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1701 = getelementptr inbounds %struct.qtree, %struct.qtree* %1700, i32 0, i32 0
  %1702 = load %struct.quad*, %struct.quad** %1701, align 8
  %1703 = call i32 @which_quad(float %1698, float %1699, %struct.quad* %1702)
  %1704 = icmp eq i32 %1703, 2
  br i1 %1704, label %1705, label %1838

1705:                                             ; preds = %1697
  %1706 = load float, float* %5, align 4
  %1707 = load float, float* %6, align 4
  %1708 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1709 = getelementptr inbounds %struct.qtree, %struct.qtree* %1708, i32 0, i32 2
  %1710 = load %struct.qtree*, %struct.qtree** %1709, align 8
  %1711 = load float, float* %8, align 4
  %1712 = call %struct.qtree* @insertPoint(float %1706, float %1707, %struct.qtree* %1710, float %1711)
  %1713 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1714 = getelementptr inbounds %struct.qtree, %struct.qtree* %1713, i32 0, i32 2
  store %struct.qtree* %1712, %struct.qtree** %1714, align 8
  %1715 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1716 = getelementptr inbounds %struct.qtree, %struct.qtree* %1715, i32 0, i32 1
  %1717 = load %struct.qtree*, %struct.qtree** %1716, align 8
  %1718 = icmp ne %struct.qtree* %1717, null
  br i1 %1718, label %1719, label %1765

1719:                                             ; preds = %1705
  %1720 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1721 = getelementptr inbounds %struct.qtree, %struct.qtree* %1720, i32 0, i32 1
  %1722 = load %struct.qtree*, %struct.qtree** %1721, align 8
  %1723 = getelementptr inbounds %struct.qtree, %struct.qtree* %1722, i32 0, i32 0
  %1724 = load %struct.quad*, %struct.quad** %1723, align 8
  %1725 = getelementptr inbounds %struct.quad, %struct.quad* %1724, i32 0, i32 3
  %1726 = load %struct.centroid*, %struct.centroid** %1725, align 8
  %1727 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1728 = getelementptr inbounds %struct.qtree, %struct.qtree* %1727, i32 0, i32 2
  %1729 = load %struct.qtree*, %struct.qtree** %1728, align 8
  %1730 = getelementptr inbounds %struct.qtree, %struct.qtree* %1729, i32 0, i32 0
  %1731 = load %struct.quad*, %struct.quad** %1730, align 8
  %1732 = getelementptr inbounds %struct.quad, %struct.quad* %1731, i32 0, i32 3
  %1733 = load %struct.centroid*, %struct.centroid** %1732, align 8
  %1734 = call %struct.centroid* @centroid_sum(%struct.centroid* %1726, %struct.centroid* %1733)
  store %struct.centroid* %1734, %struct.centroid** %40, align 8
  %1735 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1736 = getelementptr inbounds %struct.qtree, %struct.qtree* %1735, i32 0, i32 4
  %1737 = load %struct.qtree*, %struct.qtree** %1736, align 8
  %1738 = icmp ne %struct.qtree* %1737, null
  br i1 %1738, label %1739, label %1749

1739:                                             ; preds = %1719
  %1740 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1741 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1742 = getelementptr inbounds %struct.qtree, %struct.qtree* %1741, i32 0, i32 4
  %1743 = load %struct.qtree*, %struct.qtree** %1742, align 8
  %1744 = getelementptr inbounds %struct.qtree, %struct.qtree* %1743, i32 0, i32 0
  %1745 = load %struct.quad*, %struct.quad** %1744, align 8
  %1746 = getelementptr inbounds %struct.quad, %struct.quad* %1745, i32 0, i32 3
  %1747 = load %struct.centroid*, %struct.centroid** %1746, align 8
  %1748 = call %struct.centroid* @centroid_sum(%struct.centroid* %1740, %struct.centroid* %1747)
  store %struct.centroid* %1748, %struct.centroid** %40, align 8
  br label %1749

1749:                                             ; preds = %1739, %1719
  %1750 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1751 = getelementptr inbounds %struct.qtree, %struct.qtree* %1750, i32 0, i32 3
  %1752 = load %struct.qtree*, %struct.qtree** %1751, align 8
  %1753 = icmp ne %struct.qtree* %1752, null
  br i1 %1753, label %1754, label %1764

1754:                                             ; preds = %1749
  %1755 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1756 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1757 = getelementptr inbounds %struct.qtree, %struct.qtree* %1756, i32 0, i32 3
  %1758 = load %struct.qtree*, %struct.qtree** %1757, align 8
  %1759 = getelementptr inbounds %struct.qtree, %struct.qtree* %1758, i32 0, i32 0
  %1760 = load %struct.quad*, %struct.quad** %1759, align 8
  %1761 = getelementptr inbounds %struct.quad, %struct.quad* %1760, i32 0, i32 3
  %1762 = load %struct.centroid*, %struct.centroid** %1761, align 8
  %1763 = call %struct.centroid* @centroid_sum(%struct.centroid* %1755, %struct.centroid* %1762)
  store %struct.centroid* %1763, %struct.centroid** %40, align 8
  br label %1764

1764:                                             ; preds = %1754, %1749
  br label %1832

1765:                                             ; preds = %1705
  %1766 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1767 = getelementptr inbounds %struct.qtree, %struct.qtree* %1766, i32 0, i32 4
  %1768 = load %struct.qtree*, %struct.qtree** %1767, align 8
  %1769 = icmp ne %struct.qtree* %1768, null
  br i1 %1769, label %1770, label %1801

1770:                                             ; preds = %1765
  %1771 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1772 = getelementptr inbounds %struct.qtree, %struct.qtree* %1771, i32 0, i32 2
  %1773 = load %struct.qtree*, %struct.qtree** %1772, align 8
  %1774 = getelementptr inbounds %struct.qtree, %struct.qtree* %1773, i32 0, i32 0
  %1775 = load %struct.quad*, %struct.quad** %1774, align 8
  %1776 = getelementptr inbounds %struct.quad, %struct.quad* %1775, i32 0, i32 3
  %1777 = load %struct.centroid*, %struct.centroid** %1776, align 8
  %1778 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1779 = getelementptr inbounds %struct.qtree, %struct.qtree* %1778, i32 0, i32 4
  %1780 = load %struct.qtree*, %struct.qtree** %1779, align 8
  %1781 = getelementptr inbounds %struct.qtree, %struct.qtree* %1780, i32 0, i32 0
  %1782 = load %struct.quad*, %struct.quad** %1781, align 8
  %1783 = getelementptr inbounds %struct.quad, %struct.quad* %1782, i32 0, i32 3
  %1784 = load %struct.centroid*, %struct.centroid** %1783, align 8
  %1785 = call %struct.centroid* @centroid_sum(%struct.centroid* %1777, %struct.centroid* %1784)
  store %struct.centroid* %1785, %struct.centroid** %40, align 8
  %1786 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1787 = getelementptr inbounds %struct.qtree, %struct.qtree* %1786, i32 0, i32 3
  %1788 = load %struct.qtree*, %struct.qtree** %1787, align 8
  %1789 = icmp ne %struct.qtree* %1788, null
  br i1 %1789, label %1790, label %1800

1790:                                             ; preds = %1770
  %1791 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1792 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1793 = getelementptr inbounds %struct.qtree, %struct.qtree* %1792, i32 0, i32 3
  %1794 = load %struct.qtree*, %struct.qtree** %1793, align 8
  %1795 = getelementptr inbounds %struct.qtree, %struct.qtree* %1794, i32 0, i32 0
  %1796 = load %struct.quad*, %struct.quad** %1795, align 8
  %1797 = getelementptr inbounds %struct.quad, %struct.quad* %1796, i32 0, i32 3
  %1798 = load %struct.centroid*, %struct.centroid** %1797, align 8
  %1799 = call %struct.centroid* @centroid_sum(%struct.centroid* %1791, %struct.centroid* %1798)
  store %struct.centroid* %1799, %struct.centroid** %40, align 8
  br label %1800

1800:                                             ; preds = %1790, %1770
  br label %1831

1801:                                             ; preds = %1765
  %1802 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1803 = getelementptr inbounds %struct.qtree, %struct.qtree* %1802, i32 0, i32 3
  %1804 = load %struct.qtree*, %struct.qtree** %1803, align 8
  %1805 = icmp ne %struct.qtree* %1804, null
  br i1 %1805, label %1806, label %1822

1806:                                             ; preds = %1801
  %1807 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1808 = getelementptr inbounds %struct.qtree, %struct.qtree* %1807, i32 0, i32 2
  %1809 = load %struct.qtree*, %struct.qtree** %1808, align 8
  %1810 = getelementptr inbounds %struct.qtree, %struct.qtree* %1809, i32 0, i32 0
  %1811 = load %struct.quad*, %struct.quad** %1810, align 8
  %1812 = getelementptr inbounds %struct.quad, %struct.quad* %1811, i32 0, i32 3
  %1813 = load %struct.centroid*, %struct.centroid** %1812, align 8
  %1814 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1815 = getelementptr inbounds %struct.qtree, %struct.qtree* %1814, i32 0, i32 3
  %1816 = load %struct.qtree*, %struct.qtree** %1815, align 8
  %1817 = getelementptr inbounds %struct.qtree, %struct.qtree* %1816, i32 0, i32 0
  %1818 = load %struct.quad*, %struct.quad** %1817, align 8
  %1819 = getelementptr inbounds %struct.quad, %struct.quad* %1818, i32 0, i32 3
  %1820 = load %struct.centroid*, %struct.centroid** %1819, align 8
  %1821 = call %struct.centroid* @centroid_sum(%struct.centroid* %1813, %struct.centroid* %1820)
  store %struct.centroid* %1821, %struct.centroid** %40, align 8
  br label %1830

1822:                                             ; preds = %1801
  %1823 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1824 = getelementptr inbounds %struct.qtree, %struct.qtree* %1823, i32 0, i32 2
  %1825 = load %struct.qtree*, %struct.qtree** %1824, align 8
  %1826 = getelementptr inbounds %struct.qtree, %struct.qtree* %1825, i32 0, i32 0
  %1827 = load %struct.quad*, %struct.quad** %1826, align 8
  %1828 = getelementptr inbounds %struct.quad, %struct.quad* %1827, i32 0, i32 3
  %1829 = load %struct.centroid*, %struct.centroid** %1828, align 8
  store %struct.centroid* %1829, %struct.centroid** %40, align 8
  br label %1830

1830:                                             ; preds = %1822, %1806
  br label %1831

1831:                                             ; preds = %1830, %1800
  br label %1832

1832:                                             ; preds = %1831, %1764
  %1833 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1834 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1835 = getelementptr inbounds %struct.qtree, %struct.qtree* %1834, i32 0, i32 0
  %1836 = load %struct.quad*, %struct.quad** %1835, align 8
  %1837 = getelementptr inbounds %struct.quad, %struct.quad* %1836, i32 0, i32 3
  store %struct.centroid* %1833, %struct.centroid** %1837, align 8
  br label %2122

1838:                                             ; preds = %1697
  %1839 = load float, float* %5, align 4
  %1840 = load float, float* %6, align 4
  %1841 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1842 = getelementptr inbounds %struct.qtree, %struct.qtree* %1841, i32 0, i32 0
  %1843 = load %struct.quad*, %struct.quad** %1842, align 8
  %1844 = call i32 @which_quad(float %1839, float %1840, %struct.quad* %1843)
  %1845 = icmp eq i32 %1844, 3
  br i1 %1845, label %1846, label %1979

1846:                                             ; preds = %1838
  %1847 = load float, float* %5, align 4
  %1848 = load float, float* %6, align 4
  %1849 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1850 = getelementptr inbounds %struct.qtree, %struct.qtree* %1849, i32 0, i32 3
  %1851 = load %struct.qtree*, %struct.qtree** %1850, align 8
  %1852 = load float, float* %8, align 4
  %1853 = call %struct.qtree* @insertPoint(float %1847, float %1848, %struct.qtree* %1851, float %1852)
  %1854 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1855 = getelementptr inbounds %struct.qtree, %struct.qtree* %1854, i32 0, i32 3
  store %struct.qtree* %1853, %struct.qtree** %1855, align 8
  %1856 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1857 = getelementptr inbounds %struct.qtree, %struct.qtree* %1856, i32 0, i32 1
  %1858 = load %struct.qtree*, %struct.qtree** %1857, align 8
  %1859 = icmp ne %struct.qtree* %1858, null
  br i1 %1859, label %1860, label %1906

1860:                                             ; preds = %1846
  %1861 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1862 = getelementptr inbounds %struct.qtree, %struct.qtree* %1861, i32 0, i32 1
  %1863 = load %struct.qtree*, %struct.qtree** %1862, align 8
  %1864 = getelementptr inbounds %struct.qtree, %struct.qtree* %1863, i32 0, i32 0
  %1865 = load %struct.quad*, %struct.quad** %1864, align 8
  %1866 = getelementptr inbounds %struct.quad, %struct.quad* %1865, i32 0, i32 3
  %1867 = load %struct.centroid*, %struct.centroid** %1866, align 8
  %1868 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1869 = getelementptr inbounds %struct.qtree, %struct.qtree* %1868, i32 0, i32 3
  %1870 = load %struct.qtree*, %struct.qtree** %1869, align 8
  %1871 = getelementptr inbounds %struct.qtree, %struct.qtree* %1870, i32 0, i32 0
  %1872 = load %struct.quad*, %struct.quad** %1871, align 8
  %1873 = getelementptr inbounds %struct.quad, %struct.quad* %1872, i32 0, i32 3
  %1874 = load %struct.centroid*, %struct.centroid** %1873, align 8
  %1875 = call %struct.centroid* @centroid_sum(%struct.centroid* %1867, %struct.centroid* %1874)
  store %struct.centroid* %1875, %struct.centroid** %41, align 8
  %1876 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1877 = getelementptr inbounds %struct.qtree, %struct.qtree* %1876, i32 0, i32 2
  %1878 = load %struct.qtree*, %struct.qtree** %1877, align 8
  %1879 = icmp ne %struct.qtree* %1878, null
  br i1 %1879, label %1880, label %1890

1880:                                             ; preds = %1860
  %1881 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1882 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1883 = getelementptr inbounds %struct.qtree, %struct.qtree* %1882, i32 0, i32 2
  %1884 = load %struct.qtree*, %struct.qtree** %1883, align 8
  %1885 = getelementptr inbounds %struct.qtree, %struct.qtree* %1884, i32 0, i32 0
  %1886 = load %struct.quad*, %struct.quad** %1885, align 8
  %1887 = getelementptr inbounds %struct.quad, %struct.quad* %1886, i32 0, i32 3
  %1888 = load %struct.centroid*, %struct.centroid** %1887, align 8
  %1889 = call %struct.centroid* @centroid_sum(%struct.centroid* %1881, %struct.centroid* %1888)
  store %struct.centroid* %1889, %struct.centroid** %41, align 8
  br label %1890

1890:                                             ; preds = %1880, %1860
  %1891 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1892 = getelementptr inbounds %struct.qtree, %struct.qtree* %1891, i32 0, i32 4
  %1893 = load %struct.qtree*, %struct.qtree** %1892, align 8
  %1894 = icmp ne %struct.qtree* %1893, null
  br i1 %1894, label %1895, label %1905

1895:                                             ; preds = %1890
  %1896 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1897 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1898 = getelementptr inbounds %struct.qtree, %struct.qtree* %1897, i32 0, i32 4
  %1899 = load %struct.qtree*, %struct.qtree** %1898, align 8
  %1900 = getelementptr inbounds %struct.qtree, %struct.qtree* %1899, i32 0, i32 0
  %1901 = load %struct.quad*, %struct.quad** %1900, align 8
  %1902 = getelementptr inbounds %struct.quad, %struct.quad* %1901, i32 0, i32 3
  %1903 = load %struct.centroid*, %struct.centroid** %1902, align 8
  %1904 = call %struct.centroid* @centroid_sum(%struct.centroid* %1896, %struct.centroid* %1903)
  store %struct.centroid* %1904, %struct.centroid** %41, align 8
  br label %1905

1905:                                             ; preds = %1895, %1890
  br label %1973

1906:                                             ; preds = %1846
  %1907 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1908 = getelementptr inbounds %struct.qtree, %struct.qtree* %1907, i32 0, i32 2
  %1909 = load %struct.qtree*, %struct.qtree** %1908, align 8
  %1910 = icmp ne %struct.qtree* %1909, null
  br i1 %1910, label %1911, label %1942

1911:                                             ; preds = %1906
  %1912 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1913 = getelementptr inbounds %struct.qtree, %struct.qtree* %1912, i32 0, i32 2
  %1914 = load %struct.qtree*, %struct.qtree** %1913, align 8
  %1915 = getelementptr inbounds %struct.qtree, %struct.qtree* %1914, i32 0, i32 0
  %1916 = load %struct.quad*, %struct.quad** %1915, align 8
  %1917 = getelementptr inbounds %struct.quad, %struct.quad* %1916, i32 0, i32 3
  %1918 = load %struct.centroid*, %struct.centroid** %1917, align 8
  %1919 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1920 = getelementptr inbounds %struct.qtree, %struct.qtree* %1919, i32 0, i32 3
  %1921 = load %struct.qtree*, %struct.qtree** %1920, align 8
  %1922 = getelementptr inbounds %struct.qtree, %struct.qtree* %1921, i32 0, i32 0
  %1923 = load %struct.quad*, %struct.quad** %1922, align 8
  %1924 = getelementptr inbounds %struct.quad, %struct.quad* %1923, i32 0, i32 3
  %1925 = load %struct.centroid*, %struct.centroid** %1924, align 8
  %1926 = call %struct.centroid* @centroid_sum(%struct.centroid* %1918, %struct.centroid* %1925)
  store %struct.centroid* %1926, %struct.centroid** %41, align 8
  %1927 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1928 = getelementptr inbounds %struct.qtree, %struct.qtree* %1927, i32 0, i32 4
  %1929 = load %struct.qtree*, %struct.qtree** %1928, align 8
  %1930 = icmp ne %struct.qtree* %1929, null
  br i1 %1930, label %1931, label %1941

1931:                                             ; preds = %1911
  %1932 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1933 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1934 = getelementptr inbounds %struct.qtree, %struct.qtree* %1933, i32 0, i32 4
  %1935 = load %struct.qtree*, %struct.qtree** %1934, align 8
  %1936 = getelementptr inbounds %struct.qtree, %struct.qtree* %1935, i32 0, i32 0
  %1937 = load %struct.quad*, %struct.quad** %1936, align 8
  %1938 = getelementptr inbounds %struct.quad, %struct.quad* %1937, i32 0, i32 3
  %1939 = load %struct.centroid*, %struct.centroid** %1938, align 8
  %1940 = call %struct.centroid* @centroid_sum(%struct.centroid* %1932, %struct.centroid* %1939)
  store %struct.centroid* %1940, %struct.centroid** %41, align 8
  br label %1941

1941:                                             ; preds = %1931, %1911
  br label %1972

1942:                                             ; preds = %1906
  %1943 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1944 = getelementptr inbounds %struct.qtree, %struct.qtree* %1943, i32 0, i32 4
  %1945 = load %struct.qtree*, %struct.qtree** %1944, align 8
  %1946 = icmp ne %struct.qtree* %1945, null
  br i1 %1946, label %1947, label %1963

1947:                                             ; preds = %1942
  %1948 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1949 = getelementptr inbounds %struct.qtree, %struct.qtree* %1948, i32 0, i32 3
  %1950 = load %struct.qtree*, %struct.qtree** %1949, align 8
  %1951 = getelementptr inbounds %struct.qtree, %struct.qtree* %1950, i32 0, i32 0
  %1952 = load %struct.quad*, %struct.quad** %1951, align 8
  %1953 = getelementptr inbounds %struct.quad, %struct.quad* %1952, i32 0, i32 3
  %1954 = load %struct.centroid*, %struct.centroid** %1953, align 8
  %1955 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1956 = getelementptr inbounds %struct.qtree, %struct.qtree* %1955, i32 0, i32 4
  %1957 = load %struct.qtree*, %struct.qtree** %1956, align 8
  %1958 = getelementptr inbounds %struct.qtree, %struct.qtree* %1957, i32 0, i32 0
  %1959 = load %struct.quad*, %struct.quad** %1958, align 8
  %1960 = getelementptr inbounds %struct.quad, %struct.quad* %1959, i32 0, i32 3
  %1961 = load %struct.centroid*, %struct.centroid** %1960, align 8
  %1962 = call %struct.centroid* @centroid_sum(%struct.centroid* %1954, %struct.centroid* %1961)
  store %struct.centroid* %1962, %struct.centroid** %41, align 8
  br label %1971

1963:                                             ; preds = %1942
  %1964 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1965 = getelementptr inbounds %struct.qtree, %struct.qtree* %1964, i32 0, i32 3
  %1966 = load %struct.qtree*, %struct.qtree** %1965, align 8
  %1967 = getelementptr inbounds %struct.qtree, %struct.qtree* %1966, i32 0, i32 0
  %1968 = load %struct.quad*, %struct.quad** %1967, align 8
  %1969 = getelementptr inbounds %struct.quad, %struct.quad* %1968, i32 0, i32 3
  %1970 = load %struct.centroid*, %struct.centroid** %1969, align 8
  store %struct.centroid* %1970, %struct.centroid** %41, align 8
  br label %1971

1971:                                             ; preds = %1963, %1947
  br label %1972

1972:                                             ; preds = %1971, %1941
  br label %1973

1973:                                             ; preds = %1972, %1905
  %1974 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1975 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1976 = getelementptr inbounds %struct.qtree, %struct.qtree* %1975, i32 0, i32 0
  %1977 = load %struct.quad*, %struct.quad** %1976, align 8
  %1978 = getelementptr inbounds %struct.quad, %struct.quad* %1977, i32 0, i32 3
  store %struct.centroid* %1974, %struct.centroid** %1978, align 8
  br label %2121

1979:                                             ; preds = %1838
  %1980 = load float, float* %5, align 4
  %1981 = load float, float* %6, align 4
  %1982 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1983 = getelementptr inbounds %struct.qtree, %struct.qtree* %1982, i32 0, i32 0
  %1984 = load %struct.quad*, %struct.quad** %1983, align 8
  %1985 = call i32 @which_quad(float %1980, float %1981, %struct.quad* %1984)
  %1986 = icmp eq i32 %1985, 4
  br i1 %1986, label %1987, label %2120

1987:                                             ; preds = %1979
  %1988 = load float, float* %5, align 4
  %1989 = load float, float* %6, align 4
  %1990 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1991 = getelementptr inbounds %struct.qtree, %struct.qtree* %1990, i32 0, i32 4
  %1992 = load %struct.qtree*, %struct.qtree** %1991, align 8
  %1993 = load float, float* %8, align 4
  %1994 = call %struct.qtree* @insertPoint(float %1988, float %1989, %struct.qtree* %1992, float %1993)
  %1995 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1996 = getelementptr inbounds %struct.qtree, %struct.qtree* %1995, i32 0, i32 4
  store %struct.qtree* %1994, %struct.qtree** %1996, align 8
  %1997 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1998 = getelementptr inbounds %struct.qtree, %struct.qtree* %1997, i32 0, i32 1
  %1999 = load %struct.qtree*, %struct.qtree** %1998, align 8
  %2000 = icmp ne %struct.qtree* %1999, null
  br i1 %2000, label %2001, label %2047

2001:                                             ; preds = %1987
  %2002 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2003 = getelementptr inbounds %struct.qtree, %struct.qtree* %2002, i32 0, i32 1
  %2004 = load %struct.qtree*, %struct.qtree** %2003, align 8
  %2005 = getelementptr inbounds %struct.qtree, %struct.qtree* %2004, i32 0, i32 0
  %2006 = load %struct.quad*, %struct.quad** %2005, align 8
  %2007 = getelementptr inbounds %struct.quad, %struct.quad* %2006, i32 0, i32 3
  %2008 = load %struct.centroid*, %struct.centroid** %2007, align 8
  %2009 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2010 = getelementptr inbounds %struct.qtree, %struct.qtree* %2009, i32 0, i32 4
  %2011 = load %struct.qtree*, %struct.qtree** %2010, align 8
  %2012 = getelementptr inbounds %struct.qtree, %struct.qtree* %2011, i32 0, i32 0
  %2013 = load %struct.quad*, %struct.quad** %2012, align 8
  %2014 = getelementptr inbounds %struct.quad, %struct.quad* %2013, i32 0, i32 3
  %2015 = load %struct.centroid*, %struct.centroid** %2014, align 8
  %2016 = call %struct.centroid* @centroid_sum(%struct.centroid* %2008, %struct.centroid* %2015)
  store %struct.centroid* %2016, %struct.centroid** %42, align 8
  %2017 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2018 = getelementptr inbounds %struct.qtree, %struct.qtree* %2017, i32 0, i32 2
  %2019 = load %struct.qtree*, %struct.qtree** %2018, align 8
  %2020 = icmp ne %struct.qtree* %2019, null
  br i1 %2020, label %2021, label %2031

2021:                                             ; preds = %2001
  %2022 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2023 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2024 = getelementptr inbounds %struct.qtree, %struct.qtree* %2023, i32 0, i32 2
  %2025 = load %struct.qtree*, %struct.qtree** %2024, align 8
  %2026 = getelementptr inbounds %struct.qtree, %struct.qtree* %2025, i32 0, i32 0
  %2027 = load %struct.quad*, %struct.quad** %2026, align 8
  %2028 = getelementptr inbounds %struct.quad, %struct.quad* %2027, i32 0, i32 3
  %2029 = load %struct.centroid*, %struct.centroid** %2028, align 8
  %2030 = call %struct.centroid* @centroid_sum(%struct.centroid* %2022, %struct.centroid* %2029)
  store %struct.centroid* %2030, %struct.centroid** %42, align 8
  br label %2031

2031:                                             ; preds = %2021, %2001
  %2032 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2033 = getelementptr inbounds %struct.qtree, %struct.qtree* %2032, i32 0, i32 3
  %2034 = load %struct.qtree*, %struct.qtree** %2033, align 8
  %2035 = icmp ne %struct.qtree* %2034, null
  br i1 %2035, label %2036, label %2046

2036:                                             ; preds = %2031
  %2037 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2038 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2039 = getelementptr inbounds %struct.qtree, %struct.qtree* %2038, i32 0, i32 3
  %2040 = load %struct.qtree*, %struct.qtree** %2039, align 8
  %2041 = getelementptr inbounds %struct.qtree, %struct.qtree* %2040, i32 0, i32 0
  %2042 = load %struct.quad*, %struct.quad** %2041, align 8
  %2043 = getelementptr inbounds %struct.quad, %struct.quad* %2042, i32 0, i32 3
  %2044 = load %struct.centroid*, %struct.centroid** %2043, align 8
  %2045 = call %struct.centroid* @centroid_sum(%struct.centroid* %2037, %struct.centroid* %2044)
  store %struct.centroid* %2045, %struct.centroid** %42, align 8
  br label %2046

2046:                                             ; preds = %2036, %2031
  br label %2114

2047:                                             ; preds = %1987
  %2048 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2049 = getelementptr inbounds %struct.qtree, %struct.qtree* %2048, i32 0, i32 2
  %2050 = load %struct.qtree*, %struct.qtree** %2049, align 8
  %2051 = icmp ne %struct.qtree* %2050, null
  br i1 %2051, label %2052, label %2083

2052:                                             ; preds = %2047
  %2053 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2054 = getelementptr inbounds %struct.qtree, %struct.qtree* %2053, i32 0, i32 2
  %2055 = load %struct.qtree*, %struct.qtree** %2054, align 8
  %2056 = getelementptr inbounds %struct.qtree, %struct.qtree* %2055, i32 0, i32 0
  %2057 = load %struct.quad*, %struct.quad** %2056, align 8
  %2058 = getelementptr inbounds %struct.quad, %struct.quad* %2057, i32 0, i32 3
  %2059 = load %struct.centroid*, %struct.centroid** %2058, align 8
  %2060 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2061 = getelementptr inbounds %struct.qtree, %struct.qtree* %2060, i32 0, i32 4
  %2062 = load %struct.qtree*, %struct.qtree** %2061, align 8
  %2063 = getelementptr inbounds %struct.qtree, %struct.qtree* %2062, i32 0, i32 0
  %2064 = load %struct.quad*, %struct.quad** %2063, align 8
  %2065 = getelementptr inbounds %struct.quad, %struct.quad* %2064, i32 0, i32 3
  %2066 = load %struct.centroid*, %struct.centroid** %2065, align 8
  %2067 = call %struct.centroid* @centroid_sum(%struct.centroid* %2059, %struct.centroid* %2066)
  store %struct.centroid* %2067, %struct.centroid** %42, align 8
  %2068 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2069 = getelementptr inbounds %struct.qtree, %struct.qtree* %2068, i32 0, i32 3
  %2070 = load %struct.qtree*, %struct.qtree** %2069, align 8
  %2071 = icmp ne %struct.qtree* %2070, null
  br i1 %2071, label %2072, label %2082

2072:                                             ; preds = %2052
  %2073 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2074 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2075 = getelementptr inbounds %struct.qtree, %struct.qtree* %2074, i32 0, i32 3
  %2076 = load %struct.qtree*, %struct.qtree** %2075, align 8
  %2077 = getelementptr inbounds %struct.qtree, %struct.qtree* %2076, i32 0, i32 0
  %2078 = load %struct.quad*, %struct.quad** %2077, align 8
  %2079 = getelementptr inbounds %struct.quad, %struct.quad* %2078, i32 0, i32 3
  %2080 = load %struct.centroid*, %struct.centroid** %2079, align 8
  %2081 = call %struct.centroid* @centroid_sum(%struct.centroid* %2073, %struct.centroid* %2080)
  store %struct.centroid* %2081, %struct.centroid** %42, align 8
  br label %2082

2082:                                             ; preds = %2072, %2052
  br label %2113

2083:                                             ; preds = %2047
  %2084 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2085 = getelementptr inbounds %struct.qtree, %struct.qtree* %2084, i32 0, i32 2
  %2086 = load %struct.qtree*, %struct.qtree** %2085, align 8
  %2087 = icmp ne %struct.qtree* %2086, null
  br i1 %2087, label %2088, label %2104

2088:                                             ; preds = %2083
  %2089 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2090 = getelementptr inbounds %struct.qtree, %struct.qtree* %2089, i32 0, i32 2
  %2091 = load %struct.qtree*, %struct.qtree** %2090, align 8
  %2092 = getelementptr inbounds %struct.qtree, %struct.qtree* %2091, i32 0, i32 0
  %2093 = load %struct.quad*, %struct.quad** %2092, align 8
  %2094 = getelementptr inbounds %struct.quad, %struct.quad* %2093, i32 0, i32 3
  %2095 = load %struct.centroid*, %struct.centroid** %2094, align 8
  %2096 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2097 = getelementptr inbounds %struct.qtree, %struct.qtree* %2096, i32 0, i32 4
  %2098 = load %struct.qtree*, %struct.qtree** %2097, align 8
  %2099 = getelementptr inbounds %struct.qtree, %struct.qtree* %2098, i32 0, i32 0
  %2100 = load %struct.quad*, %struct.quad** %2099, align 8
  %2101 = getelementptr inbounds %struct.quad, %struct.quad* %2100, i32 0, i32 3
  %2102 = load %struct.centroid*, %struct.centroid** %2101, align 8
  %2103 = call %struct.centroid* @centroid_sum(%struct.centroid* %2095, %struct.centroid* %2102)
  store %struct.centroid* %2103, %struct.centroid** %42, align 8
  br label %2112

2104:                                             ; preds = %2083
  %2105 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2106 = getelementptr inbounds %struct.qtree, %struct.qtree* %2105, i32 0, i32 4
  %2107 = load %struct.qtree*, %struct.qtree** %2106, align 8
  %2108 = getelementptr inbounds %struct.qtree, %struct.qtree* %2107, i32 0, i32 0
  %2109 = load %struct.quad*, %struct.quad** %2108, align 8
  %2110 = getelementptr inbounds %struct.quad, %struct.quad* %2109, i32 0, i32 3
  %2111 = load %struct.centroid*, %struct.centroid** %2110, align 8
  store %struct.centroid* %2111, %struct.centroid** %42, align 8
  br label %2112

2112:                                             ; preds = %2104, %2088
  br label %2113

2113:                                             ; preds = %2112, %2082
  br label %2114

2114:                                             ; preds = %2113, %2046
  %2115 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2116 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2117 = getelementptr inbounds %struct.qtree, %struct.qtree* %2116, i32 0, i32 0
  %2118 = load %struct.quad*, %struct.quad** %2117, align 8
  %2119 = getelementptr inbounds %struct.quad, %struct.quad* %2118, i32 0, i32 3
  store %struct.centroid* %2115, %struct.centroid** %2119, align 8
  br label %2120

2120:                                             ; preds = %2114, %1979
  br label %2121

2121:                                             ; preds = %2120, %1973
  br label %2122

2122:                                             ; preds = %2121, %1832
  br label %2123

2123:                                             ; preds = %2122, %1691
  br label %2124

2124:                                             ; preds = %2123, %1550
  br label %2125

2125:                                             ; preds = %2124, %1178
  br label %2126

2126:                                             ; preds = %2125, %812
  br label %2127

2127:                                             ; preds = %2126, %446
  br label %2128

2128:                                             ; preds = %2127, %76
  br label %2129

2129:                                             ; preds = %2128, %45
  %2130 = load %struct.qtree*, %struct.qtree** %7, align 8
  ret %struct.qtree* %2130
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @body() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca %struct.qtree*, align 8
  %17 = alloca %struct.qtree*, align 8
  %18 = alloca %struct.qtree*, align 8
  %19 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  store i32 0, i32* %2, align 4
  store i32 0, i32* %3, align 4
  store i32 0, i32* %4, align 4
  store i32 0, i32* %5, align 4
  store i32 0, i32* %6, align 4
  store i32 0, i32* %7, align 4
  store i32 0, i32* %8, align 4
  store i32 0, i32* %9, align 4
  store i32 0, i32* %10, align 4
  store i32 0, i32* %11, align 4
  store i32 0, i32* %12, align 4
  store i32 0, i32* %13, align 4
  store i32 0, i32* %14, align 4
  store i32 0, i32* %15, align 4
  store %struct.qtree* null, %struct.qtree** %16, align 8
  %20 = load %struct.qtree*, %struct.qtree** %16, align 8
  %21 = call %struct.qtree* @insertPoint(float 1.500000e+00, float 2.500000e+00, %struct.qtree* %20, float 1.000000e+00)
  store %struct.qtree* %21, %struct.qtree** %16, align 8
  %22 = load %struct.qtree*, %struct.qtree** %16, align 8
  %23 = call %struct.qtree* @insertPoint(float 0x4000CCCCC0000000, float 0x4000CCCCC0000000, %struct.qtree* %22, float 1.000000e+00)
  store %struct.qtree* %23, %struct.qtree** %16, align 8
  %24 = load %struct.qtree*, %struct.qtree** %16, align 8
  %25 = call %struct.qtree* @insertPoint(float 1.000000e+00, float 1.000000e+00, %struct.qtree* %24, float 2.000000e+00)
  store %struct.qtree* %25, %struct.qtree** %16, align 8
  %26 = load %struct.qtree*, %struct.qtree** %16, align 8
  %27 = getelementptr inbounds %struct.qtree, %struct.qtree* %26, i32 0, i32 0
  %28 = load %struct.quad*, %struct.quad** %27, align 8
  %29 = getelementptr inbounds %struct.quad, %struct.quad* %28, i32 0, i32 3
  %30 = load %struct.centroid*, %struct.centroid** %29, align 8
  %31 = getelementptr inbounds %struct.centroid, %struct.centroid* %30, i32 0, i32 0
  %32 = load float, float* %31, align 4
  %33 = call i32 @compare_float(float %32, float 0x3FF6666660000000)
  %34 = icmp ne i32 %33, 0
  br i1 %34, label %35, label %56

35:                                               ; preds = %0
  %36 = load %struct.qtree*, %struct.qtree** %16, align 8
  %37 = getelementptr inbounds %struct.qtree, %struct.qtree* %36, i32 0, i32 0
  %38 = load %struct.quad*, %struct.quad** %37, align 8
  %39 = getelementptr inbounds %struct.quad, %struct.quad* %38, i32 0, i32 3
  %40 = load %struct.centroid*, %struct.centroid** %39, align 8
  %41 = getelementptr inbounds %struct.centroid, %struct.centroid* %40, i32 0, i32 1
  %42 = load float, float* %41, align 4
  %43 = call i32 @compare_float(float %42, float 0x3FFA666660000000)
  %44 = icmp ne i32 %43, 0
  br i1 %44, label %45, label %56

45:                                               ; preds = %35
  %46 = load %struct.qtree*, %struct.qtree** %16, align 8
  %47 = getelementptr inbounds %struct.qtree, %struct.qtree* %46, i32 0, i32 0
  %48 = load %struct.quad*, %struct.quad** %47, align 8
  %49 = getelementptr inbounds %struct.quad, %struct.quad* %48, i32 0, i32 3
  %50 = load %struct.centroid*, %struct.centroid** %49, align 8
  %51 = getelementptr inbounds %struct.centroid, %struct.centroid* %50, i32 0, i32 2
  %52 = load float, float* %51, align 4
  %53 = call i32 @compare_float(float %52, float 4.000000e+00)
  %54 = icmp ne i32 %53, 0
  br i1 %54, label %55, label %56

55:                                               ; preds = %45
  store i32 1, i32* %1, align 4
  br label %56

56:                                               ; preds = %55, %45, %35, %0
  %57 = load %struct.qtree*, %struct.qtree** %16, align 8
  %58 = call %struct.qtree* @insertPoint(float 0x4004CCCCC0000000, float 0x4006666660000000, %struct.qtree* %57, float 1.000000e+00)
  store %struct.qtree* %58, %struct.qtree** %16, align 8
  %59 = load %struct.qtree*, %struct.qtree** %16, align 8
  %60 = getelementptr inbounds %struct.qtree, %struct.qtree* %59, i32 0, i32 4
  %61 = load %struct.qtree*, %struct.qtree** %60, align 8
  %62 = getelementptr inbounds %struct.qtree, %struct.qtree* %61, i32 0, i32 1
  %63 = load %struct.qtree*, %struct.qtree** %62, align 8
  %64 = getelementptr inbounds %struct.qtree, %struct.qtree* %63, i32 0, i32 4
  %65 = load %struct.qtree*, %struct.qtree** %64, align 8
  %66 = getelementptr inbounds %struct.qtree, %struct.qtree* %65, i32 0, i32 0
  %67 = load %struct.quad*, %struct.quad** %66, align 8
  %68 = getelementptr inbounds %struct.quad, %struct.quad* %67, i32 0, i32 3
  %69 = load %struct.centroid*, %struct.centroid** %68, align 8
  %70 = getelementptr inbounds %struct.centroid, %struct.centroid* %69, i32 0, i32 0
  %71 = load float, float* %70, align 4
  %72 = call i32 @compare_float(float %71, float 0x4004CCCCC0000000)
  %73 = icmp ne i32 %72, 0
  br i1 %73, label %74, label %107

74:                                               ; preds = %56
  %75 = load %struct.qtree*, %struct.qtree** %16, align 8
  %76 = getelementptr inbounds %struct.qtree, %struct.qtree* %75, i32 0, i32 4
  %77 = load %struct.qtree*, %struct.qtree** %76, align 8
  %78 = getelementptr inbounds %struct.qtree, %struct.qtree* %77, i32 0, i32 1
  %79 = load %struct.qtree*, %struct.qtree** %78, align 8
  %80 = getelementptr inbounds %struct.qtree, %struct.qtree* %79, i32 0, i32 4
  %81 = load %struct.qtree*, %struct.qtree** %80, align 8
  %82 = getelementptr inbounds %struct.qtree, %struct.qtree* %81, i32 0, i32 0
  %83 = load %struct.quad*, %struct.quad** %82, align 8
  %84 = getelementptr inbounds %struct.quad, %struct.quad* %83, i32 0, i32 3
  %85 = load %struct.centroid*, %struct.centroid** %84, align 8
  %86 = getelementptr inbounds %struct.centroid, %struct.centroid* %85, i32 0, i32 1
  %87 = load float, float* %86, align 4
  %88 = call i32 @compare_float(float %87, float 0x4006666660000000)
  %89 = icmp ne i32 %88, 0
  br i1 %89, label %90, label %107

90:                                               ; preds = %74
  %91 = load %struct.qtree*, %struct.qtree** %16, align 8
  %92 = getelementptr inbounds %struct.qtree, %struct.qtree* %91, i32 0, i32 4
  %93 = load %struct.qtree*, %struct.qtree** %92, align 8
  %94 = getelementptr inbounds %struct.qtree, %struct.qtree* %93, i32 0, i32 1
  %95 = load %struct.qtree*, %struct.qtree** %94, align 8
  %96 = getelementptr inbounds %struct.qtree, %struct.qtree* %95, i32 0, i32 4
  %97 = load %struct.qtree*, %struct.qtree** %96, align 8
  %98 = getelementptr inbounds %struct.qtree, %struct.qtree* %97, i32 0, i32 0
  %99 = load %struct.quad*, %struct.quad** %98, align 8
  %100 = getelementptr inbounds %struct.quad, %struct.quad* %99, i32 0, i32 3
  %101 = load %struct.centroid*, %struct.centroid** %100, align 8
  %102 = getelementptr inbounds %struct.centroid, %struct.centroid* %101, i32 0, i32 2
  %103 = load float, float* %102, align 4
  %104 = call i32 @compare_float(float %103, float 1.000000e+00)
  %105 = icmp ne i32 %104, 0
  br i1 %105, label %106, label %107

106:                                              ; preds = %90
  store i32 1, i32* %2, align 4
  br label %107

107:                                              ; preds = %106, %90, %74, %56
  %108 = load %struct.qtree*, %struct.qtree** %16, align 8
  %109 = getelementptr inbounds %struct.qtree, %struct.qtree* %108, i32 0, i32 1
  %110 = load %struct.qtree*, %struct.qtree** %109, align 8
  %111 = getelementptr inbounds %struct.qtree, %struct.qtree* %110, i32 0, i32 0
  %112 = load %struct.quad*, %struct.quad** %111, align 8
  %113 = getelementptr inbounds %struct.quad, %struct.quad* %112, i32 0, i32 3
  %114 = load %struct.centroid*, %struct.centroid** %113, align 8
  %115 = getelementptr inbounds %struct.centroid, %struct.centroid* %114, i32 0, i32 0
  %116 = load float, float* %115, align 4
  %117 = call i32 @compare_float(float %116, float 1.000000e+00)
  %118 = icmp ne i32 %117, 0
  br i1 %118, label %119, label %144

119:                                              ; preds = %107
  %120 = load %struct.qtree*, %struct.qtree** %16, align 8
  %121 = getelementptr inbounds %struct.qtree, %struct.qtree* %120, i32 0, i32 1
  %122 = load %struct.qtree*, %struct.qtree** %121, align 8
  %123 = getelementptr inbounds %struct.qtree, %struct.qtree* %122, i32 0, i32 0
  %124 = load %struct.quad*, %struct.quad** %123, align 8
  %125 = getelementptr inbounds %struct.quad, %struct.quad* %124, i32 0, i32 3
  %126 = load %struct.centroid*, %struct.centroid** %125, align 8
  %127 = getelementptr inbounds %struct.centroid, %struct.centroid* %126, i32 0, i32 1
  %128 = load float, float* %127, align 4
  %129 = call i32 @compare_float(float %128, float 1.000000e+00)
  %130 = icmp ne i32 %129, 0
  br i1 %130, label %131, label %144

131:                                              ; preds = %119
  %132 = load %struct.qtree*, %struct.qtree** %16, align 8
  %133 = getelementptr inbounds %struct.qtree, %struct.qtree* %132, i32 0, i32 1
  %134 = load %struct.qtree*, %struct.qtree** %133, align 8
  %135 = getelementptr inbounds %struct.qtree, %struct.qtree* %134, i32 0, i32 0
  %136 = load %struct.quad*, %struct.quad** %135, align 8
  %137 = getelementptr inbounds %struct.quad, %struct.quad* %136, i32 0, i32 3
  %138 = load %struct.centroid*, %struct.centroid** %137, align 8
  %139 = getelementptr inbounds %struct.centroid, %struct.centroid* %138, i32 0, i32 2
  %140 = load float, float* %139, align 4
  %141 = call i32 @compare_float(float %140, float 2.000000e+00)
  %142 = icmp ne i32 %141, 0
  br i1 %142, label %143, label %144

143:                                              ; preds = %131
  store i32 1, i32* %3, align 4
  br label %144

144:                                              ; preds = %143, %131, %119, %107
  %145 = load %struct.qtree*, %struct.qtree** %16, align 8
  %146 = getelementptr inbounds %struct.qtree, %struct.qtree* %145, i32 0, i32 3
  %147 = load %struct.qtree*, %struct.qtree** %146, align 8
  %148 = getelementptr inbounds %struct.qtree, %struct.qtree* %147, i32 0, i32 0
  %149 = load %struct.quad*, %struct.quad** %148, align 8
  %150 = getelementptr inbounds %struct.quad, %struct.quad* %149, i32 0, i32 3
  %151 = load %struct.centroid*, %struct.centroid** %150, align 8
  %152 = getelementptr inbounds %struct.centroid, %struct.centroid* %151, i32 0, i32 0
  %153 = load float, float* %152, align 4
  %154 = call i32 @compare_float(float %153, float 1.500000e+00)
  %155 = icmp ne i32 %154, 0
  br i1 %155, label %156, label %181

156:                                              ; preds = %144
  %157 = load %struct.qtree*, %struct.qtree** %16, align 8
  %158 = getelementptr inbounds %struct.qtree, %struct.qtree* %157, i32 0, i32 3
  %159 = load %struct.qtree*, %struct.qtree** %158, align 8
  %160 = getelementptr inbounds %struct.qtree, %struct.qtree* %159, i32 0, i32 0
  %161 = load %struct.quad*, %struct.quad** %160, align 8
  %162 = getelementptr inbounds %struct.quad, %struct.quad* %161, i32 0, i32 3
  %163 = load %struct.centroid*, %struct.centroid** %162, align 8
  %164 = getelementptr inbounds %struct.centroid, %struct.centroid* %163, i32 0, i32 1
  %165 = load float, float* %164, align 4
  %166 = call i32 @compare_float(float %165, float 2.500000e+00)
  %167 = icmp ne i32 %166, 0
  br i1 %167, label %168, label %181

168:                                              ; preds = %156
  %169 = load %struct.qtree*, %struct.qtree** %16, align 8
  %170 = getelementptr inbounds %struct.qtree, %struct.qtree* %169, i32 0, i32 3
  %171 = load %struct.qtree*, %struct.qtree** %170, align 8
  %172 = getelementptr inbounds %struct.qtree, %struct.qtree* %171, i32 0, i32 0
  %173 = load %struct.quad*, %struct.quad** %172, align 8
  %174 = getelementptr inbounds %struct.quad, %struct.quad* %173, i32 0, i32 3
  %175 = load %struct.centroid*, %struct.centroid** %174, align 8
  %176 = getelementptr inbounds %struct.centroid, %struct.centroid* %175, i32 0, i32 2
  %177 = load float, float* %176, align 4
  %178 = call i32 @compare_float(float %177, float 1.000000e+00)
  %179 = icmp ne i32 %178, 0
  br i1 %179, label %180, label %181

180:                                              ; preds = %168
  store i32 1, i32* %4, align 4
  br label %181

181:                                              ; preds = %180, %168, %156, %144
  %182 = load %struct.qtree*, %struct.qtree** %16, align 8
  %183 = getelementptr inbounds %struct.qtree, %struct.qtree* %182, i32 0, i32 4
  %184 = load %struct.qtree*, %struct.qtree** %183, align 8
  %185 = getelementptr inbounds %struct.qtree, %struct.qtree* %184, i32 0, i32 1
  %186 = load %struct.qtree*, %struct.qtree** %185, align 8
  %187 = getelementptr inbounds %struct.qtree, %struct.qtree* %186, i32 0, i32 1
  %188 = load %struct.qtree*, %struct.qtree** %187, align 8
  %189 = getelementptr inbounds %struct.qtree, %struct.qtree* %188, i32 0, i32 0
  %190 = load %struct.quad*, %struct.quad** %189, align 8
  %191 = getelementptr inbounds %struct.quad, %struct.quad* %190, i32 0, i32 3
  %192 = load %struct.centroid*, %struct.centroid** %191, align 8
  %193 = getelementptr inbounds %struct.centroid, %struct.centroid* %192, i32 0, i32 0
  %194 = load float, float* %193, align 4
  %195 = call i32 @compare_float(float %194, float 0x4000CCCCC0000000)
  %196 = icmp ne i32 %195, 0
  br i1 %196, label %197, label %230

197:                                              ; preds = %181
  %198 = load %struct.qtree*, %struct.qtree** %16, align 8
  %199 = getelementptr inbounds %struct.qtree, %struct.qtree* %198, i32 0, i32 4
  %200 = load %struct.qtree*, %struct.qtree** %199, align 8
  %201 = getelementptr inbounds %struct.qtree, %struct.qtree* %200, i32 0, i32 1
  %202 = load %struct.qtree*, %struct.qtree** %201, align 8
  %203 = getelementptr inbounds %struct.qtree, %struct.qtree* %202, i32 0, i32 1
  %204 = load %struct.qtree*, %struct.qtree** %203, align 8
  %205 = getelementptr inbounds %struct.qtree, %struct.qtree* %204, i32 0, i32 0
  %206 = load %struct.quad*, %struct.quad** %205, align 8
  %207 = getelementptr inbounds %struct.quad, %struct.quad* %206, i32 0, i32 3
  %208 = load %struct.centroid*, %struct.centroid** %207, align 8
  %209 = getelementptr inbounds %struct.centroid, %struct.centroid* %208, i32 0, i32 1
  %210 = load float, float* %209, align 4
  %211 = call i32 @compare_float(float %210, float 0x4000CCCCC0000000)
  %212 = icmp ne i32 %211, 0
  br i1 %212, label %213, label %230

213:                                              ; preds = %197
  %214 = load %struct.qtree*, %struct.qtree** %16, align 8
  %215 = getelementptr inbounds %struct.qtree, %struct.qtree* %214, i32 0, i32 4
  %216 = load %struct.qtree*, %struct.qtree** %215, align 8
  %217 = getelementptr inbounds %struct.qtree, %struct.qtree* %216, i32 0, i32 1
  %218 = load %struct.qtree*, %struct.qtree** %217, align 8
  %219 = getelementptr inbounds %struct.qtree, %struct.qtree* %218, i32 0, i32 1
  %220 = load %struct.qtree*, %struct.qtree** %219, align 8
  %221 = getelementptr inbounds %struct.qtree, %struct.qtree* %220, i32 0, i32 0
  %222 = load %struct.quad*, %struct.quad** %221, align 8
  %223 = getelementptr inbounds %struct.quad, %struct.quad* %222, i32 0, i32 3
  %224 = load %struct.centroid*, %struct.centroid** %223, align 8
  %225 = getelementptr inbounds %struct.centroid, %struct.centroid* %224, i32 0, i32 2
  %226 = load float, float* %225, align 4
  %227 = call i32 @compare_float(float %226, float 1.000000e+00)
  %228 = icmp ne i32 %227, 0
  br i1 %228, label %229, label %230

229:                                              ; preds = %213
  store i32 1, i32* %5, align 4
  br label %230

230:                                              ; preds = %229, %213, %197, %181
  %231 = load %struct.qtree*, %struct.qtree** %16, align 8
  %232 = getelementptr inbounds %struct.qtree, %struct.qtree* %231, i32 0, i32 4
  %233 = load %struct.qtree*, %struct.qtree** %232, align 8
  %234 = getelementptr inbounds %struct.qtree, %struct.qtree* %233, i32 0, i32 1
  %235 = load %struct.qtree*, %struct.qtree** %234, align 8
  %236 = getelementptr inbounds %struct.qtree, %struct.qtree* %235, i32 0, i32 0
  %237 = load %struct.quad*, %struct.quad** %236, align 8
  %238 = getelementptr inbounds %struct.quad, %struct.quad* %237, i32 0, i32 3
  %239 = load %struct.centroid*, %struct.centroid** %238, align 8
  %240 = getelementptr inbounds %struct.centroid, %struct.centroid* %239, i32 0, i32 0
  %241 = load float, float* %240, align 4
  %242 = call i32 @compare_float(float %241, float 0x4002CCCCC0000000)
  %243 = icmp ne i32 %242, 0
  br i1 %243, label %244, label %273

244:                                              ; preds = %230
  %245 = load %struct.qtree*, %struct.qtree** %16, align 8
  %246 = getelementptr inbounds %struct.qtree, %struct.qtree* %245, i32 0, i32 4
  %247 = load %struct.qtree*, %struct.qtree** %246, align 8
  %248 = getelementptr inbounds %struct.qtree, %struct.qtree* %247, i32 0, i32 1
  %249 = load %struct.qtree*, %struct.qtree** %248, align 8
  %250 = getelementptr inbounds %struct.qtree, %struct.qtree* %249, i32 0, i32 0
  %251 = load %struct.quad*, %struct.quad** %250, align 8
  %252 = getelementptr inbounds %struct.quad, %struct.quad* %251, i32 0, i32 3
  %253 = load %struct.centroid*, %struct.centroid** %252, align 8
  %254 = getelementptr inbounds %struct.centroid, %struct.centroid* %253, i32 0, i32 1
  %255 = load float, float* %254, align 4
  %256 = call i32 @compare_float(float %255, float 0x40039999A0000000)
  %257 = icmp ne i32 %256, 0
  br i1 %257, label %258, label %273

258:                                              ; preds = %244
  %259 = load %struct.qtree*, %struct.qtree** %16, align 8
  %260 = getelementptr inbounds %struct.qtree, %struct.qtree* %259, i32 0, i32 4
  %261 = load %struct.qtree*, %struct.qtree** %260, align 8
  %262 = getelementptr inbounds %struct.qtree, %struct.qtree* %261, i32 0, i32 1
  %263 = load %struct.qtree*, %struct.qtree** %262, align 8
  %264 = getelementptr inbounds %struct.qtree, %struct.qtree* %263, i32 0, i32 0
  %265 = load %struct.quad*, %struct.quad** %264, align 8
  %266 = getelementptr inbounds %struct.quad, %struct.quad* %265, i32 0, i32 3
  %267 = load %struct.centroid*, %struct.centroid** %266, align 8
  %268 = getelementptr inbounds %struct.centroid, %struct.centroid* %267, i32 0, i32 2
  %269 = load float, float* %268, align 4
  %270 = call i32 @compare_float(float %269, float 2.000000e+00)
  %271 = icmp ne i32 %270, 0
  br i1 %271, label %272, label %273

272:                                              ; preds = %258
  store i32 1, i32* %6, align 4
  br label %273

273:                                              ; preds = %272, %258, %244, %230
  %274 = load %struct.qtree*, %struct.qtree** %16, align 8
  %275 = getelementptr inbounds %struct.qtree, %struct.qtree* %274, i32 0, i32 0
  %276 = load %struct.quad*, %struct.quad** %275, align 8
  %277 = getelementptr inbounds %struct.quad, %struct.quad* %276, i32 0, i32 3
  %278 = load %struct.centroid*, %struct.centroid** %277, align 8
  %279 = getelementptr inbounds %struct.centroid, %struct.centroid* %278, i32 0, i32 0
  %280 = load float, float* %279, align 4
  %281 = call i32 @compare_float(float %280, float 0x3FFA3D70A0000000)
  %282 = icmp ne i32 %281, 0
  br i1 %282, label %283, label %304

283:                                              ; preds = %273
  %284 = load %struct.qtree*, %struct.qtree** %16, align 8
  %285 = getelementptr inbounds %struct.qtree, %struct.qtree* %284, i32 0, i32 0
  %286 = load %struct.quad*, %struct.quad** %285, align 8
  %287 = getelementptr inbounds %struct.quad, %struct.quad* %286, i32 0, i32 3
  %288 = load %struct.centroid*, %struct.centroid** %287, align 8
  %289 = getelementptr inbounds %struct.centroid, %struct.centroid* %288, i32 0, i32 1
  %290 = load float, float* %289, align 4
  %291 = call i32 @compare_float(float %290, float 0x3FFE147AE0000000)
  %292 = icmp ne i32 %291, 0
  br i1 %292, label %293, label %304

293:                                              ; preds = %283
  %294 = load %struct.qtree*, %struct.qtree** %16, align 8
  %295 = getelementptr inbounds %struct.qtree, %struct.qtree* %294, i32 0, i32 0
  %296 = load %struct.quad*, %struct.quad** %295, align 8
  %297 = getelementptr inbounds %struct.quad, %struct.quad* %296, i32 0, i32 3
  %298 = load %struct.centroid*, %struct.centroid** %297, align 8
  %299 = getelementptr inbounds %struct.centroid, %struct.centroid* %298, i32 0, i32 2
  %300 = load float, float* %299, align 4
  %301 = call i32 @compare_float(float %300, float 5.000000e+00)
  %302 = icmp ne i32 %301, 0
  br i1 %302, label %303, label %304

303:                                              ; preds = %293
  store i32 1, i32* %7, align 4
  br label %304

304:                                              ; preds = %303, %293, %283, %273
  store %struct.qtree* null, %struct.qtree** %17, align 8
  %305 = load %struct.qtree*, %struct.qtree** %17, align 8
  %306 = call %struct.qtree* @insertPoint(float 1.000000e+00, float 1.000000e+00, %struct.qtree* %305, float 1.000000e+00)
  store %struct.qtree* %306, %struct.qtree** %17, align 8
  %307 = load %struct.qtree*, %struct.qtree** %17, align 8
  %308 = call %struct.qtree* @insertPoint(float 1.000000e+00, float 1.000000e+00, %struct.qtree* %307, float 1.000000e+00)
  store %struct.qtree* %308, %struct.qtree** %17, align 8
  %309 = load %struct.qtree*, %struct.qtree** %17, align 8
  %310 = getelementptr inbounds %struct.qtree, %struct.qtree* %309, i32 0, i32 0
  %311 = load %struct.quad*, %struct.quad** %310, align 8
  %312 = getelementptr inbounds %struct.quad, %struct.quad* %311, i32 0, i32 3
  %313 = load %struct.centroid*, %struct.centroid** %312, align 8
  %314 = getelementptr inbounds %struct.centroid, %struct.centroid* %313, i32 0, i32 2
  %315 = load float, float* %314, align 4
  %316 = call i32 @compare_float(float %315, float 2.000000e+00)
  %317 = icmp ne i32 %316, 0
  br i1 %317, label %318, label %319

318:                                              ; preds = %304
  store i32 1, i32* %8, align 4
  br label %319

319:                                              ; preds = %318, %304
  store %struct.qtree* null, %struct.qtree** %18, align 8
  %320 = load %struct.qtree*, %struct.qtree** %18, align 8
  %321 = call %struct.qtree* @insertPoint(float 0.000000e+00, float 0.000000e+00, %struct.qtree* %320, float 1.000000e+00)
  store %struct.qtree* %321, %struct.qtree** %18, align 8
  %322 = load %struct.qtree*, %struct.qtree** %18, align 8
  %323 = call %struct.qtree* @insertPoint(float 0x3FC99999A0000000, float 0x3FC99999A0000000, %struct.qtree* %322, float 1.000000e+00)
  store %struct.qtree* %323, %struct.qtree** %18, align 8
  %324 = load %struct.qtree*, %struct.qtree** %18, align 8
  %325 = getelementptr inbounds %struct.qtree, %struct.qtree* %324, i32 0, i32 0
  %326 = load %struct.quad*, %struct.quad** %325, align 8
  %327 = getelementptr inbounds %struct.quad, %struct.quad* %326, i32 0, i32 3
  %328 = load %struct.centroid*, %struct.centroid** %327, align 8
  %329 = getelementptr inbounds %struct.centroid, %struct.centroid* %328, i32 0, i32 0
  %330 = load float, float* %329, align 4
  %331 = call i32 @compare_float(float %330, float 0x3FB99999A0000000)
  %332 = icmp ne i32 %331, 0
  br i1 %332, label %333, label %354

333:                                              ; preds = %319
  %334 = load %struct.qtree*, %struct.qtree** %18, align 8
  %335 = getelementptr inbounds %struct.qtree, %struct.qtree* %334, i32 0, i32 0
  %336 = load %struct.quad*, %struct.quad** %335, align 8
  %337 = getelementptr inbounds %struct.quad, %struct.quad* %336, i32 0, i32 3
  %338 = load %struct.centroid*, %struct.centroid** %337, align 8
  %339 = getelementptr inbounds %struct.centroid, %struct.centroid* %338, i32 0, i32 1
  %340 = load float, float* %339, align 4
  %341 = call i32 @compare_float(float %340, float 0x3FB99999A0000000)
  %342 = icmp ne i32 %341, 0
  br i1 %342, label %343, label %354

343:                                              ; preds = %333
  %344 = load %struct.qtree*, %struct.qtree** %18, align 8
  %345 = getelementptr inbounds %struct.qtree, %struct.qtree* %344, i32 0, i32 0
  %346 = load %struct.quad*, %struct.quad** %345, align 8
  %347 = getelementptr inbounds %struct.quad, %struct.quad* %346, i32 0, i32 3
  %348 = load %struct.centroid*, %struct.centroid** %347, align 8
  %349 = getelementptr inbounds %struct.centroid, %struct.centroid* %348, i32 0, i32 2
  %350 = load float, float* %349, align 4
  %351 = call i32 @compare_float(float %350, float 2.000000e+00)
  %352 = icmp ne i32 %351, 0
  br i1 %352, label %353, label %354

353:                                              ; preds = %343
  store i32 1, i32* %9, align 4
  br label %354

354:                                              ; preds = %353, %343, %333, %319
  %355 = load %struct.qtree*, %struct.qtree** %18, align 8
  %356 = getelementptr inbounds %struct.qtree, %struct.qtree* %355, i32 0, i32 1
  %357 = load %struct.qtree*, %struct.qtree** %356, align 8
  %358 = getelementptr inbounds %struct.qtree, %struct.qtree* %357, i32 0, i32 0
  %359 = load %struct.quad*, %struct.quad** %358, align 8
  %360 = getelementptr inbounds %struct.quad, %struct.quad* %359, i32 0, i32 3
  %361 = load %struct.centroid*, %struct.centroid** %360, align 8
  %362 = getelementptr inbounds %struct.centroid, %struct.centroid* %361, i32 0, i32 0
  %363 = load float, float* %362, align 4
  %364 = call i32 @compare_float(float %363, float 0x3FB99999A0000000)
  %365 = icmp ne i32 %364, 0
  br i1 %365, label %366, label %391

366:                                              ; preds = %354
  %367 = load %struct.qtree*, %struct.qtree** %18, align 8
  %368 = getelementptr inbounds %struct.qtree, %struct.qtree* %367, i32 0, i32 1
  %369 = load %struct.qtree*, %struct.qtree** %368, align 8
  %370 = getelementptr inbounds %struct.qtree, %struct.qtree* %369, i32 0, i32 0
  %371 = load %struct.quad*, %struct.quad** %370, align 8
  %372 = getelementptr inbounds %struct.quad, %struct.quad* %371, i32 0, i32 3
  %373 = load %struct.centroid*, %struct.centroid** %372, align 8
  %374 = getelementptr inbounds %struct.centroid, %struct.centroid* %373, i32 0, i32 1
  %375 = load float, float* %374, align 4
  %376 = call i32 @compare_float(float %375, float 0x3FB99999A0000000)
  %377 = icmp ne i32 %376, 0
  br i1 %377, label %378, label %391

378:                                              ; preds = %366
  %379 = load %struct.qtree*, %struct.qtree** %18, align 8
  %380 = getelementptr inbounds %struct.qtree, %struct.qtree* %379, i32 0, i32 1
  %381 = load %struct.qtree*, %struct.qtree** %380, align 8
  %382 = getelementptr inbounds %struct.qtree, %struct.qtree* %381, i32 0, i32 0
  %383 = load %struct.quad*, %struct.quad** %382, align 8
  %384 = getelementptr inbounds %struct.quad, %struct.quad* %383, i32 0, i32 3
  %385 = load %struct.centroid*, %struct.centroid** %384, align 8
  %386 = getelementptr inbounds %struct.centroid, %struct.centroid* %385, i32 0, i32 2
  %387 = load float, float* %386, align 4
  %388 = call i32 @compare_float(float %387, float 2.000000e+00)
  %389 = icmp ne i32 %388, 0
  br i1 %389, label %390, label %391

390:                                              ; preds = %378
  store i32 1, i32* %10, align 4
  br label %391

391:                                              ; preds = %390, %378, %366, %354
  %392 = load %struct.qtree*, %struct.qtree** %18, align 8
  %393 = getelementptr inbounds %struct.qtree, %struct.qtree* %392, i32 0, i32 1
  %394 = load %struct.qtree*, %struct.qtree** %393, align 8
  %395 = getelementptr inbounds %struct.qtree, %struct.qtree* %394, i32 0, i32 1
  %396 = load %struct.qtree*, %struct.qtree** %395, align 8
  %397 = getelementptr inbounds %struct.qtree, %struct.qtree* %396, i32 0, i32 0
  %398 = load %struct.quad*, %struct.quad** %397, align 8
  %399 = getelementptr inbounds %struct.quad, %struct.quad* %398, i32 0, i32 3
  %400 = load %struct.centroid*, %struct.centroid** %399, align 8
  %401 = getelementptr inbounds %struct.centroid, %struct.centroid* %400, i32 0, i32 0
  %402 = load float, float* %401, align 4
  %403 = call i32 @compare_float(float %402, float 0x3FB99999A0000000)
  %404 = icmp ne i32 %403, 0
  br i1 %404, label %405, label %434

405:                                              ; preds = %391
  %406 = load %struct.qtree*, %struct.qtree** %18, align 8
  %407 = getelementptr inbounds %struct.qtree, %struct.qtree* %406, i32 0, i32 1
  %408 = load %struct.qtree*, %struct.qtree** %407, align 8
  %409 = getelementptr inbounds %struct.qtree, %struct.qtree* %408, i32 0, i32 1
  %410 = load %struct.qtree*, %struct.qtree** %409, align 8
  %411 = getelementptr inbounds %struct.qtree, %struct.qtree* %410, i32 0, i32 0
  %412 = load %struct.quad*, %struct.quad** %411, align 8
  %413 = getelementptr inbounds %struct.quad, %struct.quad* %412, i32 0, i32 3
  %414 = load %struct.centroid*, %struct.centroid** %413, align 8
  %415 = getelementptr inbounds %struct.centroid, %struct.centroid* %414, i32 0, i32 1
  %416 = load float, float* %415, align 4
  %417 = call i32 @compare_float(float %416, float 0x3FB99999A0000000)
  %418 = icmp ne i32 %417, 0
  br i1 %418, label %419, label %434

419:                                              ; preds = %405
  %420 = load %struct.qtree*, %struct.qtree** %18, align 8
  %421 = getelementptr inbounds %struct.qtree, %struct.qtree* %420, i32 0, i32 1
  %422 = load %struct.qtree*, %struct.qtree** %421, align 8
  %423 = getelementptr inbounds %struct.qtree, %struct.qtree* %422, i32 0, i32 1
  %424 = load %struct.qtree*, %struct.qtree** %423, align 8
  %425 = getelementptr inbounds %struct.qtree, %struct.qtree* %424, i32 0, i32 0
  %426 = load %struct.quad*, %struct.quad** %425, align 8
  %427 = getelementptr inbounds %struct.quad, %struct.quad* %426, i32 0, i32 3
  %428 = load %struct.centroid*, %struct.centroid** %427, align 8
  %429 = getelementptr inbounds %struct.centroid, %struct.centroid* %428, i32 0, i32 2
  %430 = load float, float* %429, align 4
  %431 = call i32 @compare_float(float %430, float 2.000000e+00)
  %432 = icmp ne i32 %431, 0
  br i1 %432, label %433, label %434

433:                                              ; preds = %419
  store i32 1, i32* %11, align 4
  br label %434

434:                                              ; preds = %433, %419, %405, %391
  %435 = load %struct.qtree*, %struct.qtree** %18, align 8
  %436 = getelementptr inbounds %struct.qtree, %struct.qtree* %435, i32 0, i32 1
  %437 = load %struct.qtree*, %struct.qtree** %436, align 8
  %438 = getelementptr inbounds %struct.qtree, %struct.qtree* %437, i32 0, i32 1
  %439 = load %struct.qtree*, %struct.qtree** %438, align 8
  %440 = getelementptr inbounds %struct.qtree, %struct.qtree* %439, i32 0, i32 1
  %441 = load %struct.qtree*, %struct.qtree** %440, align 8
  %442 = getelementptr inbounds %struct.qtree, %struct.qtree* %441, i32 0, i32 0
  %443 = load %struct.quad*, %struct.quad** %442, align 8
  %444 = getelementptr inbounds %struct.quad, %struct.quad* %443, i32 0, i32 3
  %445 = load %struct.centroid*, %struct.centroid** %444, align 8
  %446 = getelementptr inbounds %struct.centroid, %struct.centroid* %445, i32 0, i32 0
  %447 = load float, float* %446, align 4
  %448 = call i32 @compare_float(float %447, float 0x3FB99999A0000000)
  %449 = icmp ne i32 %448, 0
  br i1 %449, label %450, label %483

450:                                              ; preds = %434
  %451 = load %struct.qtree*, %struct.qtree** %18, align 8
  %452 = getelementptr inbounds %struct.qtree, %struct.qtree* %451, i32 0, i32 1
  %453 = load %struct.qtree*, %struct.qtree** %452, align 8
  %454 = getelementptr inbounds %struct.qtree, %struct.qtree* %453, i32 0, i32 1
  %455 = load %struct.qtree*, %struct.qtree** %454, align 8
  %456 = getelementptr inbounds %struct.qtree, %struct.qtree* %455, i32 0, i32 1
  %457 = load %struct.qtree*, %struct.qtree** %456, align 8
  %458 = getelementptr inbounds %struct.qtree, %struct.qtree* %457, i32 0, i32 0
  %459 = load %struct.quad*, %struct.quad** %458, align 8
  %460 = getelementptr inbounds %struct.quad, %struct.quad* %459, i32 0, i32 3
  %461 = load %struct.centroid*, %struct.centroid** %460, align 8
  %462 = getelementptr inbounds %struct.centroid, %struct.centroid* %461, i32 0, i32 1
  %463 = load float, float* %462, align 4
  %464 = call i32 @compare_float(float %463, float 0x3FB99999A0000000)
  %465 = icmp ne i32 %464, 0
  br i1 %465, label %466, label %483

466:                                              ; preds = %450
  %467 = load %struct.qtree*, %struct.qtree** %18, align 8
  %468 = getelementptr inbounds %struct.qtree, %struct.qtree* %467, i32 0, i32 1
  %469 = load %struct.qtree*, %struct.qtree** %468, align 8
  %470 = getelementptr inbounds %struct.qtree, %struct.qtree* %469, i32 0, i32 1
  %471 = load %struct.qtree*, %struct.qtree** %470, align 8
  %472 = getelementptr inbounds %struct.qtree, %struct.qtree* %471, i32 0, i32 1
  %473 = load %struct.qtree*, %struct.qtree** %472, align 8
  %474 = getelementptr inbounds %struct.qtree, %struct.qtree* %473, i32 0, i32 0
  %475 = load %struct.quad*, %struct.quad** %474, align 8
  %476 = getelementptr inbounds %struct.quad, %struct.quad* %475, i32 0, i32 3
  %477 = load %struct.centroid*, %struct.centroid** %476, align 8
  %478 = getelementptr inbounds %struct.centroid, %struct.centroid* %477, i32 0, i32 2
  %479 = load float, float* %478, align 4
  %480 = call i32 @compare_float(float %479, float 2.000000e+00)
  %481 = icmp ne i32 %480, 0
  br i1 %481, label %482, label %483

482:                                              ; preds = %466
  store i32 1, i32* %12, align 4
  br label %483

483:                                              ; preds = %482, %466, %450, %434
  %484 = load %struct.qtree*, %struct.qtree** %18, align 8
  %485 = getelementptr inbounds %struct.qtree, %struct.qtree* %484, i32 0, i32 1
  %486 = load %struct.qtree*, %struct.qtree** %485, align 8
  %487 = getelementptr inbounds %struct.qtree, %struct.qtree* %486, i32 0, i32 1
  %488 = load %struct.qtree*, %struct.qtree** %487, align 8
  %489 = getelementptr inbounds %struct.qtree, %struct.qtree* %488, i32 0, i32 1
  %490 = load %struct.qtree*, %struct.qtree** %489, align 8
  %491 = getelementptr inbounds %struct.qtree, %struct.qtree* %490, i32 0, i32 1
  %492 = load %struct.qtree*, %struct.qtree** %491, align 8
  %493 = getelementptr inbounds %struct.qtree, %struct.qtree* %492, i32 0, i32 0
  %494 = load %struct.quad*, %struct.quad** %493, align 8
  %495 = getelementptr inbounds %struct.quad, %struct.quad* %494, i32 0, i32 3
  %496 = load %struct.centroid*, %struct.centroid** %495, align 8
  %497 = getelementptr inbounds %struct.centroid, %struct.centroid* %496, i32 0, i32 0
  %498 = load float, float* %497, align 4
  %499 = call i32 @compare_float(float %498, float 0x3FB99999A0000000)
  %500 = icmp ne i32 %499, 0
  br i1 %500, label %501, label %538

501:                                              ; preds = %483
  %502 = load %struct.qtree*, %struct.qtree** %18, align 8
  %503 = getelementptr inbounds %struct.qtree, %struct.qtree* %502, i32 0, i32 1
  %504 = load %struct.qtree*, %struct.qtree** %503, align 8
  %505 = getelementptr inbounds %struct.qtree, %struct.qtree* %504, i32 0, i32 1
  %506 = load %struct.qtree*, %struct.qtree** %505, align 8
  %507 = getelementptr inbounds %struct.qtree, %struct.qtree* %506, i32 0, i32 1
  %508 = load %struct.qtree*, %struct.qtree** %507, align 8
  %509 = getelementptr inbounds %struct.qtree, %struct.qtree* %508, i32 0, i32 1
  %510 = load %struct.qtree*, %struct.qtree** %509, align 8
  %511 = getelementptr inbounds %struct.qtree, %struct.qtree* %510, i32 0, i32 0
  %512 = load %struct.quad*, %struct.quad** %511, align 8
  %513 = getelementptr inbounds %struct.quad, %struct.quad* %512, i32 0, i32 3
  %514 = load %struct.centroid*, %struct.centroid** %513, align 8
  %515 = getelementptr inbounds %struct.centroid, %struct.centroid* %514, i32 0, i32 1
  %516 = load float, float* %515, align 4
  %517 = call i32 @compare_float(float %516, float 0x3FB99999A0000000)
  %518 = icmp ne i32 %517, 0
  br i1 %518, label %519, label %538

519:                                              ; preds = %501
  %520 = load %struct.qtree*, %struct.qtree** %18, align 8
  %521 = getelementptr inbounds %struct.qtree, %struct.qtree* %520, i32 0, i32 1
  %522 = load %struct.qtree*, %struct.qtree** %521, align 8
  %523 = getelementptr inbounds %struct.qtree, %struct.qtree* %522, i32 0, i32 1
  %524 = load %struct.qtree*, %struct.qtree** %523, align 8
  %525 = getelementptr inbounds %struct.qtree, %struct.qtree* %524, i32 0, i32 1
  %526 = load %struct.qtree*, %struct.qtree** %525, align 8
  %527 = getelementptr inbounds %struct.qtree, %struct.qtree* %526, i32 0, i32 1
  %528 = load %struct.qtree*, %struct.qtree** %527, align 8
  %529 = getelementptr inbounds %struct.qtree, %struct.qtree* %528, i32 0, i32 0
  %530 = load %struct.quad*, %struct.quad** %529, align 8
  %531 = getelementptr inbounds %struct.quad, %struct.quad* %530, i32 0, i32 3
  %532 = load %struct.centroid*, %struct.centroid** %531, align 8
  %533 = getelementptr inbounds %struct.centroid, %struct.centroid* %532, i32 0, i32 2
  %534 = load float, float* %533, align 4
  %535 = call i32 @compare_float(float %534, float 2.000000e+00)
  %536 = icmp ne i32 %535, 0
  br i1 %536, label %537, label %538

537:                                              ; preds = %519
  store i32 1, i32* %13, align 4
  br label %538

538:                                              ; preds = %537, %519, %501, %483
  %539 = load %struct.qtree*, %struct.qtree** %18, align 8
  %540 = getelementptr inbounds %struct.qtree, %struct.qtree* %539, i32 0, i32 1
  %541 = load %struct.qtree*, %struct.qtree** %540, align 8
  %542 = getelementptr inbounds %struct.qtree, %struct.qtree* %541, i32 0, i32 1
  %543 = load %struct.qtree*, %struct.qtree** %542, align 8
  %544 = getelementptr inbounds %struct.qtree, %struct.qtree* %543, i32 0, i32 1
  %545 = load %struct.qtree*, %struct.qtree** %544, align 8
  %546 = getelementptr inbounds %struct.qtree, %struct.qtree* %545, i32 0, i32 1
  %547 = load %struct.qtree*, %struct.qtree** %546, align 8
  %548 = getelementptr inbounds %struct.qtree, %struct.qtree* %547, i32 0, i32 1
  %549 = load %struct.qtree*, %struct.qtree** %548, align 8
  %550 = getelementptr inbounds %struct.qtree, %struct.qtree* %549, i32 0, i32 0
  %551 = load %struct.quad*, %struct.quad** %550, align 8
  %552 = getelementptr inbounds %struct.quad, %struct.quad* %551, i32 0, i32 3
  %553 = load %struct.centroid*, %struct.centroid** %552, align 8
  %554 = getelementptr inbounds %struct.centroid, %struct.centroid* %553, i32 0, i32 0
  %555 = load float, float* %554, align 4
  %556 = call i32 @compare_float(float %555, float 0.000000e+00)
  %557 = icmp ne i32 %556, 0
  br i1 %557, label %558, label %599

558:                                              ; preds = %538
  %559 = load %struct.qtree*, %struct.qtree** %18, align 8
  %560 = getelementptr inbounds %struct.qtree, %struct.qtree* %559, i32 0, i32 1
  %561 = load %struct.qtree*, %struct.qtree** %560, align 8
  %562 = getelementptr inbounds %struct.qtree, %struct.qtree* %561, i32 0, i32 1
  %563 = load %struct.qtree*, %struct.qtree** %562, align 8
  %564 = getelementptr inbounds %struct.qtree, %struct.qtree* %563, i32 0, i32 1
  %565 = load %struct.qtree*, %struct.qtree** %564, align 8
  %566 = getelementptr inbounds %struct.qtree, %struct.qtree* %565, i32 0, i32 1
  %567 = load %struct.qtree*, %struct.qtree** %566, align 8
  %568 = getelementptr inbounds %struct.qtree, %struct.qtree* %567, i32 0, i32 1
  %569 = load %struct.qtree*, %struct.qtree** %568, align 8
  %570 = getelementptr inbounds %struct.qtree, %struct.qtree* %569, i32 0, i32 0
  %571 = load %struct.quad*, %struct.quad** %570, align 8
  %572 = getelementptr inbounds %struct.quad, %struct.quad* %571, i32 0, i32 3
  %573 = load %struct.centroid*, %struct.centroid** %572, align 8
  %574 = getelementptr inbounds %struct.centroid, %struct.centroid* %573, i32 0, i32 1
  %575 = load float, float* %574, align 4
  %576 = call i32 @compare_float(float %575, float 0.000000e+00)
  %577 = icmp ne i32 %576, 0
  br i1 %577, label %578, label %599

578:                                              ; preds = %558
  %579 = load %struct.qtree*, %struct.qtree** %18, align 8
  %580 = getelementptr inbounds %struct.qtree, %struct.qtree* %579, i32 0, i32 1
  %581 = load %struct.qtree*, %struct.qtree** %580, align 8
  %582 = getelementptr inbounds %struct.qtree, %struct.qtree* %581, i32 0, i32 1
  %583 = load %struct.qtree*, %struct.qtree** %582, align 8
  %584 = getelementptr inbounds %struct.qtree, %struct.qtree* %583, i32 0, i32 1
  %585 = load %struct.qtree*, %struct.qtree** %584, align 8
  %586 = getelementptr inbounds %struct.qtree, %struct.qtree* %585, i32 0, i32 1
  %587 = load %struct.qtree*, %struct.qtree** %586, align 8
  %588 = getelementptr inbounds %struct.qtree, %struct.qtree* %587, i32 0, i32 1
  %589 = load %struct.qtree*, %struct.qtree** %588, align 8
  %590 = getelementptr inbounds %struct.qtree, %struct.qtree* %589, i32 0, i32 0
  %591 = load %struct.quad*, %struct.quad** %590, align 8
  %592 = getelementptr inbounds %struct.quad, %struct.quad* %591, i32 0, i32 3
  %593 = load %struct.centroid*, %struct.centroid** %592, align 8
  %594 = getelementptr inbounds %struct.centroid, %struct.centroid* %593, i32 0, i32 2
  %595 = load float, float* %594, align 4
  %596 = call i32 @compare_float(float %595, float 1.000000e+00)
  %597 = icmp ne i32 %596, 0
  br i1 %597, label %598, label %599

598:                                              ; preds = %578
  store i32 1, i32* %14, align 4
  br label %599

599:                                              ; preds = %598, %578, %558, %538
  %600 = load %struct.qtree*, %struct.qtree** %18, align 8
  %601 = getelementptr inbounds %struct.qtree, %struct.qtree* %600, i32 0, i32 1
  %602 = load %struct.qtree*, %struct.qtree** %601, align 8
  %603 = getelementptr inbounds %struct.qtree, %struct.qtree* %602, i32 0, i32 1
  %604 = load %struct.qtree*, %struct.qtree** %603, align 8
  %605 = getelementptr inbounds %struct.qtree, %struct.qtree* %604, i32 0, i32 1
  %606 = load %struct.qtree*, %struct.qtree** %605, align 8
  %607 = getelementptr inbounds %struct.qtree, %struct.qtree* %606, i32 0, i32 1
  %608 = load %struct.qtree*, %struct.qtree** %607, align 8
  %609 = getelementptr inbounds %struct.qtree, %struct.qtree* %608, i32 0, i32 4
  %610 = load %struct.qtree*, %struct.qtree** %609, align 8
  %611 = getelementptr inbounds %struct.qtree, %struct.qtree* %610, i32 0, i32 0
  %612 = load %struct.quad*, %struct.quad** %611, align 8
  %613 = getelementptr inbounds %struct.quad, %struct.quad* %612, i32 0, i32 3
  %614 = load %struct.centroid*, %struct.centroid** %613, align 8
  %615 = getelementptr inbounds %struct.centroid, %struct.centroid* %614, i32 0, i32 0
  %616 = load float, float* %615, align 4
  %617 = call i32 @compare_float(float %616, float 0x3FC99999A0000000)
  %618 = icmp ne i32 %617, 0
  br i1 %618, label %619, label %660

619:                                              ; preds = %599
  %620 = load %struct.qtree*, %struct.qtree** %18, align 8
  %621 = getelementptr inbounds %struct.qtree, %struct.qtree* %620, i32 0, i32 1
  %622 = load %struct.qtree*, %struct.qtree** %621, align 8
  %623 = getelementptr inbounds %struct.qtree, %struct.qtree* %622, i32 0, i32 1
  %624 = load %struct.qtree*, %struct.qtree** %623, align 8
  %625 = getelementptr inbounds %struct.qtree, %struct.qtree* %624, i32 0, i32 1
  %626 = load %struct.qtree*, %struct.qtree** %625, align 8
  %627 = getelementptr inbounds %struct.qtree, %struct.qtree* %626, i32 0, i32 1
  %628 = load %struct.qtree*, %struct.qtree** %627, align 8
  %629 = getelementptr inbounds %struct.qtree, %struct.qtree* %628, i32 0, i32 4
  %630 = load %struct.qtree*, %struct.qtree** %629, align 8
  %631 = getelementptr inbounds %struct.qtree, %struct.qtree* %630, i32 0, i32 0
  %632 = load %struct.quad*, %struct.quad** %631, align 8
  %633 = getelementptr inbounds %struct.quad, %struct.quad* %632, i32 0, i32 3
  %634 = load %struct.centroid*, %struct.centroid** %633, align 8
  %635 = getelementptr inbounds %struct.centroid, %struct.centroid* %634, i32 0, i32 1
  %636 = load float, float* %635, align 4
  %637 = call i32 @compare_float(float %636, float 0x3FC99999A0000000)
  %638 = icmp ne i32 %637, 0
  br i1 %638, label %639, label %660

639:                                              ; preds = %619
  %640 = load %struct.qtree*, %struct.qtree** %18, align 8
  %641 = getelementptr inbounds %struct.qtree, %struct.qtree* %640, i32 0, i32 1
  %642 = load %struct.qtree*, %struct.qtree** %641, align 8
  %643 = getelementptr inbounds %struct.qtree, %struct.qtree* %642, i32 0, i32 1
  %644 = load %struct.qtree*, %struct.qtree** %643, align 8
  %645 = getelementptr inbounds %struct.qtree, %struct.qtree* %644, i32 0, i32 1
  %646 = load %struct.qtree*, %struct.qtree** %645, align 8
  %647 = getelementptr inbounds %struct.qtree, %struct.qtree* %646, i32 0, i32 1
  %648 = load %struct.qtree*, %struct.qtree** %647, align 8
  %649 = getelementptr inbounds %struct.qtree, %struct.qtree* %648, i32 0, i32 4
  %650 = load %struct.qtree*, %struct.qtree** %649, align 8
  %651 = getelementptr inbounds %struct.qtree, %struct.qtree* %650, i32 0, i32 0
  %652 = load %struct.quad*, %struct.quad** %651, align 8
  %653 = getelementptr inbounds %struct.quad, %struct.quad* %652, i32 0, i32 3
  %654 = load %struct.centroid*, %struct.centroid** %653, align 8
  %655 = getelementptr inbounds %struct.centroid, %struct.centroid* %654, i32 0, i32 2
  %656 = load float, float* %655, align 4
  %657 = call i32 @compare_float(float %656, float 1.000000e+00)
  %658 = icmp ne i32 %657, 0
  br i1 %658, label %659, label %660

659:                                              ; preds = %639
  store i32 1, i32* %15, align 4
  br label %660

660:                                              ; preds = %659, %639, %619, %599
  store i32 0, i32* %19, align 4
  %661 = load i32, i32* %1, align 4
  %662 = icmp ne i32 %661, 0
  br i1 %662, label %663, label %706

663:                                              ; preds = %660
  %664 = load i32, i32* %2, align 4
  %665 = icmp ne i32 %664, 0
  br i1 %665, label %666, label %706

666:                                              ; preds = %663
  %667 = load i32, i32* %3, align 4
  %668 = icmp ne i32 %667, 0
  br i1 %668, label %669, label %706

669:                                              ; preds = %666
  %670 = load i32, i32* %4, align 4
  %671 = icmp ne i32 %670, 0
  br i1 %671, label %672, label %706

672:                                              ; preds = %669
  %673 = load i32, i32* %5, align 4
  %674 = icmp ne i32 %673, 0
  br i1 %674, label %675, label %706

675:                                              ; preds = %672
  %676 = load i32, i32* %6, align 4
  %677 = icmp ne i32 %676, 0
  br i1 %677, label %678, label %706

678:                                              ; preds = %675
  %679 = load i32, i32* %7, align 4
  %680 = icmp ne i32 %679, 0
  br i1 %680, label %681, label %706

681:                                              ; preds = %678
  %682 = load i32, i32* %8, align 4
  %683 = icmp ne i32 %682, 0
  br i1 %683, label %684, label %706

684:                                              ; preds = %681
  %685 = load i32, i32* %9, align 4
  %686 = icmp ne i32 %685, 0
  br i1 %686, label %687, label %706

687:                                              ; preds = %684
  %688 = load i32, i32* %10, align 4
  %689 = icmp ne i32 %688, 0
  br i1 %689, label %690, label %706

690:                                              ; preds = %687
  %691 = load i32, i32* %11, align 4
  %692 = icmp ne i32 %691, 0
  br i1 %692, label %693, label %706

693:                                              ; preds = %690
  %694 = load i32, i32* %12, align 4
  %695 = icmp ne i32 %694, 0
  br i1 %695, label %696, label %706

696:                                              ; preds = %693
  %697 = load i32, i32* %13, align 4
  %698 = icmp ne i32 %697, 0
  br i1 %698, label %699, label %706

699:                                              ; preds = %696
  %700 = load i32, i32* %14, align 4
  %701 = icmp ne i32 %700, 0
  br i1 %701, label %702, label %706

702:                                              ; preds = %699
  %703 = load i32, i32* %15, align 4
  %704 = icmp ne i32 %703, 0
  br i1 %704, label %705, label %706

705:                                              ; preds = %702
  store i32 1, i32* %19, align 4
  br label %706

706:                                              ; preds = %705, %702, %699, %696, %693, %690, %687, %684, %681, %678, %675, %672, %669, %666, %663, %660
  %707 = load i32, i32* %19, align 4
  ret i32 %707
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main(i32 %0, i8** %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca i32, align 4
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  %7 = call i32 @body()
  store i32 %7, i32* %6, align 4
  %8 = call i32 @body()
  ret i32 %8
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { allocsize(0) }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 1]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple clang version 12.0.0 (clang-1200.0.32.29)"}

; Disabled due to unsupported operations
; DISABLED EQ: i32 1 = call i32 @main()