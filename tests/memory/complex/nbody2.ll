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
  %9 = load %struct.quad*, %struct.quad** %7, align 8
  %10 = getelementptr inbounds %struct.quad, %struct.quad* %9, i32 0, i32 1
  %11 = load float, float* %10, align 4
  %12 = load %struct.quad*, %struct.quad** %7, align 8
  %13 = getelementptr inbounds %struct.quad, %struct.quad* %12, i32 0, i32 0
  %14 = load float, float* %13, align 8
  %15 = fdiv float %14, 2.000000e+00
  %16 = fadd float %11, %15
  %17 = fcmp ole float %8, %16
  br i1 %17, label %18, label %30

18:                                               ; preds = %3
  %19 = load float, float* %6, align 4
  %20 = load %struct.quad*, %struct.quad** %7, align 8
  %21 = getelementptr inbounds %struct.quad, %struct.quad* %20, i32 0, i32 2
  %22 = load float, float* %21, align 8
  %23 = load %struct.quad*, %struct.quad** %7, align 8
  %24 = getelementptr inbounds %struct.quad, %struct.quad* %23, i32 0, i32 0
  %25 = load float, float* %24, align 8
  %26 = fdiv float %25, 2.000000e+00
  %27 = fadd float %22, %26
  %28 = fcmp olt float %19, %27
  br i1 %28, label %29, label %30

29:                                               ; preds = %18
  store i32 1, i32* %4, align 4
  br label %77

30:                                               ; preds = %18, %3
  %31 = load float, float* %5, align 4
  %32 = load %struct.quad*, %struct.quad** %7, align 8
  %33 = getelementptr inbounds %struct.quad, %struct.quad* %32, i32 0, i32 1
  %34 = load float, float* %33, align 4
  %35 = load %struct.quad*, %struct.quad** %7, align 8
  %36 = getelementptr inbounds %struct.quad, %struct.quad* %35, i32 0, i32 0
  %37 = load float, float* %36, align 8
  %38 = fdiv float %37, 2.000000e+00
  %39 = fadd float %34, %38
  %40 = fcmp ogt float %31, %39
  br i1 %40, label %41, label %53

41:                                               ; preds = %30
  %42 = load float, float* %6, align 4
  %43 = load %struct.quad*, %struct.quad** %7, align 8
  %44 = getelementptr inbounds %struct.quad, %struct.quad* %43, i32 0, i32 2
  %45 = load float, float* %44, align 8
  %46 = load %struct.quad*, %struct.quad** %7, align 8
  %47 = getelementptr inbounds %struct.quad, %struct.quad* %46, i32 0, i32 0
  %48 = load float, float* %47, align 8
  %49 = fdiv float %48, 2.000000e+00
  %50 = fadd float %45, %49
  %51 = fcmp olt float %42, %50
  br i1 %51, label %52, label %53

52:                                               ; preds = %41
  store i32 2, i32* %4, align 4
  br label %77

53:                                               ; preds = %41, %30
  %54 = load float, float* %5, align 4
  %55 = load %struct.quad*, %struct.quad** %7, align 8
  %56 = getelementptr inbounds %struct.quad, %struct.quad* %55, i32 0, i32 1
  %57 = load float, float* %56, align 4
  %58 = load %struct.quad*, %struct.quad** %7, align 8
  %59 = getelementptr inbounds %struct.quad, %struct.quad* %58, i32 0, i32 0
  %60 = load float, float* %59, align 8
  %61 = fdiv float %60, 2.000000e+00
  %62 = fadd float %57, %61
  %63 = fcmp ole float %54, %62
  br i1 %63, label %64, label %76

64:                                               ; preds = %53
  %65 = load float, float* %6, align 4
  %66 = load %struct.quad*, %struct.quad** %7, align 8
  %67 = getelementptr inbounds %struct.quad, %struct.quad* %66, i32 0, i32 2
  %68 = load float, float* %67, align 8
  %69 = load %struct.quad*, %struct.quad** %7, align 8
  %70 = getelementptr inbounds %struct.quad, %struct.quad* %69, i32 0, i32 0
  %71 = load float, float* %70, align 8
  %72 = fdiv float %71, 2.000000e+00
  %73 = fadd float %68, %72
  %74 = fcmp oge float %65, %73
  br i1 %74, label %75, label %76

75:                                               ; preds = %64
  store i32 3, i32* %4, align 4
  br label %77

76:                                               ; preds = %64, %53
  store i32 4, i32* %4, align 4
  br label %77

77:                                               ; preds = %76, %75, %52, %29
  %78 = load i32, i32* %4, align 4
  ret i32 %78
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
  br label %76

14:                                               ; preds = %2
  %15 = load %struct.centroid*, %struct.centroid** %5, align 8
  %16 = icmp eq %struct.centroid* %15, null
  br i1 %16, label %17, label %19

17:                                               ; preds = %14
  %18 = load %struct.centroid*, %struct.centroid** %4, align 8
  store %struct.centroid* %18, %struct.centroid** %3, align 8
  br label %76

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
  %34 = fdiv float 1.000000e+00, %33
  %35 = load %struct.centroid*, %struct.centroid** %4, align 8
  %36 = getelementptr inbounds %struct.centroid, %struct.centroid* %35, i32 0, i32 2
  %37 = load float, float* %36, align 4
  %38 = load %struct.centroid*, %struct.centroid** %4, align 8
  %39 = getelementptr inbounds %struct.centroid, %struct.centroid* %38, i32 0, i32 0
  %40 = load float, float* %39, align 4
  %41 = fmul float %37, %40
  %42 = load %struct.centroid*, %struct.centroid** %5, align 8
  %43 = getelementptr inbounds %struct.centroid, %struct.centroid* %42, i32 0, i32 2
  %44 = load float, float* %43, align 4
  %45 = load %struct.centroid*, %struct.centroid** %5, align 8
  %46 = getelementptr inbounds %struct.centroid, %struct.centroid* %45, i32 0, i32 0
  %47 = load float, float* %46, align 4
  %48 = fmul float %44, %47
  %49 = fadd float %41, %48
  %50 = fmul float %34, %49
  store float %50, float* %8, align 4
  %51 = load float, float* %8, align 4
  %52 = load %struct.centroid*, %struct.centroid** %6, align 8
  %53 = getelementptr inbounds %struct.centroid, %struct.centroid* %52, i32 0, i32 0
  store float %51, float* %53, align 4
  %54 = load float, float* %7, align 4
  %55 = fdiv float 1.000000e+00, %54
  %56 = load %struct.centroid*, %struct.centroid** %4, align 8
  %57 = getelementptr inbounds %struct.centroid, %struct.centroid* %56, i32 0, i32 2
  %58 = load float, float* %57, align 4
  %59 = load %struct.centroid*, %struct.centroid** %4, align 8
  %60 = getelementptr inbounds %struct.centroid, %struct.centroid* %59, i32 0, i32 1
  %61 = load float, float* %60, align 4
  %62 = fmul float %58, %61
  %63 = load %struct.centroid*, %struct.centroid** %5, align 8
  %64 = getelementptr inbounds %struct.centroid, %struct.centroid* %63, i32 0, i32 2
  %65 = load float, float* %64, align 4
  %66 = load %struct.centroid*, %struct.centroid** %5, align 8
  %67 = getelementptr inbounds %struct.centroid, %struct.centroid* %66, i32 0, i32 1
  %68 = load float, float* %67, align 4
  %69 = fmul float %65, %68
  %70 = fadd float %62, %69
  %71 = fmul float %55, %70
  store float %71, float* %9, align 4
  %72 = load float, float* %9, align 4
  %73 = load %struct.centroid*, %struct.centroid** %6, align 8
  %74 = getelementptr inbounds %struct.centroid, %struct.centroid* %73, i32 0, i32 1
  store float %72, float* %74, align 4
  %75 = load %struct.centroid*, %struct.centroid** %6, align 8
  store %struct.centroid* %75, %struct.centroid** %3, align 8
  br label %76

76:                                               ; preds = %20, %17, %12
  %77 = load %struct.centroid*, %struct.centroid** %3, align 8
  ret %struct.centroid* %77
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
  br label %2109

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
  br label %2108

92:                                               ; preds = %66, %56
  %93 = load float, float* %5, align 4
  %94 = load float, float* %6, align 4
  %95 = load %struct.qtree*, %struct.qtree** %7, align 8
  %96 = getelementptr inbounds %struct.qtree, %struct.qtree* %95, i32 0, i32 0
  %97 = load %struct.quad*, %struct.quad** %96, align 8
  %98 = call i32 @which_quad(float %93, float %94, %struct.quad* %97)
  %99 = icmp eq i32 %98, 1
  br i1 %99, label %100, label %450

100:                                              ; preds = %92
  %101 = load %struct.qtree*, %struct.qtree** %7, align 8
  %102 = getelementptr inbounds %struct.qtree, %struct.qtree* %101, i32 0, i32 1
  %103 = load %struct.qtree*, %struct.qtree** %102, align 8
  %104 = icmp eq %struct.qtree* %103, null
  br i1 %104, label %105, label %450

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
  br i1 %298, label %299, label %318

299:                                              ; preds = %289
  %300 = load float, float* %5, align 4
  %301 = load float, float* %6, align 4
  %302 = load float, float* %8, align 4
  %303 = load float, float* %16, align 4
  %304 = fdiv float %303, 2.000000e+00
  %305 = load %struct.qtree*, %struct.qtree** %7, align 8
  %306 = getelementptr inbounds %struct.qtree, %struct.qtree* %305, i32 0, i32 0
  %307 = load %struct.quad*, %struct.quad** %306, align 8
  %308 = getelementptr inbounds %struct.quad, %struct.quad* %307, i32 0, i32 2
  %309 = load float, float* %308, align 8
  %310 = load %struct.qtree*, %struct.qtree** %7, align 8
  %311 = getelementptr inbounds %struct.qtree, %struct.qtree* %310, i32 0, i32 0
  %312 = load %struct.quad*, %struct.quad** %311, align 8
  %313 = getelementptr inbounds %struct.quad, %struct.quad* %312, i32 0, i32 1
  %314 = load float, float* %313, align 4
  %315 = call %struct.qtree* @empty_qtree(float %300, float %301, float %302, float %304, float %309, float %314)
  %316 = load %struct.qtree*, %struct.qtree** %7, align 8
  %317 = getelementptr inbounds %struct.qtree, %struct.qtree* %316, i32 0, i32 1
  store %struct.qtree* %315, %struct.qtree** %317, align 8
  br label %326

318:                                              ; preds = %289
  %319 = load float, float* %5, align 4
  %320 = load float, float* %6, align 4
  %321 = load %struct.qtree*, %struct.qtree** %7, align 8
  %322 = getelementptr inbounds %struct.qtree, %struct.qtree* %321, i32 0, i32 1
  %323 = load %struct.qtree*, %struct.qtree** %322, align 8
  %324 = load float, float* %8, align 4
  %325 = call %struct.qtree* @insertPoint(float %319, float %320, %struct.qtree* %323, float %324)
  br label %326

326:                                              ; preds = %318, %299
  %327 = load %struct.qtree*, %struct.qtree** %7, align 8
  %328 = getelementptr inbounds %struct.qtree, %struct.qtree* %327, i32 0, i32 2
  %329 = load %struct.qtree*, %struct.qtree** %328, align 8
  %330 = icmp ne %struct.qtree* %329, null
  br i1 %330, label %331, label %377

331:                                              ; preds = %326
  %332 = load %struct.qtree*, %struct.qtree** %7, align 8
  %333 = getelementptr inbounds %struct.qtree, %struct.qtree* %332, i32 0, i32 1
  %334 = load %struct.qtree*, %struct.qtree** %333, align 8
  %335 = getelementptr inbounds %struct.qtree, %struct.qtree* %334, i32 0, i32 0
  %336 = load %struct.quad*, %struct.quad** %335, align 8
  %337 = getelementptr inbounds %struct.quad, %struct.quad* %336, i32 0, i32 3
  %338 = load %struct.centroid*, %struct.centroid** %337, align 8
  %339 = load %struct.qtree*, %struct.qtree** %7, align 8
  %340 = getelementptr inbounds %struct.qtree, %struct.qtree* %339, i32 0, i32 2
  %341 = load %struct.qtree*, %struct.qtree** %340, align 8
  %342 = getelementptr inbounds %struct.qtree, %struct.qtree* %341, i32 0, i32 0
  %343 = load %struct.quad*, %struct.quad** %342, align 8
  %344 = getelementptr inbounds %struct.quad, %struct.quad* %343, i32 0, i32 3
  %345 = load %struct.centroid*, %struct.centroid** %344, align 8
  %346 = call %struct.centroid* @centroid_sum(%struct.centroid* %338, %struct.centroid* %345)
  store %struct.centroid* %346, %struct.centroid** %17, align 8
  %347 = load %struct.qtree*, %struct.qtree** %7, align 8
  %348 = getelementptr inbounds %struct.qtree, %struct.qtree* %347, i32 0, i32 4
  %349 = load %struct.qtree*, %struct.qtree** %348, align 8
  %350 = icmp ne %struct.qtree* %349, null
  br i1 %350, label %351, label %361

351:                                              ; preds = %331
  %352 = load %struct.centroid*, %struct.centroid** %17, align 8
  %353 = load %struct.qtree*, %struct.qtree** %7, align 8
  %354 = getelementptr inbounds %struct.qtree, %struct.qtree* %353, i32 0, i32 4
  %355 = load %struct.qtree*, %struct.qtree** %354, align 8
  %356 = getelementptr inbounds %struct.qtree, %struct.qtree* %355, i32 0, i32 0
  %357 = load %struct.quad*, %struct.quad** %356, align 8
  %358 = getelementptr inbounds %struct.quad, %struct.quad* %357, i32 0, i32 3
  %359 = load %struct.centroid*, %struct.centroid** %358, align 8
  %360 = call %struct.centroid* @centroid_sum(%struct.centroid* %352, %struct.centroid* %359)
  store %struct.centroid* %360, %struct.centroid** %17, align 8
  br label %361

361:                                              ; preds = %351, %331
  %362 = load %struct.qtree*, %struct.qtree** %7, align 8
  %363 = getelementptr inbounds %struct.qtree, %struct.qtree* %362, i32 0, i32 3
  %364 = load %struct.qtree*, %struct.qtree** %363, align 8
  %365 = icmp ne %struct.qtree* %364, null
  br i1 %365, label %366, label %376

366:                                              ; preds = %361
  %367 = load %struct.centroid*, %struct.centroid** %17, align 8
  %368 = load %struct.qtree*, %struct.qtree** %7, align 8
  %369 = getelementptr inbounds %struct.qtree, %struct.qtree* %368, i32 0, i32 3
  %370 = load %struct.qtree*, %struct.qtree** %369, align 8
  %371 = getelementptr inbounds %struct.qtree, %struct.qtree* %370, i32 0, i32 0
  %372 = load %struct.quad*, %struct.quad** %371, align 8
  %373 = getelementptr inbounds %struct.quad, %struct.quad* %372, i32 0, i32 3
  %374 = load %struct.centroid*, %struct.centroid** %373, align 8
  %375 = call %struct.centroid* @centroid_sum(%struct.centroid* %367, %struct.centroid* %374)
  store %struct.centroid* %375, %struct.centroid** %17, align 8
  br label %376

376:                                              ; preds = %366, %361
  br label %444

377:                                              ; preds = %326
  %378 = load %struct.qtree*, %struct.qtree** %7, align 8
  %379 = getelementptr inbounds %struct.qtree, %struct.qtree* %378, i32 0, i32 3
  %380 = load %struct.qtree*, %struct.qtree** %379, align 8
  %381 = icmp ne %struct.qtree* %380, null
  br i1 %381, label %382, label %413

382:                                              ; preds = %377
  %383 = load %struct.qtree*, %struct.qtree** %7, align 8
  %384 = getelementptr inbounds %struct.qtree, %struct.qtree* %383, i32 0, i32 1
  %385 = load %struct.qtree*, %struct.qtree** %384, align 8
  %386 = getelementptr inbounds %struct.qtree, %struct.qtree* %385, i32 0, i32 0
  %387 = load %struct.quad*, %struct.quad** %386, align 8
  %388 = getelementptr inbounds %struct.quad, %struct.quad* %387, i32 0, i32 3
  %389 = load %struct.centroid*, %struct.centroid** %388, align 8
  %390 = load %struct.qtree*, %struct.qtree** %7, align 8
  %391 = getelementptr inbounds %struct.qtree, %struct.qtree* %390, i32 0, i32 3
  %392 = load %struct.qtree*, %struct.qtree** %391, align 8
  %393 = getelementptr inbounds %struct.qtree, %struct.qtree* %392, i32 0, i32 0
  %394 = load %struct.quad*, %struct.quad** %393, align 8
  %395 = getelementptr inbounds %struct.quad, %struct.quad* %394, i32 0, i32 3
  %396 = load %struct.centroid*, %struct.centroid** %395, align 8
  %397 = call %struct.centroid* @centroid_sum(%struct.centroid* %389, %struct.centroid* %396)
  store %struct.centroid* %397, %struct.centroid** %17, align 8
  %398 = load %struct.qtree*, %struct.qtree** %7, align 8
  %399 = getelementptr inbounds %struct.qtree, %struct.qtree* %398, i32 0, i32 4
  %400 = load %struct.qtree*, %struct.qtree** %399, align 8
  %401 = icmp ne %struct.qtree* %400, null
  br i1 %401, label %402, label %412

402:                                              ; preds = %382
  %403 = load %struct.centroid*, %struct.centroid** %17, align 8
  %404 = load %struct.qtree*, %struct.qtree** %7, align 8
  %405 = getelementptr inbounds %struct.qtree, %struct.qtree* %404, i32 0, i32 4
  %406 = load %struct.qtree*, %struct.qtree** %405, align 8
  %407 = getelementptr inbounds %struct.qtree, %struct.qtree* %406, i32 0, i32 0
  %408 = load %struct.quad*, %struct.quad** %407, align 8
  %409 = getelementptr inbounds %struct.quad, %struct.quad* %408, i32 0, i32 3
  %410 = load %struct.centroid*, %struct.centroid** %409, align 8
  %411 = call %struct.centroid* @centroid_sum(%struct.centroid* %403, %struct.centroid* %410)
  store %struct.centroid* %411, %struct.centroid** %17, align 8
  br label %412

412:                                              ; preds = %402, %382
  br label %443

413:                                              ; preds = %377
  %414 = load %struct.qtree*, %struct.qtree** %7, align 8
  %415 = getelementptr inbounds %struct.qtree, %struct.qtree* %414, i32 0, i32 4
  %416 = load %struct.qtree*, %struct.qtree** %415, align 8
  %417 = icmp ne %struct.qtree* %416, null
  br i1 %417, label %418, label %434

418:                                              ; preds = %413
  %419 = load %struct.qtree*, %struct.qtree** %7, align 8
  %420 = getelementptr inbounds %struct.qtree, %struct.qtree* %419, i32 0, i32 1
  %421 = load %struct.qtree*, %struct.qtree** %420, align 8
  %422 = getelementptr inbounds %struct.qtree, %struct.qtree* %421, i32 0, i32 0
  %423 = load %struct.quad*, %struct.quad** %422, align 8
  %424 = getelementptr inbounds %struct.quad, %struct.quad* %423, i32 0, i32 3
  %425 = load %struct.centroid*, %struct.centroid** %424, align 8
  %426 = load %struct.qtree*, %struct.qtree** %7, align 8
  %427 = getelementptr inbounds %struct.qtree, %struct.qtree* %426, i32 0, i32 4
  %428 = load %struct.qtree*, %struct.qtree** %427, align 8
  %429 = getelementptr inbounds %struct.qtree, %struct.qtree* %428, i32 0, i32 0
  %430 = load %struct.quad*, %struct.quad** %429, align 8
  %431 = getelementptr inbounds %struct.quad, %struct.quad* %430, i32 0, i32 3
  %432 = load %struct.centroid*, %struct.centroid** %431, align 8
  %433 = call %struct.centroid* @centroid_sum(%struct.centroid* %425, %struct.centroid* %432)
  store %struct.centroid* %433, %struct.centroid** %17, align 8
  br label %442

434:                                              ; preds = %413
  %435 = load %struct.qtree*, %struct.qtree** %7, align 8
  %436 = getelementptr inbounds %struct.qtree, %struct.qtree* %435, i32 0, i32 1
  %437 = load %struct.qtree*, %struct.qtree** %436, align 8
  %438 = getelementptr inbounds %struct.qtree, %struct.qtree* %437, i32 0, i32 0
  %439 = load %struct.quad*, %struct.quad** %438, align 8
  %440 = getelementptr inbounds %struct.quad, %struct.quad* %439, i32 0, i32 3
  %441 = load %struct.centroid*, %struct.centroid** %440, align 8
  store %struct.centroid* %441, %struct.centroid** %17, align 8
  br label %442

442:                                              ; preds = %434, %418
  br label %443

443:                                              ; preds = %442, %412
  br label %444

444:                                              ; preds = %443, %376
  %445 = load %struct.centroid*, %struct.centroid** %17, align 8
  %446 = load %struct.qtree*, %struct.qtree** %7, align 8
  %447 = getelementptr inbounds %struct.qtree, %struct.qtree* %446, i32 0, i32 0
  %448 = load %struct.quad*, %struct.quad** %447, align 8
  %449 = getelementptr inbounds %struct.quad, %struct.quad* %448, i32 0, i32 3
  store %struct.centroid* %445, %struct.centroid** %449, align 8
  br label %2107

450:                                              ; preds = %100, %92
  %451 = load float, float* %5, align 4
  %452 = load float, float* %6, align 4
  %453 = load %struct.qtree*, %struct.qtree** %7, align 8
  %454 = getelementptr inbounds %struct.qtree, %struct.qtree* %453, i32 0, i32 0
  %455 = load %struct.quad*, %struct.quad** %454, align 8
  %456 = call i32 @which_quad(float %451, float %452, %struct.quad* %455)
  %457 = icmp eq i32 %456, 2
  br i1 %457, label %458, label %811

458:                                              ; preds = %450
  %459 = load %struct.qtree*, %struct.qtree** %7, align 8
  %460 = getelementptr inbounds %struct.qtree, %struct.qtree* %459, i32 0, i32 2
  %461 = load %struct.qtree*, %struct.qtree** %460, align 8
  %462 = icmp eq %struct.qtree* %461, null
  br i1 %462, label %463, label %811

463:                                              ; preds = %458
  %464 = load %struct.qtree*, %struct.qtree** %7, align 8
  %465 = getelementptr inbounds %struct.qtree, %struct.qtree* %464, i32 0, i32 1
  %466 = load %struct.qtree*, %struct.qtree** %465, align 8
  %467 = icmp eq %struct.qtree* %466, null
  br i1 %467, label %468, label %647

468:                                              ; preds = %463
  %469 = load %struct.qtree*, %struct.qtree** %7, align 8
  %470 = getelementptr inbounds %struct.qtree, %struct.qtree* %469, i32 0, i32 2
  %471 = load %struct.qtree*, %struct.qtree** %470, align 8
  %472 = icmp eq %struct.qtree* %471, null
  br i1 %472, label %473, label %647

473:                                              ; preds = %468
  %474 = load %struct.qtree*, %struct.qtree** %7, align 8
  %475 = getelementptr inbounds %struct.qtree, %struct.qtree* %474, i32 0, i32 3
  %476 = load %struct.qtree*, %struct.qtree** %475, align 8
  %477 = icmp eq %struct.qtree* %476, null
  br i1 %477, label %478, label %647

478:                                              ; preds = %473
  %479 = load %struct.qtree*, %struct.qtree** %7, align 8
  %480 = getelementptr inbounds %struct.qtree, %struct.qtree* %479, i32 0, i32 4
  %481 = load %struct.qtree*, %struct.qtree** %480, align 8
  %482 = icmp eq %struct.qtree* %481, null
  br i1 %482, label %483, label %647

483:                                              ; preds = %478
  %484 = load %struct.qtree*, %struct.qtree** %7, align 8
  %485 = getelementptr inbounds %struct.qtree, %struct.qtree* %484, i32 0, i32 0
  %486 = load %struct.quad*, %struct.quad** %485, align 8
  %487 = getelementptr inbounds %struct.quad, %struct.quad* %486, i32 0, i32 3
  %488 = load %struct.centroid*, %struct.centroid** %487, align 8
  %489 = getelementptr inbounds %struct.centroid, %struct.centroid* %488, i32 0, i32 0
  %490 = load float, float* %489, align 4
  store float %490, float* %18, align 4
  %491 = load %struct.qtree*, %struct.qtree** %7, align 8
  %492 = getelementptr inbounds %struct.qtree, %struct.qtree* %491, i32 0, i32 0
  %493 = load %struct.quad*, %struct.quad** %492, align 8
  %494 = getelementptr inbounds %struct.quad, %struct.quad* %493, i32 0, i32 3
  %495 = load %struct.centroid*, %struct.centroid** %494, align 8
  %496 = getelementptr inbounds %struct.centroid, %struct.centroid* %495, i32 0, i32 1
  %497 = load float, float* %496, align 4
  store float %497, float* %19, align 4
  %498 = load %struct.qtree*, %struct.qtree** %7, align 8
  %499 = getelementptr inbounds %struct.qtree, %struct.qtree* %498, i32 0, i32 0
  %500 = load %struct.quad*, %struct.quad** %499, align 8
  %501 = getelementptr inbounds %struct.quad, %struct.quad* %500, i32 0, i32 3
  %502 = load %struct.centroid*, %struct.centroid** %501, align 8
  %503 = getelementptr inbounds %struct.centroid, %struct.centroid* %502, i32 0, i32 2
  %504 = load float, float* %503, align 4
  store float %504, float* %20, align 4
  %505 = load float, float* %18, align 4
  %506 = load float, float* %19, align 4
  %507 = load %struct.qtree*, %struct.qtree** %7, align 8
  %508 = getelementptr inbounds %struct.qtree, %struct.qtree* %507, i32 0, i32 0
  %509 = load %struct.quad*, %struct.quad** %508, align 8
  %510 = call i32 @which_quad(float %505, float %506, %struct.quad* %509)
  %511 = sitofp i32 %510 to float
  store float %511, float* %21, align 4
  %512 = load float, float* %21, align 4
  %513 = fcmp oeq float %512, 1.000000e+00
  br i1 %513, label %514, label %538

514:                                              ; preds = %483
  %515 = load float, float* %18, align 4
  %516 = load float, float* %19, align 4
  %517 = load float, float* %20, align 4
  %518 = load %struct.qtree*, %struct.qtree** %7, align 8
  %519 = getelementptr inbounds %struct.qtree, %struct.qtree* %518, i32 0, i32 0
  %520 = load %struct.quad*, %struct.quad** %519, align 8
  %521 = getelementptr inbounds %struct.quad, %struct.quad* %520, i32 0, i32 0
  %522 = load float, float* %521, align 8
  %523 = fdiv float %522, 2.000000e+00
  %524 = load %struct.qtree*, %struct.qtree** %7, align 8
  %525 = getelementptr inbounds %struct.qtree, %struct.qtree* %524, i32 0, i32 0
  %526 = load %struct.quad*, %struct.quad** %525, align 8
  %527 = getelementptr inbounds %struct.quad, %struct.quad* %526, i32 0, i32 2
  %528 = load float, float* %527, align 8
  %529 = load %struct.qtree*, %struct.qtree** %7, align 8
  %530 = getelementptr inbounds %struct.qtree, %struct.qtree* %529, i32 0, i32 0
  %531 = load %struct.quad*, %struct.quad** %530, align 8
  %532 = getelementptr inbounds %struct.quad, %struct.quad* %531, i32 0, i32 1
  %533 = load float, float* %532, align 4
  %534 = call %struct.qtree* @empty_qtree(float %515, float %516, float %517, float %523, float %528, float %533)
  store %struct.qtree* %534, %struct.qtree** %22, align 8
  %535 = load %struct.qtree*, %struct.qtree** %22, align 8
  %536 = load %struct.qtree*, %struct.qtree** %7, align 8
  %537 = getelementptr inbounds %struct.qtree, %struct.qtree* %536, i32 0, i32 1
  store %struct.qtree* %535, %struct.qtree** %537, align 8
  br label %646

538:                                              ; preds = %483
  %539 = load float, float* %21, align 4
  %540 = fcmp oeq float %539, 3.000000e+00
  br i1 %540, label %541, label %572

541:                                              ; preds = %538
  %542 = load float, float* %18, align 4
  %543 = load float, float* %19, align 4
  %544 = load float, float* %20, align 4
  %545 = load %struct.qtree*, %struct.qtree** %7, align 8
  %546 = getelementptr inbounds %struct.qtree, %struct.qtree* %545, i32 0, i32 0
  %547 = load %struct.quad*, %struct.quad** %546, align 8
  %548 = getelementptr inbounds %struct.quad, %struct.quad* %547, i32 0, i32 0
  %549 = load float, float* %548, align 8
  %550 = fdiv float %549, 2.000000e+00
  %551 = load %struct.qtree*, %struct.qtree** %7, align 8
  %552 = getelementptr inbounds %struct.qtree, %struct.qtree* %551, i32 0, i32 0
  %553 = load %struct.quad*, %struct.quad** %552, align 8
  %554 = getelementptr inbounds %struct.quad, %struct.quad* %553, i32 0, i32 2
  %555 = load float, float* %554, align 8
  %556 = load %struct.qtree*, %struct.qtree** %7, align 8
  %557 = getelementptr inbounds %struct.qtree, %struct.qtree* %556, i32 0, i32 0
  %558 = load %struct.quad*, %struct.quad** %557, align 8
  %559 = getelementptr inbounds %struct.quad, %struct.quad* %558, i32 0, i32 0
  %560 = load float, float* %559, align 8
  %561 = fdiv float %560, 2.000000e+00
  %562 = fadd float %555, %561
  %563 = load %struct.qtree*, %struct.qtree** %7, align 8
  %564 = getelementptr inbounds %struct.qtree, %struct.qtree* %563, i32 0, i32 0
  %565 = load %struct.quad*, %struct.quad** %564, align 8
  %566 = getelementptr inbounds %struct.quad, %struct.quad* %565, i32 0, i32 1
  %567 = load float, float* %566, align 4
  %568 = call %struct.qtree* @empty_qtree(float %542, float %543, float %544, float %550, float %562, float %567)
  store %struct.qtree* %568, %struct.qtree** %22, align 8
  %569 = load %struct.qtree*, %struct.qtree** %22, align 8
  %570 = load %struct.qtree*, %struct.qtree** %7, align 8
  %571 = getelementptr inbounds %struct.qtree, %struct.qtree* %570, i32 0, i32 3
  store %struct.qtree* %569, %struct.qtree** %571, align 8
  br label %645

572:                                              ; preds = %538
  %573 = load float, float* %21, align 4
  %574 = fcmp oeq float %573, 2.000000e+00
  br i1 %574, label %575, label %606

575:                                              ; preds = %572
  %576 = load float, float* %18, align 4
  %577 = load float, float* %19, align 4
  %578 = load float, float* %20, align 4
  %579 = load %struct.qtree*, %struct.qtree** %7, align 8
  %580 = getelementptr inbounds %struct.qtree, %struct.qtree* %579, i32 0, i32 0
  %581 = load %struct.quad*, %struct.quad** %580, align 8
  %582 = getelementptr inbounds %struct.quad, %struct.quad* %581, i32 0, i32 0
  %583 = load float, float* %582, align 8
  %584 = fdiv float %583, 2.000000e+00
  %585 = load %struct.qtree*, %struct.qtree** %7, align 8
  %586 = getelementptr inbounds %struct.qtree, %struct.qtree* %585, i32 0, i32 0
  %587 = load %struct.quad*, %struct.quad** %586, align 8
  %588 = getelementptr inbounds %struct.quad, %struct.quad* %587, i32 0, i32 2
  %589 = load float, float* %588, align 8
  %590 = load %struct.qtree*, %struct.qtree** %7, align 8
  %591 = getelementptr inbounds %struct.qtree, %struct.qtree* %590, i32 0, i32 0
  %592 = load %struct.quad*, %struct.quad** %591, align 8
  %593 = getelementptr inbounds %struct.quad, %struct.quad* %592, i32 0, i32 1
  %594 = load float, float* %593, align 4
  %595 = load %struct.qtree*, %struct.qtree** %7, align 8
  %596 = getelementptr inbounds %struct.qtree, %struct.qtree* %595, i32 0, i32 0
  %597 = load %struct.quad*, %struct.quad** %596, align 8
  %598 = getelementptr inbounds %struct.quad, %struct.quad* %597, i32 0, i32 0
  %599 = load float, float* %598, align 8
  %600 = fdiv float %599, 2.000000e+00
  %601 = fadd float %594, %600
  %602 = call %struct.qtree* @empty_qtree(float %576, float %577, float %578, float %584, float %589, float %601)
  store %struct.qtree* %602, %struct.qtree** %22, align 8
  %603 = load %struct.qtree*, %struct.qtree** %22, align 8
  %604 = load %struct.qtree*, %struct.qtree** %7, align 8
  %605 = getelementptr inbounds %struct.qtree, %struct.qtree* %604, i32 0, i32 2
  store %struct.qtree* %603, %struct.qtree** %605, align 8
  br label %644

606:                                              ; preds = %572
  %607 = load float, float* %18, align 4
  %608 = load float, float* %19, align 4
  %609 = load float, float* %20, align 4
  %610 = load %struct.qtree*, %struct.qtree** %7, align 8
  %611 = getelementptr inbounds %struct.qtree, %struct.qtree* %610, i32 0, i32 0
  %612 = load %struct.quad*, %struct.quad** %611, align 8
  %613 = getelementptr inbounds %struct.quad, %struct.quad* %612, i32 0, i32 0
  %614 = load float, float* %613, align 8
  %615 = fdiv float %614, 2.000000e+00
  %616 = load %struct.qtree*, %struct.qtree** %7, align 8
  %617 = getelementptr inbounds %struct.qtree, %struct.qtree* %616, i32 0, i32 0
  %618 = load %struct.quad*, %struct.quad** %617, align 8
  %619 = getelementptr inbounds %struct.quad, %struct.quad* %618, i32 0, i32 2
  %620 = load float, float* %619, align 8
  %621 = load %struct.qtree*, %struct.qtree** %7, align 8
  %622 = getelementptr inbounds %struct.qtree, %struct.qtree* %621, i32 0, i32 0
  %623 = load %struct.quad*, %struct.quad** %622, align 8
  %624 = getelementptr inbounds %struct.quad, %struct.quad* %623, i32 0, i32 0
  %625 = load float, float* %624, align 8
  %626 = fdiv float %625, 2.000000e+00
  %627 = fadd float %620, %626
  %628 = load %struct.qtree*, %struct.qtree** %7, align 8
  %629 = getelementptr inbounds %struct.qtree, %struct.qtree* %628, i32 0, i32 0
  %630 = load %struct.quad*, %struct.quad** %629, align 8
  %631 = getelementptr inbounds %struct.quad, %struct.quad* %630, i32 0, i32 1
  %632 = load float, float* %631, align 4
  %633 = load %struct.qtree*, %struct.qtree** %7, align 8
  %634 = getelementptr inbounds %struct.qtree, %struct.qtree* %633, i32 0, i32 0
  %635 = load %struct.quad*, %struct.quad** %634, align 8
  %636 = getelementptr inbounds %struct.quad, %struct.quad* %635, i32 0, i32 0
  %637 = load float, float* %636, align 8
  %638 = fdiv float %637, 2.000000e+00
  %639 = fadd float %632, %638
  %640 = call %struct.qtree* @empty_qtree(float %607, float %608, float %609, float %615, float %627, float %639)
  store %struct.qtree* %640, %struct.qtree** %22, align 8
  %641 = load %struct.qtree*, %struct.qtree** %22, align 8
  %642 = load %struct.qtree*, %struct.qtree** %7, align 8
  %643 = getelementptr inbounds %struct.qtree, %struct.qtree* %642, i32 0, i32 4
  store %struct.qtree* %641, %struct.qtree** %643, align 8
  br label %644

644:                                              ; preds = %606, %575
  br label %645

645:                                              ; preds = %644, %541
  br label %646

646:                                              ; preds = %645, %514
  br label %647

647:                                              ; preds = %646, %478, %473, %468, %463
  %648 = load %struct.qtree*, %struct.qtree** %7, align 8
  %649 = getelementptr inbounds %struct.qtree, %struct.qtree* %648, i32 0, i32 0
  %650 = load %struct.quad*, %struct.quad** %649, align 8
  %651 = getelementptr inbounds %struct.quad, %struct.quad* %650, i32 0, i32 0
  %652 = load float, float* %651, align 8
  store float %652, float* %23, align 4
  %653 = load %struct.qtree*, %struct.qtree** %7, align 8
  %654 = getelementptr inbounds %struct.qtree, %struct.qtree* %653, i32 0, i32 2
  %655 = load %struct.qtree*, %struct.qtree** %654, align 8
  %656 = icmp eq %struct.qtree* %655, null
  br i1 %656, label %657, label %679

657:                                              ; preds = %647
  %658 = load float, float* %5, align 4
  %659 = load float, float* %6, align 4
  %660 = load float, float* %8, align 4
  %661 = load float, float* %23, align 4
  %662 = fdiv float %661, 2.000000e+00
  %663 = load %struct.qtree*, %struct.qtree** %7, align 8
  %664 = getelementptr inbounds %struct.qtree, %struct.qtree* %663, i32 0, i32 0
  %665 = load %struct.quad*, %struct.quad** %664, align 8
  %666 = getelementptr inbounds %struct.quad, %struct.quad* %665, i32 0, i32 2
  %667 = load float, float* %666, align 8
  %668 = load %struct.qtree*, %struct.qtree** %7, align 8
  %669 = getelementptr inbounds %struct.qtree, %struct.qtree* %668, i32 0, i32 0
  %670 = load %struct.quad*, %struct.quad** %669, align 8
  %671 = getelementptr inbounds %struct.quad, %struct.quad* %670, i32 0, i32 1
  %672 = load float, float* %671, align 4
  %673 = load float, float* %23, align 4
  %674 = fdiv float %673, 2.000000e+00
  %675 = fadd float %672, %674
  %676 = call %struct.qtree* @empty_qtree(float %658, float %659, float %660, float %662, float %667, float %675)
  %677 = load %struct.qtree*, %struct.qtree** %7, align 8
  %678 = getelementptr inbounds %struct.qtree, %struct.qtree* %677, i32 0, i32 2
  store %struct.qtree* %676, %struct.qtree** %678, align 8
  br label %687

679:                                              ; preds = %647
  %680 = load float, float* %5, align 4
  %681 = load float, float* %6, align 4
  %682 = load %struct.qtree*, %struct.qtree** %7, align 8
  %683 = getelementptr inbounds %struct.qtree, %struct.qtree* %682, i32 0, i32 2
  %684 = load %struct.qtree*, %struct.qtree** %683, align 8
  %685 = load float, float* %8, align 4
  %686 = call %struct.qtree* @insertPoint(float %680, float %681, %struct.qtree* %684, float %685)
  br label %687

687:                                              ; preds = %679, %657
  %688 = load %struct.qtree*, %struct.qtree** %7, align 8
  %689 = getelementptr inbounds %struct.qtree, %struct.qtree* %688, i32 0, i32 1
  %690 = load %struct.qtree*, %struct.qtree** %689, align 8
  %691 = icmp ne %struct.qtree* %690, null
  br i1 %691, label %692, label %738

692:                                              ; preds = %687
  %693 = load %struct.qtree*, %struct.qtree** %7, align 8
  %694 = getelementptr inbounds %struct.qtree, %struct.qtree* %693, i32 0, i32 1
  %695 = load %struct.qtree*, %struct.qtree** %694, align 8
  %696 = getelementptr inbounds %struct.qtree, %struct.qtree* %695, i32 0, i32 0
  %697 = load %struct.quad*, %struct.quad** %696, align 8
  %698 = getelementptr inbounds %struct.quad, %struct.quad* %697, i32 0, i32 3
  %699 = load %struct.centroid*, %struct.centroid** %698, align 8
  %700 = load %struct.qtree*, %struct.qtree** %7, align 8
  %701 = getelementptr inbounds %struct.qtree, %struct.qtree* %700, i32 0, i32 2
  %702 = load %struct.qtree*, %struct.qtree** %701, align 8
  %703 = getelementptr inbounds %struct.qtree, %struct.qtree* %702, i32 0, i32 0
  %704 = load %struct.quad*, %struct.quad** %703, align 8
  %705 = getelementptr inbounds %struct.quad, %struct.quad* %704, i32 0, i32 3
  %706 = load %struct.centroid*, %struct.centroid** %705, align 8
  %707 = call %struct.centroid* @centroid_sum(%struct.centroid* %699, %struct.centroid* %706)
  store %struct.centroid* %707, %struct.centroid** %24, align 8
  %708 = load %struct.qtree*, %struct.qtree** %7, align 8
  %709 = getelementptr inbounds %struct.qtree, %struct.qtree* %708, i32 0, i32 4
  %710 = load %struct.qtree*, %struct.qtree** %709, align 8
  %711 = icmp ne %struct.qtree* %710, null
  br i1 %711, label %712, label %722

712:                                              ; preds = %692
  %713 = load %struct.centroid*, %struct.centroid** %24, align 8
  %714 = load %struct.qtree*, %struct.qtree** %7, align 8
  %715 = getelementptr inbounds %struct.qtree, %struct.qtree* %714, i32 0, i32 4
  %716 = load %struct.qtree*, %struct.qtree** %715, align 8
  %717 = getelementptr inbounds %struct.qtree, %struct.qtree* %716, i32 0, i32 0
  %718 = load %struct.quad*, %struct.quad** %717, align 8
  %719 = getelementptr inbounds %struct.quad, %struct.quad* %718, i32 0, i32 3
  %720 = load %struct.centroid*, %struct.centroid** %719, align 8
  %721 = call %struct.centroid* @centroid_sum(%struct.centroid* %713, %struct.centroid* %720)
  store %struct.centroid* %721, %struct.centroid** %24, align 8
  br label %722

722:                                              ; preds = %712, %692
  %723 = load %struct.qtree*, %struct.qtree** %7, align 8
  %724 = getelementptr inbounds %struct.qtree, %struct.qtree* %723, i32 0, i32 3
  %725 = load %struct.qtree*, %struct.qtree** %724, align 8
  %726 = icmp ne %struct.qtree* %725, null
  br i1 %726, label %727, label %737

727:                                              ; preds = %722
  %728 = load %struct.centroid*, %struct.centroid** %24, align 8
  %729 = load %struct.qtree*, %struct.qtree** %7, align 8
  %730 = getelementptr inbounds %struct.qtree, %struct.qtree* %729, i32 0, i32 3
  %731 = load %struct.qtree*, %struct.qtree** %730, align 8
  %732 = getelementptr inbounds %struct.qtree, %struct.qtree* %731, i32 0, i32 0
  %733 = load %struct.quad*, %struct.quad** %732, align 8
  %734 = getelementptr inbounds %struct.quad, %struct.quad* %733, i32 0, i32 3
  %735 = load %struct.centroid*, %struct.centroid** %734, align 8
  %736 = call %struct.centroid* @centroid_sum(%struct.centroid* %728, %struct.centroid* %735)
  store %struct.centroid* %736, %struct.centroid** %24, align 8
  br label %737

737:                                              ; preds = %727, %722
  br label %805

738:                                              ; preds = %687
  %739 = load %struct.qtree*, %struct.qtree** %7, align 8
  %740 = getelementptr inbounds %struct.qtree, %struct.qtree* %739, i32 0, i32 4
  %741 = load %struct.qtree*, %struct.qtree** %740, align 8
  %742 = icmp ne %struct.qtree* %741, null
  br i1 %742, label %743, label %774

743:                                              ; preds = %738
  %744 = load %struct.qtree*, %struct.qtree** %7, align 8
  %745 = getelementptr inbounds %struct.qtree, %struct.qtree* %744, i32 0, i32 2
  %746 = load %struct.qtree*, %struct.qtree** %745, align 8
  %747 = getelementptr inbounds %struct.qtree, %struct.qtree* %746, i32 0, i32 0
  %748 = load %struct.quad*, %struct.quad** %747, align 8
  %749 = getelementptr inbounds %struct.quad, %struct.quad* %748, i32 0, i32 3
  %750 = load %struct.centroid*, %struct.centroid** %749, align 8
  %751 = load %struct.qtree*, %struct.qtree** %7, align 8
  %752 = getelementptr inbounds %struct.qtree, %struct.qtree* %751, i32 0, i32 4
  %753 = load %struct.qtree*, %struct.qtree** %752, align 8
  %754 = getelementptr inbounds %struct.qtree, %struct.qtree* %753, i32 0, i32 0
  %755 = load %struct.quad*, %struct.quad** %754, align 8
  %756 = getelementptr inbounds %struct.quad, %struct.quad* %755, i32 0, i32 3
  %757 = load %struct.centroid*, %struct.centroid** %756, align 8
  %758 = call %struct.centroid* @centroid_sum(%struct.centroid* %750, %struct.centroid* %757)
  store %struct.centroid* %758, %struct.centroid** %24, align 8
  %759 = load %struct.qtree*, %struct.qtree** %7, align 8
  %760 = getelementptr inbounds %struct.qtree, %struct.qtree* %759, i32 0, i32 3
  %761 = load %struct.qtree*, %struct.qtree** %760, align 8
  %762 = icmp ne %struct.qtree* %761, null
  br i1 %762, label %763, label %773

763:                                              ; preds = %743
  %764 = load %struct.centroid*, %struct.centroid** %24, align 8
  %765 = load %struct.qtree*, %struct.qtree** %7, align 8
  %766 = getelementptr inbounds %struct.qtree, %struct.qtree* %765, i32 0, i32 3
  %767 = load %struct.qtree*, %struct.qtree** %766, align 8
  %768 = getelementptr inbounds %struct.qtree, %struct.qtree* %767, i32 0, i32 0
  %769 = load %struct.quad*, %struct.quad** %768, align 8
  %770 = getelementptr inbounds %struct.quad, %struct.quad* %769, i32 0, i32 3
  %771 = load %struct.centroid*, %struct.centroid** %770, align 8
  %772 = call %struct.centroid* @centroid_sum(%struct.centroid* %764, %struct.centroid* %771)
  store %struct.centroid* %772, %struct.centroid** %24, align 8
  br label %773

773:                                              ; preds = %763, %743
  br label %804

774:                                              ; preds = %738
  %775 = load %struct.qtree*, %struct.qtree** %7, align 8
  %776 = getelementptr inbounds %struct.qtree, %struct.qtree* %775, i32 0, i32 3
  %777 = load %struct.qtree*, %struct.qtree** %776, align 8
  %778 = icmp ne %struct.qtree* %777, null
  br i1 %778, label %779, label %795

779:                                              ; preds = %774
  %780 = load %struct.qtree*, %struct.qtree** %7, align 8
  %781 = getelementptr inbounds %struct.qtree, %struct.qtree* %780, i32 0, i32 2
  %782 = load %struct.qtree*, %struct.qtree** %781, align 8
  %783 = getelementptr inbounds %struct.qtree, %struct.qtree* %782, i32 0, i32 0
  %784 = load %struct.quad*, %struct.quad** %783, align 8
  %785 = getelementptr inbounds %struct.quad, %struct.quad* %784, i32 0, i32 3
  %786 = load %struct.centroid*, %struct.centroid** %785, align 8
  %787 = load %struct.qtree*, %struct.qtree** %7, align 8
  %788 = getelementptr inbounds %struct.qtree, %struct.qtree* %787, i32 0, i32 3
  %789 = load %struct.qtree*, %struct.qtree** %788, align 8
  %790 = getelementptr inbounds %struct.qtree, %struct.qtree* %789, i32 0, i32 0
  %791 = load %struct.quad*, %struct.quad** %790, align 8
  %792 = getelementptr inbounds %struct.quad, %struct.quad* %791, i32 0, i32 3
  %793 = load %struct.centroid*, %struct.centroid** %792, align 8
  %794 = call %struct.centroid* @centroid_sum(%struct.centroid* %786, %struct.centroid* %793)
  store %struct.centroid* %794, %struct.centroid** %24, align 8
  br label %803

795:                                              ; preds = %774
  %796 = load %struct.qtree*, %struct.qtree** %7, align 8
  %797 = getelementptr inbounds %struct.qtree, %struct.qtree* %796, i32 0, i32 2
  %798 = load %struct.qtree*, %struct.qtree** %797, align 8
  %799 = getelementptr inbounds %struct.qtree, %struct.qtree* %798, i32 0, i32 0
  %800 = load %struct.quad*, %struct.quad** %799, align 8
  %801 = getelementptr inbounds %struct.quad, %struct.quad* %800, i32 0, i32 3
  %802 = load %struct.centroid*, %struct.centroid** %801, align 8
  store %struct.centroid* %802, %struct.centroid** %24, align 8
  br label %803

803:                                              ; preds = %795, %779
  br label %804

804:                                              ; preds = %803, %773
  br label %805

805:                                              ; preds = %804, %737
  %806 = load %struct.centroid*, %struct.centroid** %24, align 8
  %807 = load %struct.qtree*, %struct.qtree** %7, align 8
  %808 = getelementptr inbounds %struct.qtree, %struct.qtree* %807, i32 0, i32 0
  %809 = load %struct.quad*, %struct.quad** %808, align 8
  %810 = getelementptr inbounds %struct.quad, %struct.quad* %809, i32 0, i32 3
  store %struct.centroid* %806, %struct.centroid** %810, align 8
  br label %2106

811:                                              ; preds = %458, %450
  %812 = load float, float* %5, align 4
  %813 = load float, float* %6, align 4
  %814 = load %struct.qtree*, %struct.qtree** %7, align 8
  %815 = getelementptr inbounds %struct.qtree, %struct.qtree* %814, i32 0, i32 0
  %816 = load %struct.quad*, %struct.quad** %815, align 8
  %817 = call i32 @which_quad(float %812, float %813, %struct.quad* %816)
  %818 = icmp eq i32 %817, 3
  br i1 %818, label %819, label %1172

819:                                              ; preds = %811
  %820 = load %struct.qtree*, %struct.qtree** %7, align 8
  %821 = getelementptr inbounds %struct.qtree, %struct.qtree* %820, i32 0, i32 3
  %822 = load %struct.qtree*, %struct.qtree** %821, align 8
  %823 = icmp eq %struct.qtree* %822, null
  br i1 %823, label %824, label %1172

824:                                              ; preds = %819
  %825 = load %struct.qtree*, %struct.qtree** %7, align 8
  %826 = getelementptr inbounds %struct.qtree, %struct.qtree* %825, i32 0, i32 1
  %827 = load %struct.qtree*, %struct.qtree** %826, align 8
  %828 = icmp eq %struct.qtree* %827, null
  br i1 %828, label %829, label %1008

829:                                              ; preds = %824
  %830 = load %struct.qtree*, %struct.qtree** %7, align 8
  %831 = getelementptr inbounds %struct.qtree, %struct.qtree* %830, i32 0, i32 2
  %832 = load %struct.qtree*, %struct.qtree** %831, align 8
  %833 = icmp eq %struct.qtree* %832, null
  br i1 %833, label %834, label %1008

834:                                              ; preds = %829
  %835 = load %struct.qtree*, %struct.qtree** %7, align 8
  %836 = getelementptr inbounds %struct.qtree, %struct.qtree* %835, i32 0, i32 3
  %837 = load %struct.qtree*, %struct.qtree** %836, align 8
  %838 = icmp eq %struct.qtree* %837, null
  br i1 %838, label %839, label %1008

839:                                              ; preds = %834
  %840 = load %struct.qtree*, %struct.qtree** %7, align 8
  %841 = getelementptr inbounds %struct.qtree, %struct.qtree* %840, i32 0, i32 4
  %842 = load %struct.qtree*, %struct.qtree** %841, align 8
  %843 = icmp eq %struct.qtree* %842, null
  br i1 %843, label %844, label %1008

844:                                              ; preds = %839
  %845 = load %struct.qtree*, %struct.qtree** %7, align 8
  %846 = getelementptr inbounds %struct.qtree, %struct.qtree* %845, i32 0, i32 0
  %847 = load %struct.quad*, %struct.quad** %846, align 8
  %848 = getelementptr inbounds %struct.quad, %struct.quad* %847, i32 0, i32 3
  %849 = load %struct.centroid*, %struct.centroid** %848, align 8
  %850 = getelementptr inbounds %struct.centroid, %struct.centroid* %849, i32 0, i32 0
  %851 = load float, float* %850, align 4
  store float %851, float* %25, align 4
  %852 = load %struct.qtree*, %struct.qtree** %7, align 8
  %853 = getelementptr inbounds %struct.qtree, %struct.qtree* %852, i32 0, i32 0
  %854 = load %struct.quad*, %struct.quad** %853, align 8
  %855 = getelementptr inbounds %struct.quad, %struct.quad* %854, i32 0, i32 3
  %856 = load %struct.centroid*, %struct.centroid** %855, align 8
  %857 = getelementptr inbounds %struct.centroid, %struct.centroid* %856, i32 0, i32 1
  %858 = load float, float* %857, align 4
  store float %858, float* %26, align 4
  %859 = load %struct.qtree*, %struct.qtree** %7, align 8
  %860 = getelementptr inbounds %struct.qtree, %struct.qtree* %859, i32 0, i32 0
  %861 = load %struct.quad*, %struct.quad** %860, align 8
  %862 = getelementptr inbounds %struct.quad, %struct.quad* %861, i32 0, i32 3
  %863 = load %struct.centroid*, %struct.centroid** %862, align 8
  %864 = getelementptr inbounds %struct.centroid, %struct.centroid* %863, i32 0, i32 2
  %865 = load float, float* %864, align 4
  store float %865, float* %27, align 4
  %866 = load float, float* %25, align 4
  %867 = load float, float* %26, align 4
  %868 = load %struct.qtree*, %struct.qtree** %7, align 8
  %869 = getelementptr inbounds %struct.qtree, %struct.qtree* %868, i32 0, i32 0
  %870 = load %struct.quad*, %struct.quad** %869, align 8
  %871 = call i32 @which_quad(float %866, float %867, %struct.quad* %870)
  %872 = sitofp i32 %871 to float
  store float %872, float* %28, align 4
  %873 = load float, float* %28, align 4
  %874 = fcmp oeq float %873, 1.000000e+00
  br i1 %874, label %875, label %899

875:                                              ; preds = %844
  %876 = load float, float* %25, align 4
  %877 = load float, float* %26, align 4
  %878 = load float, float* %27, align 4
  %879 = load %struct.qtree*, %struct.qtree** %7, align 8
  %880 = getelementptr inbounds %struct.qtree, %struct.qtree* %879, i32 0, i32 0
  %881 = load %struct.quad*, %struct.quad** %880, align 8
  %882 = getelementptr inbounds %struct.quad, %struct.quad* %881, i32 0, i32 0
  %883 = load float, float* %882, align 8
  %884 = fdiv float %883, 2.000000e+00
  %885 = load %struct.qtree*, %struct.qtree** %7, align 8
  %886 = getelementptr inbounds %struct.qtree, %struct.qtree* %885, i32 0, i32 0
  %887 = load %struct.quad*, %struct.quad** %886, align 8
  %888 = getelementptr inbounds %struct.quad, %struct.quad* %887, i32 0, i32 2
  %889 = load float, float* %888, align 8
  %890 = load %struct.qtree*, %struct.qtree** %7, align 8
  %891 = getelementptr inbounds %struct.qtree, %struct.qtree* %890, i32 0, i32 0
  %892 = load %struct.quad*, %struct.quad** %891, align 8
  %893 = getelementptr inbounds %struct.quad, %struct.quad* %892, i32 0, i32 1
  %894 = load float, float* %893, align 4
  %895 = call %struct.qtree* @empty_qtree(float %876, float %877, float %878, float %884, float %889, float %894)
  store %struct.qtree* %895, %struct.qtree** %29, align 8
  %896 = load %struct.qtree*, %struct.qtree** %29, align 8
  %897 = load %struct.qtree*, %struct.qtree** %7, align 8
  %898 = getelementptr inbounds %struct.qtree, %struct.qtree* %897, i32 0, i32 1
  store %struct.qtree* %896, %struct.qtree** %898, align 8
  br label %1007

899:                                              ; preds = %844
  %900 = load float, float* %28, align 4
  %901 = fcmp oeq float %900, 3.000000e+00
  br i1 %901, label %902, label %933

902:                                              ; preds = %899
  %903 = load float, float* %25, align 4
  %904 = load float, float* %26, align 4
  %905 = load float, float* %27, align 4
  %906 = load %struct.qtree*, %struct.qtree** %7, align 8
  %907 = getelementptr inbounds %struct.qtree, %struct.qtree* %906, i32 0, i32 0
  %908 = load %struct.quad*, %struct.quad** %907, align 8
  %909 = getelementptr inbounds %struct.quad, %struct.quad* %908, i32 0, i32 0
  %910 = load float, float* %909, align 8
  %911 = fdiv float %910, 2.000000e+00
  %912 = load %struct.qtree*, %struct.qtree** %7, align 8
  %913 = getelementptr inbounds %struct.qtree, %struct.qtree* %912, i32 0, i32 0
  %914 = load %struct.quad*, %struct.quad** %913, align 8
  %915 = getelementptr inbounds %struct.quad, %struct.quad* %914, i32 0, i32 2
  %916 = load float, float* %915, align 8
  %917 = load %struct.qtree*, %struct.qtree** %7, align 8
  %918 = getelementptr inbounds %struct.qtree, %struct.qtree* %917, i32 0, i32 0
  %919 = load %struct.quad*, %struct.quad** %918, align 8
  %920 = getelementptr inbounds %struct.quad, %struct.quad* %919, i32 0, i32 0
  %921 = load float, float* %920, align 8
  %922 = fdiv float %921, 2.000000e+00
  %923 = fadd float %916, %922
  %924 = load %struct.qtree*, %struct.qtree** %7, align 8
  %925 = getelementptr inbounds %struct.qtree, %struct.qtree* %924, i32 0, i32 0
  %926 = load %struct.quad*, %struct.quad** %925, align 8
  %927 = getelementptr inbounds %struct.quad, %struct.quad* %926, i32 0, i32 1
  %928 = load float, float* %927, align 4
  %929 = call %struct.qtree* @empty_qtree(float %903, float %904, float %905, float %911, float %923, float %928)
  store %struct.qtree* %929, %struct.qtree** %29, align 8
  %930 = load %struct.qtree*, %struct.qtree** %29, align 8
  %931 = load %struct.qtree*, %struct.qtree** %7, align 8
  %932 = getelementptr inbounds %struct.qtree, %struct.qtree* %931, i32 0, i32 3
  store %struct.qtree* %930, %struct.qtree** %932, align 8
  br label %1006

933:                                              ; preds = %899
  %934 = load float, float* %28, align 4
  %935 = fcmp oeq float %934, 2.000000e+00
  br i1 %935, label %936, label %967

936:                                              ; preds = %933
  %937 = load float, float* %25, align 4
  %938 = load float, float* %26, align 4
  %939 = load float, float* %27, align 4
  %940 = load %struct.qtree*, %struct.qtree** %7, align 8
  %941 = getelementptr inbounds %struct.qtree, %struct.qtree* %940, i32 0, i32 0
  %942 = load %struct.quad*, %struct.quad** %941, align 8
  %943 = getelementptr inbounds %struct.quad, %struct.quad* %942, i32 0, i32 0
  %944 = load float, float* %943, align 8
  %945 = fdiv float %944, 2.000000e+00
  %946 = load %struct.qtree*, %struct.qtree** %7, align 8
  %947 = getelementptr inbounds %struct.qtree, %struct.qtree* %946, i32 0, i32 0
  %948 = load %struct.quad*, %struct.quad** %947, align 8
  %949 = getelementptr inbounds %struct.quad, %struct.quad* %948, i32 0, i32 2
  %950 = load float, float* %949, align 8
  %951 = load %struct.qtree*, %struct.qtree** %7, align 8
  %952 = getelementptr inbounds %struct.qtree, %struct.qtree* %951, i32 0, i32 0
  %953 = load %struct.quad*, %struct.quad** %952, align 8
  %954 = getelementptr inbounds %struct.quad, %struct.quad* %953, i32 0, i32 1
  %955 = load float, float* %954, align 4
  %956 = load %struct.qtree*, %struct.qtree** %7, align 8
  %957 = getelementptr inbounds %struct.qtree, %struct.qtree* %956, i32 0, i32 0
  %958 = load %struct.quad*, %struct.quad** %957, align 8
  %959 = getelementptr inbounds %struct.quad, %struct.quad* %958, i32 0, i32 0
  %960 = load float, float* %959, align 8
  %961 = fdiv float %960, 2.000000e+00
  %962 = fadd float %955, %961
  %963 = call %struct.qtree* @empty_qtree(float %937, float %938, float %939, float %945, float %950, float %962)
  store %struct.qtree* %963, %struct.qtree** %29, align 8
  %964 = load %struct.qtree*, %struct.qtree** %29, align 8
  %965 = load %struct.qtree*, %struct.qtree** %7, align 8
  %966 = getelementptr inbounds %struct.qtree, %struct.qtree* %965, i32 0, i32 2
  store %struct.qtree* %964, %struct.qtree** %966, align 8
  br label %1005

967:                                              ; preds = %933
  %968 = load float, float* %25, align 4
  %969 = load float, float* %26, align 4
  %970 = load float, float* %27, align 4
  %971 = load %struct.qtree*, %struct.qtree** %7, align 8
  %972 = getelementptr inbounds %struct.qtree, %struct.qtree* %971, i32 0, i32 0
  %973 = load %struct.quad*, %struct.quad** %972, align 8
  %974 = getelementptr inbounds %struct.quad, %struct.quad* %973, i32 0, i32 0
  %975 = load float, float* %974, align 8
  %976 = fdiv float %975, 2.000000e+00
  %977 = load %struct.qtree*, %struct.qtree** %7, align 8
  %978 = getelementptr inbounds %struct.qtree, %struct.qtree* %977, i32 0, i32 0
  %979 = load %struct.quad*, %struct.quad** %978, align 8
  %980 = getelementptr inbounds %struct.quad, %struct.quad* %979, i32 0, i32 2
  %981 = load float, float* %980, align 8
  %982 = load %struct.qtree*, %struct.qtree** %7, align 8
  %983 = getelementptr inbounds %struct.qtree, %struct.qtree* %982, i32 0, i32 0
  %984 = load %struct.quad*, %struct.quad** %983, align 8
  %985 = getelementptr inbounds %struct.quad, %struct.quad* %984, i32 0, i32 0
  %986 = load float, float* %985, align 8
  %987 = fdiv float %986, 2.000000e+00
  %988 = fadd float %981, %987
  %989 = load %struct.qtree*, %struct.qtree** %7, align 8
  %990 = getelementptr inbounds %struct.qtree, %struct.qtree* %989, i32 0, i32 0
  %991 = load %struct.quad*, %struct.quad** %990, align 8
  %992 = getelementptr inbounds %struct.quad, %struct.quad* %991, i32 0, i32 1
  %993 = load float, float* %992, align 4
  %994 = load %struct.qtree*, %struct.qtree** %7, align 8
  %995 = getelementptr inbounds %struct.qtree, %struct.qtree* %994, i32 0, i32 0
  %996 = load %struct.quad*, %struct.quad** %995, align 8
  %997 = getelementptr inbounds %struct.quad, %struct.quad* %996, i32 0, i32 0
  %998 = load float, float* %997, align 8
  %999 = fdiv float %998, 2.000000e+00
  %1000 = fadd float %993, %999
  %1001 = call %struct.qtree* @empty_qtree(float %968, float %969, float %970, float %976, float %988, float %1000)
  store %struct.qtree* %1001, %struct.qtree** %29, align 8
  %1002 = load %struct.qtree*, %struct.qtree** %29, align 8
  %1003 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1004 = getelementptr inbounds %struct.qtree, %struct.qtree* %1003, i32 0, i32 4
  store %struct.qtree* %1002, %struct.qtree** %1004, align 8
  br label %1005

1005:                                             ; preds = %967, %936
  br label %1006

1006:                                             ; preds = %1005, %902
  br label %1007

1007:                                             ; preds = %1006, %875
  br label %1008

1008:                                             ; preds = %1007, %839, %834, %829, %824
  %1009 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1010 = getelementptr inbounds %struct.qtree, %struct.qtree* %1009, i32 0, i32 0
  %1011 = load %struct.quad*, %struct.quad** %1010, align 8
  %1012 = getelementptr inbounds %struct.quad, %struct.quad* %1011, i32 0, i32 0
  %1013 = load float, float* %1012, align 8
  store float %1013, float* %30, align 4
  %1014 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1015 = getelementptr inbounds %struct.qtree, %struct.qtree* %1014, i32 0, i32 3
  %1016 = load %struct.qtree*, %struct.qtree** %1015, align 8
  %1017 = icmp eq %struct.qtree* %1016, null
  br i1 %1017, label %1018, label %1040

1018:                                             ; preds = %1008
  %1019 = load float, float* %5, align 4
  %1020 = load float, float* %6, align 4
  %1021 = load float, float* %8, align 4
  %1022 = load float, float* %30, align 4
  %1023 = fdiv float %1022, 2.000000e+00
  %1024 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1025 = getelementptr inbounds %struct.qtree, %struct.qtree* %1024, i32 0, i32 0
  %1026 = load %struct.quad*, %struct.quad** %1025, align 8
  %1027 = getelementptr inbounds %struct.quad, %struct.quad* %1026, i32 0, i32 2
  %1028 = load float, float* %1027, align 8
  %1029 = load float, float* %30, align 4
  %1030 = fdiv float %1029, 2.000000e+00
  %1031 = fadd float %1028, %1030
  %1032 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1033 = getelementptr inbounds %struct.qtree, %struct.qtree* %1032, i32 0, i32 0
  %1034 = load %struct.quad*, %struct.quad** %1033, align 8
  %1035 = getelementptr inbounds %struct.quad, %struct.quad* %1034, i32 0, i32 1
  %1036 = load float, float* %1035, align 4
  %1037 = call %struct.qtree* @empty_qtree(float %1019, float %1020, float %1021, float %1023, float %1031, float %1036)
  %1038 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1039 = getelementptr inbounds %struct.qtree, %struct.qtree* %1038, i32 0, i32 3
  store %struct.qtree* %1037, %struct.qtree** %1039, align 8
  br label %1048

1040:                                             ; preds = %1008
  %1041 = load float, float* %5, align 4
  %1042 = load float, float* %6, align 4
  %1043 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1044 = getelementptr inbounds %struct.qtree, %struct.qtree* %1043, i32 0, i32 3
  %1045 = load %struct.qtree*, %struct.qtree** %1044, align 8
  %1046 = load float, float* %8, align 4
  %1047 = call %struct.qtree* @insertPoint(float %1041, float %1042, %struct.qtree* %1045, float %1046)
  br label %1048

1048:                                             ; preds = %1040, %1018
  %1049 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1050 = getelementptr inbounds %struct.qtree, %struct.qtree* %1049, i32 0, i32 1
  %1051 = load %struct.qtree*, %struct.qtree** %1050, align 8
  %1052 = icmp ne %struct.qtree* %1051, null
  br i1 %1052, label %1053, label %1099

1053:                                             ; preds = %1048
  %1054 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1055 = getelementptr inbounds %struct.qtree, %struct.qtree* %1054, i32 0, i32 1
  %1056 = load %struct.qtree*, %struct.qtree** %1055, align 8
  %1057 = getelementptr inbounds %struct.qtree, %struct.qtree* %1056, i32 0, i32 0
  %1058 = load %struct.quad*, %struct.quad** %1057, align 8
  %1059 = getelementptr inbounds %struct.quad, %struct.quad* %1058, i32 0, i32 3
  %1060 = load %struct.centroid*, %struct.centroid** %1059, align 8
  %1061 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1062 = getelementptr inbounds %struct.qtree, %struct.qtree* %1061, i32 0, i32 3
  %1063 = load %struct.qtree*, %struct.qtree** %1062, align 8
  %1064 = getelementptr inbounds %struct.qtree, %struct.qtree* %1063, i32 0, i32 0
  %1065 = load %struct.quad*, %struct.quad** %1064, align 8
  %1066 = getelementptr inbounds %struct.quad, %struct.quad* %1065, i32 0, i32 3
  %1067 = load %struct.centroid*, %struct.centroid** %1066, align 8
  %1068 = call %struct.centroid* @centroid_sum(%struct.centroid* %1060, %struct.centroid* %1067)
  store %struct.centroid* %1068, %struct.centroid** %31, align 8
  %1069 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1070 = getelementptr inbounds %struct.qtree, %struct.qtree* %1069, i32 0, i32 2
  %1071 = load %struct.qtree*, %struct.qtree** %1070, align 8
  %1072 = icmp ne %struct.qtree* %1071, null
  br i1 %1072, label %1073, label %1083

1073:                                             ; preds = %1053
  %1074 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1075 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1076 = getelementptr inbounds %struct.qtree, %struct.qtree* %1075, i32 0, i32 2
  %1077 = load %struct.qtree*, %struct.qtree** %1076, align 8
  %1078 = getelementptr inbounds %struct.qtree, %struct.qtree* %1077, i32 0, i32 0
  %1079 = load %struct.quad*, %struct.quad** %1078, align 8
  %1080 = getelementptr inbounds %struct.quad, %struct.quad* %1079, i32 0, i32 3
  %1081 = load %struct.centroid*, %struct.centroid** %1080, align 8
  %1082 = call %struct.centroid* @centroid_sum(%struct.centroid* %1074, %struct.centroid* %1081)
  store %struct.centroid* %1082, %struct.centroid** %31, align 8
  br label %1083

1083:                                             ; preds = %1073, %1053
  %1084 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1085 = getelementptr inbounds %struct.qtree, %struct.qtree* %1084, i32 0, i32 4
  %1086 = load %struct.qtree*, %struct.qtree** %1085, align 8
  %1087 = icmp ne %struct.qtree* %1086, null
  br i1 %1087, label %1088, label %1098

1088:                                             ; preds = %1083
  %1089 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1090 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1091 = getelementptr inbounds %struct.qtree, %struct.qtree* %1090, i32 0, i32 4
  %1092 = load %struct.qtree*, %struct.qtree** %1091, align 8
  %1093 = getelementptr inbounds %struct.qtree, %struct.qtree* %1092, i32 0, i32 0
  %1094 = load %struct.quad*, %struct.quad** %1093, align 8
  %1095 = getelementptr inbounds %struct.quad, %struct.quad* %1094, i32 0, i32 3
  %1096 = load %struct.centroid*, %struct.centroid** %1095, align 8
  %1097 = call %struct.centroid* @centroid_sum(%struct.centroid* %1089, %struct.centroid* %1096)
  store %struct.centroid* %1097, %struct.centroid** %31, align 8
  br label %1098

1098:                                             ; preds = %1088, %1083
  br label %1166

1099:                                             ; preds = %1048
  %1100 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1101 = getelementptr inbounds %struct.qtree, %struct.qtree* %1100, i32 0, i32 2
  %1102 = load %struct.qtree*, %struct.qtree** %1101, align 8
  %1103 = icmp ne %struct.qtree* %1102, null
  br i1 %1103, label %1104, label %1135

1104:                                             ; preds = %1099
  %1105 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1106 = getelementptr inbounds %struct.qtree, %struct.qtree* %1105, i32 0, i32 2
  %1107 = load %struct.qtree*, %struct.qtree** %1106, align 8
  %1108 = getelementptr inbounds %struct.qtree, %struct.qtree* %1107, i32 0, i32 0
  %1109 = load %struct.quad*, %struct.quad** %1108, align 8
  %1110 = getelementptr inbounds %struct.quad, %struct.quad* %1109, i32 0, i32 3
  %1111 = load %struct.centroid*, %struct.centroid** %1110, align 8
  %1112 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1113 = getelementptr inbounds %struct.qtree, %struct.qtree* %1112, i32 0, i32 3
  %1114 = load %struct.qtree*, %struct.qtree** %1113, align 8
  %1115 = getelementptr inbounds %struct.qtree, %struct.qtree* %1114, i32 0, i32 0
  %1116 = load %struct.quad*, %struct.quad** %1115, align 8
  %1117 = getelementptr inbounds %struct.quad, %struct.quad* %1116, i32 0, i32 3
  %1118 = load %struct.centroid*, %struct.centroid** %1117, align 8
  %1119 = call %struct.centroid* @centroid_sum(%struct.centroid* %1111, %struct.centroid* %1118)
  store %struct.centroid* %1119, %struct.centroid** %31, align 8
  %1120 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1121 = getelementptr inbounds %struct.qtree, %struct.qtree* %1120, i32 0, i32 4
  %1122 = load %struct.qtree*, %struct.qtree** %1121, align 8
  %1123 = icmp ne %struct.qtree* %1122, null
  br i1 %1123, label %1124, label %1134

1124:                                             ; preds = %1104
  %1125 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1126 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1127 = getelementptr inbounds %struct.qtree, %struct.qtree* %1126, i32 0, i32 4
  %1128 = load %struct.qtree*, %struct.qtree** %1127, align 8
  %1129 = getelementptr inbounds %struct.qtree, %struct.qtree* %1128, i32 0, i32 0
  %1130 = load %struct.quad*, %struct.quad** %1129, align 8
  %1131 = getelementptr inbounds %struct.quad, %struct.quad* %1130, i32 0, i32 3
  %1132 = load %struct.centroid*, %struct.centroid** %1131, align 8
  %1133 = call %struct.centroid* @centroid_sum(%struct.centroid* %1125, %struct.centroid* %1132)
  store %struct.centroid* %1133, %struct.centroid** %31, align 8
  br label %1134

1134:                                             ; preds = %1124, %1104
  br label %1165

1135:                                             ; preds = %1099
  %1136 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1137 = getelementptr inbounds %struct.qtree, %struct.qtree* %1136, i32 0, i32 4
  %1138 = load %struct.qtree*, %struct.qtree** %1137, align 8
  %1139 = icmp ne %struct.qtree* %1138, null
  br i1 %1139, label %1140, label %1156

1140:                                             ; preds = %1135
  %1141 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1142 = getelementptr inbounds %struct.qtree, %struct.qtree* %1141, i32 0, i32 3
  %1143 = load %struct.qtree*, %struct.qtree** %1142, align 8
  %1144 = getelementptr inbounds %struct.qtree, %struct.qtree* %1143, i32 0, i32 0
  %1145 = load %struct.quad*, %struct.quad** %1144, align 8
  %1146 = getelementptr inbounds %struct.quad, %struct.quad* %1145, i32 0, i32 3
  %1147 = load %struct.centroid*, %struct.centroid** %1146, align 8
  %1148 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1149 = getelementptr inbounds %struct.qtree, %struct.qtree* %1148, i32 0, i32 4
  %1150 = load %struct.qtree*, %struct.qtree** %1149, align 8
  %1151 = getelementptr inbounds %struct.qtree, %struct.qtree* %1150, i32 0, i32 0
  %1152 = load %struct.quad*, %struct.quad** %1151, align 8
  %1153 = getelementptr inbounds %struct.quad, %struct.quad* %1152, i32 0, i32 3
  %1154 = load %struct.centroid*, %struct.centroid** %1153, align 8
  %1155 = call %struct.centroid* @centroid_sum(%struct.centroid* %1147, %struct.centroid* %1154)
  store %struct.centroid* %1155, %struct.centroid** %31, align 8
  br label %1164

1156:                                             ; preds = %1135
  %1157 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1158 = getelementptr inbounds %struct.qtree, %struct.qtree* %1157, i32 0, i32 3
  %1159 = load %struct.qtree*, %struct.qtree** %1158, align 8
  %1160 = getelementptr inbounds %struct.qtree, %struct.qtree* %1159, i32 0, i32 0
  %1161 = load %struct.quad*, %struct.quad** %1160, align 8
  %1162 = getelementptr inbounds %struct.quad, %struct.quad* %1161, i32 0, i32 3
  %1163 = load %struct.centroid*, %struct.centroid** %1162, align 8
  store %struct.centroid* %1163, %struct.centroid** %31, align 8
  br label %1164

1164:                                             ; preds = %1156, %1140
  br label %1165

1165:                                             ; preds = %1164, %1134
  br label %1166

1166:                                             ; preds = %1165, %1098
  %1167 = load %struct.centroid*, %struct.centroid** %31, align 8
  %1168 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1169 = getelementptr inbounds %struct.qtree, %struct.qtree* %1168, i32 0, i32 0
  %1170 = load %struct.quad*, %struct.quad** %1169, align 8
  %1171 = getelementptr inbounds %struct.quad, %struct.quad* %1170, i32 0, i32 3
  store %struct.centroid* %1167, %struct.centroid** %1171, align 8
  br label %2105

1172:                                             ; preds = %819, %811
  %1173 = load float, float* %5, align 4
  %1174 = load float, float* %6, align 4
  %1175 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1176 = getelementptr inbounds %struct.qtree, %struct.qtree* %1175, i32 0, i32 0
  %1177 = load %struct.quad*, %struct.quad** %1176, align 8
  %1178 = call i32 @which_quad(float %1173, float %1174, %struct.quad* %1177)
  %1179 = icmp eq i32 %1178, 4
  br i1 %1179, label %1180, label %1536

1180:                                             ; preds = %1172
  %1181 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1182 = getelementptr inbounds %struct.qtree, %struct.qtree* %1181, i32 0, i32 4
  %1183 = load %struct.qtree*, %struct.qtree** %1182, align 8
  %1184 = icmp eq %struct.qtree* %1183, null
  br i1 %1184, label %1185, label %1536

1185:                                             ; preds = %1180
  %1186 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1187 = getelementptr inbounds %struct.qtree, %struct.qtree* %1186, i32 0, i32 1
  %1188 = load %struct.qtree*, %struct.qtree** %1187, align 8
  %1189 = icmp eq %struct.qtree* %1188, null
  br i1 %1189, label %1190, label %1369

1190:                                             ; preds = %1185
  %1191 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1192 = getelementptr inbounds %struct.qtree, %struct.qtree* %1191, i32 0, i32 2
  %1193 = load %struct.qtree*, %struct.qtree** %1192, align 8
  %1194 = icmp eq %struct.qtree* %1193, null
  br i1 %1194, label %1195, label %1369

1195:                                             ; preds = %1190
  %1196 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1197 = getelementptr inbounds %struct.qtree, %struct.qtree* %1196, i32 0, i32 3
  %1198 = load %struct.qtree*, %struct.qtree** %1197, align 8
  %1199 = icmp eq %struct.qtree* %1198, null
  br i1 %1199, label %1200, label %1369

1200:                                             ; preds = %1195
  %1201 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1202 = getelementptr inbounds %struct.qtree, %struct.qtree* %1201, i32 0, i32 4
  %1203 = load %struct.qtree*, %struct.qtree** %1202, align 8
  %1204 = icmp eq %struct.qtree* %1203, null
  br i1 %1204, label %1205, label %1369

1205:                                             ; preds = %1200
  %1206 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1207 = getelementptr inbounds %struct.qtree, %struct.qtree* %1206, i32 0, i32 0
  %1208 = load %struct.quad*, %struct.quad** %1207, align 8
  %1209 = getelementptr inbounds %struct.quad, %struct.quad* %1208, i32 0, i32 3
  %1210 = load %struct.centroid*, %struct.centroid** %1209, align 8
  %1211 = getelementptr inbounds %struct.centroid, %struct.centroid* %1210, i32 0, i32 0
  %1212 = load float, float* %1211, align 4
  store float %1212, float* %32, align 4
  %1213 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1214 = getelementptr inbounds %struct.qtree, %struct.qtree* %1213, i32 0, i32 0
  %1215 = load %struct.quad*, %struct.quad** %1214, align 8
  %1216 = getelementptr inbounds %struct.quad, %struct.quad* %1215, i32 0, i32 3
  %1217 = load %struct.centroid*, %struct.centroid** %1216, align 8
  %1218 = getelementptr inbounds %struct.centroid, %struct.centroid* %1217, i32 0, i32 1
  %1219 = load float, float* %1218, align 4
  store float %1219, float* %33, align 4
  %1220 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1221 = getelementptr inbounds %struct.qtree, %struct.qtree* %1220, i32 0, i32 0
  %1222 = load %struct.quad*, %struct.quad** %1221, align 8
  %1223 = getelementptr inbounds %struct.quad, %struct.quad* %1222, i32 0, i32 3
  %1224 = load %struct.centroid*, %struct.centroid** %1223, align 8
  %1225 = getelementptr inbounds %struct.centroid, %struct.centroid* %1224, i32 0, i32 2
  %1226 = load float, float* %1225, align 4
  store float %1226, float* %34, align 4
  %1227 = load float, float* %32, align 4
  %1228 = load float, float* %33, align 4
  %1229 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1230 = getelementptr inbounds %struct.qtree, %struct.qtree* %1229, i32 0, i32 0
  %1231 = load %struct.quad*, %struct.quad** %1230, align 8
  %1232 = call i32 @which_quad(float %1227, float %1228, %struct.quad* %1231)
  %1233 = sitofp i32 %1232 to float
  store float %1233, float* %35, align 4
  %1234 = load float, float* %35, align 4
  %1235 = fcmp oeq float %1234, 1.000000e+00
  br i1 %1235, label %1236, label %1260

1236:                                             ; preds = %1205
  %1237 = load float, float* %32, align 4
  %1238 = load float, float* %33, align 4
  %1239 = load float, float* %34, align 4
  %1240 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1241 = getelementptr inbounds %struct.qtree, %struct.qtree* %1240, i32 0, i32 0
  %1242 = load %struct.quad*, %struct.quad** %1241, align 8
  %1243 = getelementptr inbounds %struct.quad, %struct.quad* %1242, i32 0, i32 0
  %1244 = load float, float* %1243, align 8
  %1245 = fdiv float %1244, 2.000000e+00
  %1246 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1247 = getelementptr inbounds %struct.qtree, %struct.qtree* %1246, i32 0, i32 0
  %1248 = load %struct.quad*, %struct.quad** %1247, align 8
  %1249 = getelementptr inbounds %struct.quad, %struct.quad* %1248, i32 0, i32 2
  %1250 = load float, float* %1249, align 8
  %1251 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1252 = getelementptr inbounds %struct.qtree, %struct.qtree* %1251, i32 0, i32 0
  %1253 = load %struct.quad*, %struct.quad** %1252, align 8
  %1254 = getelementptr inbounds %struct.quad, %struct.quad* %1253, i32 0, i32 1
  %1255 = load float, float* %1254, align 4
  %1256 = call %struct.qtree* @empty_qtree(float %1237, float %1238, float %1239, float %1245, float %1250, float %1255)
  store %struct.qtree* %1256, %struct.qtree** %36, align 8
  %1257 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1258 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1259 = getelementptr inbounds %struct.qtree, %struct.qtree* %1258, i32 0, i32 1
  store %struct.qtree* %1257, %struct.qtree** %1259, align 8
  br label %1368

1260:                                             ; preds = %1205
  %1261 = load float, float* %35, align 4
  %1262 = fcmp oeq float %1261, 3.000000e+00
  br i1 %1262, label %1263, label %1294

1263:                                             ; preds = %1260
  %1264 = load float, float* %32, align 4
  %1265 = load float, float* %33, align 4
  %1266 = load float, float* %34, align 4
  %1267 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1268 = getelementptr inbounds %struct.qtree, %struct.qtree* %1267, i32 0, i32 0
  %1269 = load %struct.quad*, %struct.quad** %1268, align 8
  %1270 = getelementptr inbounds %struct.quad, %struct.quad* %1269, i32 0, i32 0
  %1271 = load float, float* %1270, align 8
  %1272 = fdiv float %1271, 2.000000e+00
  %1273 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1274 = getelementptr inbounds %struct.qtree, %struct.qtree* %1273, i32 0, i32 0
  %1275 = load %struct.quad*, %struct.quad** %1274, align 8
  %1276 = getelementptr inbounds %struct.quad, %struct.quad* %1275, i32 0, i32 2
  %1277 = load float, float* %1276, align 8
  %1278 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1279 = getelementptr inbounds %struct.qtree, %struct.qtree* %1278, i32 0, i32 0
  %1280 = load %struct.quad*, %struct.quad** %1279, align 8
  %1281 = getelementptr inbounds %struct.quad, %struct.quad* %1280, i32 0, i32 0
  %1282 = load float, float* %1281, align 8
  %1283 = fdiv float %1282, 2.000000e+00
  %1284 = fadd float %1277, %1283
  %1285 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1286 = getelementptr inbounds %struct.qtree, %struct.qtree* %1285, i32 0, i32 0
  %1287 = load %struct.quad*, %struct.quad** %1286, align 8
  %1288 = getelementptr inbounds %struct.quad, %struct.quad* %1287, i32 0, i32 1
  %1289 = load float, float* %1288, align 4
  %1290 = call %struct.qtree* @empty_qtree(float %1264, float %1265, float %1266, float %1272, float %1284, float %1289)
  store %struct.qtree* %1290, %struct.qtree** %36, align 8
  %1291 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1292 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1293 = getelementptr inbounds %struct.qtree, %struct.qtree* %1292, i32 0, i32 3
  store %struct.qtree* %1291, %struct.qtree** %1293, align 8
  br label %1367

1294:                                             ; preds = %1260
  %1295 = load float, float* %35, align 4
  %1296 = fcmp oeq float %1295, 2.000000e+00
  br i1 %1296, label %1297, label %1328

1297:                                             ; preds = %1294
  %1298 = load float, float* %32, align 4
  %1299 = load float, float* %33, align 4
  %1300 = load float, float* %34, align 4
  %1301 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1302 = getelementptr inbounds %struct.qtree, %struct.qtree* %1301, i32 0, i32 0
  %1303 = load %struct.quad*, %struct.quad** %1302, align 8
  %1304 = getelementptr inbounds %struct.quad, %struct.quad* %1303, i32 0, i32 0
  %1305 = load float, float* %1304, align 8
  %1306 = fdiv float %1305, 2.000000e+00
  %1307 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1308 = getelementptr inbounds %struct.qtree, %struct.qtree* %1307, i32 0, i32 0
  %1309 = load %struct.quad*, %struct.quad** %1308, align 8
  %1310 = getelementptr inbounds %struct.quad, %struct.quad* %1309, i32 0, i32 2
  %1311 = load float, float* %1310, align 8
  %1312 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1313 = getelementptr inbounds %struct.qtree, %struct.qtree* %1312, i32 0, i32 0
  %1314 = load %struct.quad*, %struct.quad** %1313, align 8
  %1315 = getelementptr inbounds %struct.quad, %struct.quad* %1314, i32 0, i32 1
  %1316 = load float, float* %1315, align 4
  %1317 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1318 = getelementptr inbounds %struct.qtree, %struct.qtree* %1317, i32 0, i32 0
  %1319 = load %struct.quad*, %struct.quad** %1318, align 8
  %1320 = getelementptr inbounds %struct.quad, %struct.quad* %1319, i32 0, i32 0
  %1321 = load float, float* %1320, align 8
  %1322 = fdiv float %1321, 2.000000e+00
  %1323 = fadd float %1316, %1322
  %1324 = call %struct.qtree* @empty_qtree(float %1298, float %1299, float %1300, float %1306, float %1311, float %1323)
  store %struct.qtree* %1324, %struct.qtree** %36, align 8
  %1325 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1326 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1327 = getelementptr inbounds %struct.qtree, %struct.qtree* %1326, i32 0, i32 2
  store %struct.qtree* %1325, %struct.qtree** %1327, align 8
  br label %1366

1328:                                             ; preds = %1294
  %1329 = load float, float* %32, align 4
  %1330 = load float, float* %33, align 4
  %1331 = load float, float* %34, align 4
  %1332 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1333 = getelementptr inbounds %struct.qtree, %struct.qtree* %1332, i32 0, i32 0
  %1334 = load %struct.quad*, %struct.quad** %1333, align 8
  %1335 = getelementptr inbounds %struct.quad, %struct.quad* %1334, i32 0, i32 0
  %1336 = load float, float* %1335, align 8
  %1337 = fdiv float %1336, 2.000000e+00
  %1338 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1339 = getelementptr inbounds %struct.qtree, %struct.qtree* %1338, i32 0, i32 0
  %1340 = load %struct.quad*, %struct.quad** %1339, align 8
  %1341 = getelementptr inbounds %struct.quad, %struct.quad* %1340, i32 0, i32 2
  %1342 = load float, float* %1341, align 8
  %1343 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1344 = getelementptr inbounds %struct.qtree, %struct.qtree* %1343, i32 0, i32 0
  %1345 = load %struct.quad*, %struct.quad** %1344, align 8
  %1346 = getelementptr inbounds %struct.quad, %struct.quad* %1345, i32 0, i32 0
  %1347 = load float, float* %1346, align 8
  %1348 = fdiv float %1347, 2.000000e+00
  %1349 = fadd float %1342, %1348
  %1350 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1351 = getelementptr inbounds %struct.qtree, %struct.qtree* %1350, i32 0, i32 0
  %1352 = load %struct.quad*, %struct.quad** %1351, align 8
  %1353 = getelementptr inbounds %struct.quad, %struct.quad* %1352, i32 0, i32 1
  %1354 = load float, float* %1353, align 4
  %1355 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1356 = getelementptr inbounds %struct.qtree, %struct.qtree* %1355, i32 0, i32 0
  %1357 = load %struct.quad*, %struct.quad** %1356, align 8
  %1358 = getelementptr inbounds %struct.quad, %struct.quad* %1357, i32 0, i32 0
  %1359 = load float, float* %1358, align 8
  %1360 = fdiv float %1359, 2.000000e+00
  %1361 = fadd float %1354, %1360
  %1362 = call %struct.qtree* @empty_qtree(float %1329, float %1330, float %1331, float %1337, float %1349, float %1361)
  store %struct.qtree* %1362, %struct.qtree** %36, align 8
  %1363 = load %struct.qtree*, %struct.qtree** %36, align 8
  %1364 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1365 = getelementptr inbounds %struct.qtree, %struct.qtree* %1364, i32 0, i32 4
  store %struct.qtree* %1363, %struct.qtree** %1365, align 8
  br label %1366

1366:                                             ; preds = %1328, %1297
  br label %1367

1367:                                             ; preds = %1366, %1263
  br label %1368

1368:                                             ; preds = %1367, %1236
  br label %1369

1369:                                             ; preds = %1368, %1200, %1195, %1190, %1185
  %1370 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1371 = getelementptr inbounds %struct.qtree, %struct.qtree* %1370, i32 0, i32 0
  %1372 = load %struct.quad*, %struct.quad** %1371, align 8
  %1373 = getelementptr inbounds %struct.quad, %struct.quad* %1372, i32 0, i32 0
  %1374 = load float, float* %1373, align 8
  store float %1374, float* %37, align 4
  %1375 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1376 = getelementptr inbounds %struct.qtree, %struct.qtree* %1375, i32 0, i32 4
  %1377 = load %struct.qtree*, %struct.qtree** %1376, align 8
  %1378 = icmp eq %struct.qtree* %1377, null
  br i1 %1378, label %1379, label %1404

1379:                                             ; preds = %1369
  %1380 = load float, float* %5, align 4
  %1381 = load float, float* %6, align 4
  %1382 = load float, float* %8, align 4
  %1383 = load float, float* %37, align 4
  %1384 = fdiv float %1383, 2.000000e+00
  %1385 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1386 = getelementptr inbounds %struct.qtree, %struct.qtree* %1385, i32 0, i32 0
  %1387 = load %struct.quad*, %struct.quad** %1386, align 8
  %1388 = getelementptr inbounds %struct.quad, %struct.quad* %1387, i32 0, i32 2
  %1389 = load float, float* %1388, align 8
  %1390 = load float, float* %37, align 4
  %1391 = fdiv float %1390, 2.000000e+00
  %1392 = fadd float %1389, %1391
  %1393 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1394 = getelementptr inbounds %struct.qtree, %struct.qtree* %1393, i32 0, i32 0
  %1395 = load %struct.quad*, %struct.quad** %1394, align 8
  %1396 = getelementptr inbounds %struct.quad, %struct.quad* %1395, i32 0, i32 1
  %1397 = load float, float* %1396, align 4
  %1398 = load float, float* %37, align 4
  %1399 = fdiv float %1398, 2.000000e+00
  %1400 = fadd float %1397, %1399
  %1401 = call %struct.qtree* @empty_qtree(float %1380, float %1381, float %1382, float %1384, float %1392, float %1400)
  %1402 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1403 = getelementptr inbounds %struct.qtree, %struct.qtree* %1402, i32 0, i32 4
  store %struct.qtree* %1401, %struct.qtree** %1403, align 8
  br label %1412

1404:                                             ; preds = %1369
  %1405 = load float, float* %5, align 4
  %1406 = load float, float* %6, align 4
  %1407 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1408 = getelementptr inbounds %struct.qtree, %struct.qtree* %1407, i32 0, i32 4
  %1409 = load %struct.qtree*, %struct.qtree** %1408, align 8
  %1410 = load float, float* %8, align 4
  %1411 = call %struct.qtree* @insertPoint(float %1405, float %1406, %struct.qtree* %1409, float %1410)
  br label %1412

1412:                                             ; preds = %1404, %1379
  %1413 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1414 = getelementptr inbounds %struct.qtree, %struct.qtree* %1413, i32 0, i32 1
  %1415 = load %struct.qtree*, %struct.qtree** %1414, align 8
  %1416 = icmp ne %struct.qtree* %1415, null
  br i1 %1416, label %1417, label %1463

1417:                                             ; preds = %1412
  %1418 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1419 = getelementptr inbounds %struct.qtree, %struct.qtree* %1418, i32 0, i32 1
  %1420 = load %struct.qtree*, %struct.qtree** %1419, align 8
  %1421 = getelementptr inbounds %struct.qtree, %struct.qtree* %1420, i32 0, i32 0
  %1422 = load %struct.quad*, %struct.quad** %1421, align 8
  %1423 = getelementptr inbounds %struct.quad, %struct.quad* %1422, i32 0, i32 3
  %1424 = load %struct.centroid*, %struct.centroid** %1423, align 8
  %1425 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1426 = getelementptr inbounds %struct.qtree, %struct.qtree* %1425, i32 0, i32 4
  %1427 = load %struct.qtree*, %struct.qtree** %1426, align 8
  %1428 = getelementptr inbounds %struct.qtree, %struct.qtree* %1427, i32 0, i32 0
  %1429 = load %struct.quad*, %struct.quad** %1428, align 8
  %1430 = getelementptr inbounds %struct.quad, %struct.quad* %1429, i32 0, i32 3
  %1431 = load %struct.centroid*, %struct.centroid** %1430, align 8
  %1432 = call %struct.centroid* @centroid_sum(%struct.centroid* %1424, %struct.centroid* %1431)
  store %struct.centroid* %1432, %struct.centroid** %38, align 8
  %1433 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1434 = getelementptr inbounds %struct.qtree, %struct.qtree* %1433, i32 0, i32 2
  %1435 = load %struct.qtree*, %struct.qtree** %1434, align 8
  %1436 = icmp ne %struct.qtree* %1435, null
  br i1 %1436, label %1437, label %1447

1437:                                             ; preds = %1417
  %1438 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1439 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1440 = getelementptr inbounds %struct.qtree, %struct.qtree* %1439, i32 0, i32 2
  %1441 = load %struct.qtree*, %struct.qtree** %1440, align 8
  %1442 = getelementptr inbounds %struct.qtree, %struct.qtree* %1441, i32 0, i32 0
  %1443 = load %struct.quad*, %struct.quad** %1442, align 8
  %1444 = getelementptr inbounds %struct.quad, %struct.quad* %1443, i32 0, i32 3
  %1445 = load %struct.centroid*, %struct.centroid** %1444, align 8
  %1446 = call %struct.centroid* @centroid_sum(%struct.centroid* %1438, %struct.centroid* %1445)
  store %struct.centroid* %1446, %struct.centroid** %38, align 8
  br label %1447

1447:                                             ; preds = %1437, %1417
  %1448 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1449 = getelementptr inbounds %struct.qtree, %struct.qtree* %1448, i32 0, i32 3
  %1450 = load %struct.qtree*, %struct.qtree** %1449, align 8
  %1451 = icmp ne %struct.qtree* %1450, null
  br i1 %1451, label %1452, label %1462

1452:                                             ; preds = %1447
  %1453 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1454 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1455 = getelementptr inbounds %struct.qtree, %struct.qtree* %1454, i32 0, i32 3
  %1456 = load %struct.qtree*, %struct.qtree** %1455, align 8
  %1457 = getelementptr inbounds %struct.qtree, %struct.qtree* %1456, i32 0, i32 0
  %1458 = load %struct.quad*, %struct.quad** %1457, align 8
  %1459 = getelementptr inbounds %struct.quad, %struct.quad* %1458, i32 0, i32 3
  %1460 = load %struct.centroid*, %struct.centroid** %1459, align 8
  %1461 = call %struct.centroid* @centroid_sum(%struct.centroid* %1453, %struct.centroid* %1460)
  store %struct.centroid* %1461, %struct.centroid** %38, align 8
  br label %1462

1462:                                             ; preds = %1452, %1447
  br label %1530

1463:                                             ; preds = %1412
  %1464 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1465 = getelementptr inbounds %struct.qtree, %struct.qtree* %1464, i32 0, i32 2
  %1466 = load %struct.qtree*, %struct.qtree** %1465, align 8
  %1467 = icmp ne %struct.qtree* %1466, null
  br i1 %1467, label %1468, label %1499

1468:                                             ; preds = %1463
  %1469 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1470 = getelementptr inbounds %struct.qtree, %struct.qtree* %1469, i32 0, i32 2
  %1471 = load %struct.qtree*, %struct.qtree** %1470, align 8
  %1472 = getelementptr inbounds %struct.qtree, %struct.qtree* %1471, i32 0, i32 0
  %1473 = load %struct.quad*, %struct.quad** %1472, align 8
  %1474 = getelementptr inbounds %struct.quad, %struct.quad* %1473, i32 0, i32 3
  %1475 = load %struct.centroid*, %struct.centroid** %1474, align 8
  %1476 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1477 = getelementptr inbounds %struct.qtree, %struct.qtree* %1476, i32 0, i32 4
  %1478 = load %struct.qtree*, %struct.qtree** %1477, align 8
  %1479 = getelementptr inbounds %struct.qtree, %struct.qtree* %1478, i32 0, i32 0
  %1480 = load %struct.quad*, %struct.quad** %1479, align 8
  %1481 = getelementptr inbounds %struct.quad, %struct.quad* %1480, i32 0, i32 3
  %1482 = load %struct.centroid*, %struct.centroid** %1481, align 8
  %1483 = call %struct.centroid* @centroid_sum(%struct.centroid* %1475, %struct.centroid* %1482)
  store %struct.centroid* %1483, %struct.centroid** %38, align 8
  %1484 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1485 = getelementptr inbounds %struct.qtree, %struct.qtree* %1484, i32 0, i32 3
  %1486 = load %struct.qtree*, %struct.qtree** %1485, align 8
  %1487 = icmp ne %struct.qtree* %1486, null
  br i1 %1487, label %1488, label %1498

1488:                                             ; preds = %1468
  %1489 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1490 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1491 = getelementptr inbounds %struct.qtree, %struct.qtree* %1490, i32 0, i32 3
  %1492 = load %struct.qtree*, %struct.qtree** %1491, align 8
  %1493 = getelementptr inbounds %struct.qtree, %struct.qtree* %1492, i32 0, i32 0
  %1494 = load %struct.quad*, %struct.quad** %1493, align 8
  %1495 = getelementptr inbounds %struct.quad, %struct.quad* %1494, i32 0, i32 3
  %1496 = load %struct.centroid*, %struct.centroid** %1495, align 8
  %1497 = call %struct.centroid* @centroid_sum(%struct.centroid* %1489, %struct.centroid* %1496)
  store %struct.centroid* %1497, %struct.centroid** %38, align 8
  br label %1498

1498:                                             ; preds = %1488, %1468
  br label %1529

1499:                                             ; preds = %1463
  %1500 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1501 = getelementptr inbounds %struct.qtree, %struct.qtree* %1500, i32 0, i32 3
  %1502 = load %struct.qtree*, %struct.qtree** %1501, align 8
  %1503 = icmp ne %struct.qtree* %1502, null
  br i1 %1503, label %1504, label %1520

1504:                                             ; preds = %1499
  %1505 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1506 = getelementptr inbounds %struct.qtree, %struct.qtree* %1505, i32 0, i32 3
  %1507 = load %struct.qtree*, %struct.qtree** %1506, align 8
  %1508 = getelementptr inbounds %struct.qtree, %struct.qtree* %1507, i32 0, i32 0
  %1509 = load %struct.quad*, %struct.quad** %1508, align 8
  %1510 = getelementptr inbounds %struct.quad, %struct.quad* %1509, i32 0, i32 3
  %1511 = load %struct.centroid*, %struct.centroid** %1510, align 8
  %1512 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1513 = getelementptr inbounds %struct.qtree, %struct.qtree* %1512, i32 0, i32 4
  %1514 = load %struct.qtree*, %struct.qtree** %1513, align 8
  %1515 = getelementptr inbounds %struct.qtree, %struct.qtree* %1514, i32 0, i32 0
  %1516 = load %struct.quad*, %struct.quad** %1515, align 8
  %1517 = getelementptr inbounds %struct.quad, %struct.quad* %1516, i32 0, i32 3
  %1518 = load %struct.centroid*, %struct.centroid** %1517, align 8
  %1519 = call %struct.centroid* @centroid_sum(%struct.centroid* %1511, %struct.centroid* %1518)
  store %struct.centroid* %1519, %struct.centroid** %38, align 8
  br label %1528

1520:                                             ; preds = %1499
  %1521 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1522 = getelementptr inbounds %struct.qtree, %struct.qtree* %1521, i32 0, i32 4
  %1523 = load %struct.qtree*, %struct.qtree** %1522, align 8
  %1524 = getelementptr inbounds %struct.qtree, %struct.qtree* %1523, i32 0, i32 0
  %1525 = load %struct.quad*, %struct.quad** %1524, align 8
  %1526 = getelementptr inbounds %struct.quad, %struct.quad* %1525, i32 0, i32 3
  %1527 = load %struct.centroid*, %struct.centroid** %1526, align 8
  store %struct.centroid* %1527, %struct.centroid** %38, align 8
  br label %1528

1528:                                             ; preds = %1520, %1504
  br label %1529

1529:                                             ; preds = %1528, %1498
  br label %1530

1530:                                             ; preds = %1529, %1462
  %1531 = load %struct.centroid*, %struct.centroid** %38, align 8
  %1532 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1533 = getelementptr inbounds %struct.qtree, %struct.qtree* %1532, i32 0, i32 0
  %1534 = load %struct.quad*, %struct.quad** %1533, align 8
  %1535 = getelementptr inbounds %struct.quad, %struct.quad* %1534, i32 0, i32 3
  store %struct.centroid* %1531, %struct.centroid** %1535, align 8
  br label %2104

1536:                                             ; preds = %1180, %1172
  %1537 = load float, float* %5, align 4
  %1538 = load float, float* %6, align 4
  %1539 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1540 = getelementptr inbounds %struct.qtree, %struct.qtree* %1539, i32 0, i32 0
  %1541 = load %struct.quad*, %struct.quad** %1540, align 8
  %1542 = call i32 @which_quad(float %1537, float %1538, %struct.quad* %1541)
  %1543 = icmp eq i32 %1542, 1
  br i1 %1543, label %1544, label %1677

1544:                                             ; preds = %1536
  %1545 = load float, float* %5, align 4
  %1546 = load float, float* %6, align 4
  %1547 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1548 = getelementptr inbounds %struct.qtree, %struct.qtree* %1547, i32 0, i32 1
  %1549 = load %struct.qtree*, %struct.qtree** %1548, align 8
  %1550 = load float, float* %8, align 4
  %1551 = call %struct.qtree* @insertPoint(float %1545, float %1546, %struct.qtree* %1549, float %1550)
  %1552 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1553 = getelementptr inbounds %struct.qtree, %struct.qtree* %1552, i32 0, i32 1
  store %struct.qtree* %1551, %struct.qtree** %1553, align 8
  %1554 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1555 = getelementptr inbounds %struct.qtree, %struct.qtree* %1554, i32 0, i32 2
  %1556 = load %struct.qtree*, %struct.qtree** %1555, align 8
  %1557 = icmp ne %struct.qtree* %1556, null
  br i1 %1557, label %1558, label %1604

1558:                                             ; preds = %1544
  %1559 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1560 = getelementptr inbounds %struct.qtree, %struct.qtree* %1559, i32 0, i32 1
  %1561 = load %struct.qtree*, %struct.qtree** %1560, align 8
  %1562 = getelementptr inbounds %struct.qtree, %struct.qtree* %1561, i32 0, i32 0
  %1563 = load %struct.quad*, %struct.quad** %1562, align 8
  %1564 = getelementptr inbounds %struct.quad, %struct.quad* %1563, i32 0, i32 3
  %1565 = load %struct.centroid*, %struct.centroid** %1564, align 8
  %1566 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1567 = getelementptr inbounds %struct.qtree, %struct.qtree* %1566, i32 0, i32 2
  %1568 = load %struct.qtree*, %struct.qtree** %1567, align 8
  %1569 = getelementptr inbounds %struct.qtree, %struct.qtree* %1568, i32 0, i32 0
  %1570 = load %struct.quad*, %struct.quad** %1569, align 8
  %1571 = getelementptr inbounds %struct.quad, %struct.quad* %1570, i32 0, i32 3
  %1572 = load %struct.centroid*, %struct.centroid** %1571, align 8
  %1573 = call %struct.centroid* @centroid_sum(%struct.centroid* %1565, %struct.centroid* %1572)
  store %struct.centroid* %1573, %struct.centroid** %39, align 8
  %1574 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1575 = getelementptr inbounds %struct.qtree, %struct.qtree* %1574, i32 0, i32 4
  %1576 = load %struct.qtree*, %struct.qtree** %1575, align 8
  %1577 = icmp ne %struct.qtree* %1576, null
  br i1 %1577, label %1578, label %1588

1578:                                             ; preds = %1558
  %1579 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1580 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1581 = getelementptr inbounds %struct.qtree, %struct.qtree* %1580, i32 0, i32 4
  %1582 = load %struct.qtree*, %struct.qtree** %1581, align 8
  %1583 = getelementptr inbounds %struct.qtree, %struct.qtree* %1582, i32 0, i32 0
  %1584 = load %struct.quad*, %struct.quad** %1583, align 8
  %1585 = getelementptr inbounds %struct.quad, %struct.quad* %1584, i32 0, i32 3
  %1586 = load %struct.centroid*, %struct.centroid** %1585, align 8
  %1587 = call %struct.centroid* @centroid_sum(%struct.centroid* %1579, %struct.centroid* %1586)
  store %struct.centroid* %1587, %struct.centroid** %39, align 8
  br label %1588

1588:                                             ; preds = %1578, %1558
  %1589 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1590 = getelementptr inbounds %struct.qtree, %struct.qtree* %1589, i32 0, i32 3
  %1591 = load %struct.qtree*, %struct.qtree** %1590, align 8
  %1592 = icmp ne %struct.qtree* %1591, null
  br i1 %1592, label %1593, label %1603

1593:                                             ; preds = %1588
  %1594 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1595 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1596 = getelementptr inbounds %struct.qtree, %struct.qtree* %1595, i32 0, i32 3
  %1597 = load %struct.qtree*, %struct.qtree** %1596, align 8
  %1598 = getelementptr inbounds %struct.qtree, %struct.qtree* %1597, i32 0, i32 0
  %1599 = load %struct.quad*, %struct.quad** %1598, align 8
  %1600 = getelementptr inbounds %struct.quad, %struct.quad* %1599, i32 0, i32 3
  %1601 = load %struct.centroid*, %struct.centroid** %1600, align 8
  %1602 = call %struct.centroid* @centroid_sum(%struct.centroid* %1594, %struct.centroid* %1601)
  store %struct.centroid* %1602, %struct.centroid** %39, align 8
  br label %1603

1603:                                             ; preds = %1593, %1588
  br label %1671

1604:                                             ; preds = %1544
  %1605 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1606 = getelementptr inbounds %struct.qtree, %struct.qtree* %1605, i32 0, i32 3
  %1607 = load %struct.qtree*, %struct.qtree** %1606, align 8
  %1608 = icmp ne %struct.qtree* %1607, null
  br i1 %1608, label %1609, label %1640

1609:                                             ; preds = %1604
  %1610 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1611 = getelementptr inbounds %struct.qtree, %struct.qtree* %1610, i32 0, i32 1
  %1612 = load %struct.qtree*, %struct.qtree** %1611, align 8
  %1613 = getelementptr inbounds %struct.qtree, %struct.qtree* %1612, i32 0, i32 0
  %1614 = load %struct.quad*, %struct.quad** %1613, align 8
  %1615 = getelementptr inbounds %struct.quad, %struct.quad* %1614, i32 0, i32 3
  %1616 = load %struct.centroid*, %struct.centroid** %1615, align 8
  %1617 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1618 = getelementptr inbounds %struct.qtree, %struct.qtree* %1617, i32 0, i32 3
  %1619 = load %struct.qtree*, %struct.qtree** %1618, align 8
  %1620 = getelementptr inbounds %struct.qtree, %struct.qtree* %1619, i32 0, i32 0
  %1621 = load %struct.quad*, %struct.quad** %1620, align 8
  %1622 = getelementptr inbounds %struct.quad, %struct.quad* %1621, i32 0, i32 3
  %1623 = load %struct.centroid*, %struct.centroid** %1622, align 8
  %1624 = call %struct.centroid* @centroid_sum(%struct.centroid* %1616, %struct.centroid* %1623)
  store %struct.centroid* %1624, %struct.centroid** %39, align 8
  %1625 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1626 = getelementptr inbounds %struct.qtree, %struct.qtree* %1625, i32 0, i32 4
  %1627 = load %struct.qtree*, %struct.qtree** %1626, align 8
  %1628 = icmp ne %struct.qtree* %1627, null
  br i1 %1628, label %1629, label %1639

1629:                                             ; preds = %1609
  %1630 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1631 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1632 = getelementptr inbounds %struct.qtree, %struct.qtree* %1631, i32 0, i32 4
  %1633 = load %struct.qtree*, %struct.qtree** %1632, align 8
  %1634 = getelementptr inbounds %struct.qtree, %struct.qtree* %1633, i32 0, i32 0
  %1635 = load %struct.quad*, %struct.quad** %1634, align 8
  %1636 = getelementptr inbounds %struct.quad, %struct.quad* %1635, i32 0, i32 3
  %1637 = load %struct.centroid*, %struct.centroid** %1636, align 8
  %1638 = call %struct.centroid* @centroid_sum(%struct.centroid* %1630, %struct.centroid* %1637)
  store %struct.centroid* %1638, %struct.centroid** %39, align 8
  br label %1639

1639:                                             ; preds = %1629, %1609
  br label %1670

1640:                                             ; preds = %1604
  %1641 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1642 = getelementptr inbounds %struct.qtree, %struct.qtree* %1641, i32 0, i32 4
  %1643 = load %struct.qtree*, %struct.qtree** %1642, align 8
  %1644 = icmp ne %struct.qtree* %1643, null
  br i1 %1644, label %1645, label %1661

1645:                                             ; preds = %1640
  %1646 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1647 = getelementptr inbounds %struct.qtree, %struct.qtree* %1646, i32 0, i32 1
  %1648 = load %struct.qtree*, %struct.qtree** %1647, align 8
  %1649 = getelementptr inbounds %struct.qtree, %struct.qtree* %1648, i32 0, i32 0
  %1650 = load %struct.quad*, %struct.quad** %1649, align 8
  %1651 = getelementptr inbounds %struct.quad, %struct.quad* %1650, i32 0, i32 3
  %1652 = load %struct.centroid*, %struct.centroid** %1651, align 8
  %1653 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1654 = getelementptr inbounds %struct.qtree, %struct.qtree* %1653, i32 0, i32 4
  %1655 = load %struct.qtree*, %struct.qtree** %1654, align 8
  %1656 = getelementptr inbounds %struct.qtree, %struct.qtree* %1655, i32 0, i32 0
  %1657 = load %struct.quad*, %struct.quad** %1656, align 8
  %1658 = getelementptr inbounds %struct.quad, %struct.quad* %1657, i32 0, i32 3
  %1659 = load %struct.centroid*, %struct.centroid** %1658, align 8
  %1660 = call %struct.centroid* @centroid_sum(%struct.centroid* %1652, %struct.centroid* %1659)
  store %struct.centroid* %1660, %struct.centroid** %39, align 8
  br label %1669

1661:                                             ; preds = %1640
  %1662 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1663 = getelementptr inbounds %struct.qtree, %struct.qtree* %1662, i32 0, i32 1
  %1664 = load %struct.qtree*, %struct.qtree** %1663, align 8
  %1665 = getelementptr inbounds %struct.qtree, %struct.qtree* %1664, i32 0, i32 0
  %1666 = load %struct.quad*, %struct.quad** %1665, align 8
  %1667 = getelementptr inbounds %struct.quad, %struct.quad* %1666, i32 0, i32 3
  %1668 = load %struct.centroid*, %struct.centroid** %1667, align 8
  store %struct.centroid* %1668, %struct.centroid** %39, align 8
  br label %1669

1669:                                             ; preds = %1661, %1645
  br label %1670

1670:                                             ; preds = %1669, %1639
  br label %1671

1671:                                             ; preds = %1670, %1603
  %1672 = load %struct.centroid*, %struct.centroid** %39, align 8
  %1673 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1674 = getelementptr inbounds %struct.qtree, %struct.qtree* %1673, i32 0, i32 0
  %1675 = load %struct.quad*, %struct.quad** %1674, align 8
  %1676 = getelementptr inbounds %struct.quad, %struct.quad* %1675, i32 0, i32 3
  store %struct.centroid* %1672, %struct.centroid** %1676, align 8
  br label %2103

1677:                                             ; preds = %1536
  %1678 = load float, float* %5, align 4
  %1679 = load float, float* %6, align 4
  %1680 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1681 = getelementptr inbounds %struct.qtree, %struct.qtree* %1680, i32 0, i32 0
  %1682 = load %struct.quad*, %struct.quad** %1681, align 8
  %1683 = call i32 @which_quad(float %1678, float %1679, %struct.quad* %1682)
  %1684 = icmp eq i32 %1683, 2
  br i1 %1684, label %1685, label %1818

1685:                                             ; preds = %1677
  %1686 = load float, float* %5, align 4
  %1687 = load float, float* %6, align 4
  %1688 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1689 = getelementptr inbounds %struct.qtree, %struct.qtree* %1688, i32 0, i32 2
  %1690 = load %struct.qtree*, %struct.qtree** %1689, align 8
  %1691 = load float, float* %8, align 4
  %1692 = call %struct.qtree* @insertPoint(float %1686, float %1687, %struct.qtree* %1690, float %1691)
  %1693 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1694 = getelementptr inbounds %struct.qtree, %struct.qtree* %1693, i32 0, i32 2
  store %struct.qtree* %1692, %struct.qtree** %1694, align 8
  %1695 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1696 = getelementptr inbounds %struct.qtree, %struct.qtree* %1695, i32 0, i32 1
  %1697 = load %struct.qtree*, %struct.qtree** %1696, align 8
  %1698 = icmp ne %struct.qtree* %1697, null
  br i1 %1698, label %1699, label %1745

1699:                                             ; preds = %1685
  %1700 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1701 = getelementptr inbounds %struct.qtree, %struct.qtree* %1700, i32 0, i32 1
  %1702 = load %struct.qtree*, %struct.qtree** %1701, align 8
  %1703 = getelementptr inbounds %struct.qtree, %struct.qtree* %1702, i32 0, i32 0
  %1704 = load %struct.quad*, %struct.quad** %1703, align 8
  %1705 = getelementptr inbounds %struct.quad, %struct.quad* %1704, i32 0, i32 3
  %1706 = load %struct.centroid*, %struct.centroid** %1705, align 8
  %1707 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1708 = getelementptr inbounds %struct.qtree, %struct.qtree* %1707, i32 0, i32 2
  %1709 = load %struct.qtree*, %struct.qtree** %1708, align 8
  %1710 = getelementptr inbounds %struct.qtree, %struct.qtree* %1709, i32 0, i32 0
  %1711 = load %struct.quad*, %struct.quad** %1710, align 8
  %1712 = getelementptr inbounds %struct.quad, %struct.quad* %1711, i32 0, i32 3
  %1713 = load %struct.centroid*, %struct.centroid** %1712, align 8
  %1714 = call %struct.centroid* @centroid_sum(%struct.centroid* %1706, %struct.centroid* %1713)
  store %struct.centroid* %1714, %struct.centroid** %40, align 8
  %1715 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1716 = getelementptr inbounds %struct.qtree, %struct.qtree* %1715, i32 0, i32 4
  %1717 = load %struct.qtree*, %struct.qtree** %1716, align 8
  %1718 = icmp ne %struct.qtree* %1717, null
  br i1 %1718, label %1719, label %1729

1719:                                             ; preds = %1699
  %1720 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1721 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1722 = getelementptr inbounds %struct.qtree, %struct.qtree* %1721, i32 0, i32 4
  %1723 = load %struct.qtree*, %struct.qtree** %1722, align 8
  %1724 = getelementptr inbounds %struct.qtree, %struct.qtree* %1723, i32 0, i32 0
  %1725 = load %struct.quad*, %struct.quad** %1724, align 8
  %1726 = getelementptr inbounds %struct.quad, %struct.quad* %1725, i32 0, i32 3
  %1727 = load %struct.centroid*, %struct.centroid** %1726, align 8
  %1728 = call %struct.centroid* @centroid_sum(%struct.centroid* %1720, %struct.centroid* %1727)
  store %struct.centroid* %1728, %struct.centroid** %40, align 8
  br label %1729

1729:                                             ; preds = %1719, %1699
  %1730 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1731 = getelementptr inbounds %struct.qtree, %struct.qtree* %1730, i32 0, i32 3
  %1732 = load %struct.qtree*, %struct.qtree** %1731, align 8
  %1733 = icmp ne %struct.qtree* %1732, null
  br i1 %1733, label %1734, label %1744

1734:                                             ; preds = %1729
  %1735 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1736 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1737 = getelementptr inbounds %struct.qtree, %struct.qtree* %1736, i32 0, i32 3
  %1738 = load %struct.qtree*, %struct.qtree** %1737, align 8
  %1739 = getelementptr inbounds %struct.qtree, %struct.qtree* %1738, i32 0, i32 0
  %1740 = load %struct.quad*, %struct.quad** %1739, align 8
  %1741 = getelementptr inbounds %struct.quad, %struct.quad* %1740, i32 0, i32 3
  %1742 = load %struct.centroid*, %struct.centroid** %1741, align 8
  %1743 = call %struct.centroid* @centroid_sum(%struct.centroid* %1735, %struct.centroid* %1742)
  store %struct.centroid* %1743, %struct.centroid** %40, align 8
  br label %1744

1744:                                             ; preds = %1734, %1729
  br label %1812

1745:                                             ; preds = %1685
  %1746 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1747 = getelementptr inbounds %struct.qtree, %struct.qtree* %1746, i32 0, i32 4
  %1748 = load %struct.qtree*, %struct.qtree** %1747, align 8
  %1749 = icmp ne %struct.qtree* %1748, null
  br i1 %1749, label %1750, label %1781

1750:                                             ; preds = %1745
  %1751 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1752 = getelementptr inbounds %struct.qtree, %struct.qtree* %1751, i32 0, i32 2
  %1753 = load %struct.qtree*, %struct.qtree** %1752, align 8
  %1754 = getelementptr inbounds %struct.qtree, %struct.qtree* %1753, i32 0, i32 0
  %1755 = load %struct.quad*, %struct.quad** %1754, align 8
  %1756 = getelementptr inbounds %struct.quad, %struct.quad* %1755, i32 0, i32 3
  %1757 = load %struct.centroid*, %struct.centroid** %1756, align 8
  %1758 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1759 = getelementptr inbounds %struct.qtree, %struct.qtree* %1758, i32 0, i32 4
  %1760 = load %struct.qtree*, %struct.qtree** %1759, align 8
  %1761 = getelementptr inbounds %struct.qtree, %struct.qtree* %1760, i32 0, i32 0
  %1762 = load %struct.quad*, %struct.quad** %1761, align 8
  %1763 = getelementptr inbounds %struct.quad, %struct.quad* %1762, i32 0, i32 3
  %1764 = load %struct.centroid*, %struct.centroid** %1763, align 8
  %1765 = call %struct.centroid* @centroid_sum(%struct.centroid* %1757, %struct.centroid* %1764)
  store %struct.centroid* %1765, %struct.centroid** %40, align 8
  %1766 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1767 = getelementptr inbounds %struct.qtree, %struct.qtree* %1766, i32 0, i32 3
  %1768 = load %struct.qtree*, %struct.qtree** %1767, align 8
  %1769 = icmp ne %struct.qtree* %1768, null
  br i1 %1769, label %1770, label %1780

1770:                                             ; preds = %1750
  %1771 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1772 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1773 = getelementptr inbounds %struct.qtree, %struct.qtree* %1772, i32 0, i32 3
  %1774 = load %struct.qtree*, %struct.qtree** %1773, align 8
  %1775 = getelementptr inbounds %struct.qtree, %struct.qtree* %1774, i32 0, i32 0
  %1776 = load %struct.quad*, %struct.quad** %1775, align 8
  %1777 = getelementptr inbounds %struct.quad, %struct.quad* %1776, i32 0, i32 3
  %1778 = load %struct.centroid*, %struct.centroid** %1777, align 8
  %1779 = call %struct.centroid* @centroid_sum(%struct.centroid* %1771, %struct.centroid* %1778)
  store %struct.centroid* %1779, %struct.centroid** %40, align 8
  br label %1780

1780:                                             ; preds = %1770, %1750
  br label %1811

1781:                                             ; preds = %1745
  %1782 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1783 = getelementptr inbounds %struct.qtree, %struct.qtree* %1782, i32 0, i32 3
  %1784 = load %struct.qtree*, %struct.qtree** %1783, align 8
  %1785 = icmp ne %struct.qtree* %1784, null
  br i1 %1785, label %1786, label %1802

1786:                                             ; preds = %1781
  %1787 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1788 = getelementptr inbounds %struct.qtree, %struct.qtree* %1787, i32 0, i32 2
  %1789 = load %struct.qtree*, %struct.qtree** %1788, align 8
  %1790 = getelementptr inbounds %struct.qtree, %struct.qtree* %1789, i32 0, i32 0
  %1791 = load %struct.quad*, %struct.quad** %1790, align 8
  %1792 = getelementptr inbounds %struct.quad, %struct.quad* %1791, i32 0, i32 3
  %1793 = load %struct.centroid*, %struct.centroid** %1792, align 8
  %1794 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1795 = getelementptr inbounds %struct.qtree, %struct.qtree* %1794, i32 0, i32 3
  %1796 = load %struct.qtree*, %struct.qtree** %1795, align 8
  %1797 = getelementptr inbounds %struct.qtree, %struct.qtree* %1796, i32 0, i32 0
  %1798 = load %struct.quad*, %struct.quad** %1797, align 8
  %1799 = getelementptr inbounds %struct.quad, %struct.quad* %1798, i32 0, i32 3
  %1800 = load %struct.centroid*, %struct.centroid** %1799, align 8
  %1801 = call %struct.centroid* @centroid_sum(%struct.centroid* %1793, %struct.centroid* %1800)
  store %struct.centroid* %1801, %struct.centroid** %40, align 8
  br label %1810

1802:                                             ; preds = %1781
  %1803 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1804 = getelementptr inbounds %struct.qtree, %struct.qtree* %1803, i32 0, i32 2
  %1805 = load %struct.qtree*, %struct.qtree** %1804, align 8
  %1806 = getelementptr inbounds %struct.qtree, %struct.qtree* %1805, i32 0, i32 0
  %1807 = load %struct.quad*, %struct.quad** %1806, align 8
  %1808 = getelementptr inbounds %struct.quad, %struct.quad* %1807, i32 0, i32 3
  %1809 = load %struct.centroid*, %struct.centroid** %1808, align 8
  store %struct.centroid* %1809, %struct.centroid** %40, align 8
  br label %1810

1810:                                             ; preds = %1802, %1786
  br label %1811

1811:                                             ; preds = %1810, %1780
  br label %1812

1812:                                             ; preds = %1811, %1744
  %1813 = load %struct.centroid*, %struct.centroid** %40, align 8
  %1814 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1815 = getelementptr inbounds %struct.qtree, %struct.qtree* %1814, i32 0, i32 0
  %1816 = load %struct.quad*, %struct.quad** %1815, align 8
  %1817 = getelementptr inbounds %struct.quad, %struct.quad* %1816, i32 0, i32 3
  store %struct.centroid* %1813, %struct.centroid** %1817, align 8
  br label %2102

1818:                                             ; preds = %1677
  %1819 = load float, float* %5, align 4
  %1820 = load float, float* %6, align 4
  %1821 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1822 = getelementptr inbounds %struct.qtree, %struct.qtree* %1821, i32 0, i32 0
  %1823 = load %struct.quad*, %struct.quad** %1822, align 8
  %1824 = call i32 @which_quad(float %1819, float %1820, %struct.quad* %1823)
  %1825 = icmp eq i32 %1824, 3
  br i1 %1825, label %1826, label %1959

1826:                                             ; preds = %1818
  %1827 = load float, float* %5, align 4
  %1828 = load float, float* %6, align 4
  %1829 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1830 = getelementptr inbounds %struct.qtree, %struct.qtree* %1829, i32 0, i32 3
  %1831 = load %struct.qtree*, %struct.qtree** %1830, align 8
  %1832 = load float, float* %8, align 4
  %1833 = call %struct.qtree* @insertPoint(float %1827, float %1828, %struct.qtree* %1831, float %1832)
  %1834 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1835 = getelementptr inbounds %struct.qtree, %struct.qtree* %1834, i32 0, i32 3
  store %struct.qtree* %1833, %struct.qtree** %1835, align 8
  %1836 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1837 = getelementptr inbounds %struct.qtree, %struct.qtree* %1836, i32 0, i32 1
  %1838 = load %struct.qtree*, %struct.qtree** %1837, align 8
  %1839 = icmp ne %struct.qtree* %1838, null
  br i1 %1839, label %1840, label %1886

1840:                                             ; preds = %1826
  %1841 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1842 = getelementptr inbounds %struct.qtree, %struct.qtree* %1841, i32 0, i32 1
  %1843 = load %struct.qtree*, %struct.qtree** %1842, align 8
  %1844 = getelementptr inbounds %struct.qtree, %struct.qtree* %1843, i32 0, i32 0
  %1845 = load %struct.quad*, %struct.quad** %1844, align 8
  %1846 = getelementptr inbounds %struct.quad, %struct.quad* %1845, i32 0, i32 3
  %1847 = load %struct.centroid*, %struct.centroid** %1846, align 8
  %1848 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1849 = getelementptr inbounds %struct.qtree, %struct.qtree* %1848, i32 0, i32 3
  %1850 = load %struct.qtree*, %struct.qtree** %1849, align 8
  %1851 = getelementptr inbounds %struct.qtree, %struct.qtree* %1850, i32 0, i32 0
  %1852 = load %struct.quad*, %struct.quad** %1851, align 8
  %1853 = getelementptr inbounds %struct.quad, %struct.quad* %1852, i32 0, i32 3
  %1854 = load %struct.centroid*, %struct.centroid** %1853, align 8
  %1855 = call %struct.centroid* @centroid_sum(%struct.centroid* %1847, %struct.centroid* %1854)
  store %struct.centroid* %1855, %struct.centroid** %41, align 8
  %1856 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1857 = getelementptr inbounds %struct.qtree, %struct.qtree* %1856, i32 0, i32 2
  %1858 = load %struct.qtree*, %struct.qtree** %1857, align 8
  %1859 = icmp ne %struct.qtree* %1858, null
  br i1 %1859, label %1860, label %1870

1860:                                             ; preds = %1840
  %1861 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1862 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1863 = getelementptr inbounds %struct.qtree, %struct.qtree* %1862, i32 0, i32 2
  %1864 = load %struct.qtree*, %struct.qtree** %1863, align 8
  %1865 = getelementptr inbounds %struct.qtree, %struct.qtree* %1864, i32 0, i32 0
  %1866 = load %struct.quad*, %struct.quad** %1865, align 8
  %1867 = getelementptr inbounds %struct.quad, %struct.quad* %1866, i32 0, i32 3
  %1868 = load %struct.centroid*, %struct.centroid** %1867, align 8
  %1869 = call %struct.centroid* @centroid_sum(%struct.centroid* %1861, %struct.centroid* %1868)
  store %struct.centroid* %1869, %struct.centroid** %41, align 8
  br label %1870

1870:                                             ; preds = %1860, %1840
  %1871 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1872 = getelementptr inbounds %struct.qtree, %struct.qtree* %1871, i32 0, i32 4
  %1873 = load %struct.qtree*, %struct.qtree** %1872, align 8
  %1874 = icmp ne %struct.qtree* %1873, null
  br i1 %1874, label %1875, label %1885

1875:                                             ; preds = %1870
  %1876 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1877 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1878 = getelementptr inbounds %struct.qtree, %struct.qtree* %1877, i32 0, i32 4
  %1879 = load %struct.qtree*, %struct.qtree** %1878, align 8
  %1880 = getelementptr inbounds %struct.qtree, %struct.qtree* %1879, i32 0, i32 0
  %1881 = load %struct.quad*, %struct.quad** %1880, align 8
  %1882 = getelementptr inbounds %struct.quad, %struct.quad* %1881, i32 0, i32 3
  %1883 = load %struct.centroid*, %struct.centroid** %1882, align 8
  %1884 = call %struct.centroid* @centroid_sum(%struct.centroid* %1876, %struct.centroid* %1883)
  store %struct.centroid* %1884, %struct.centroid** %41, align 8
  br label %1885

1885:                                             ; preds = %1875, %1870
  br label %1953

1886:                                             ; preds = %1826
  %1887 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1888 = getelementptr inbounds %struct.qtree, %struct.qtree* %1887, i32 0, i32 2
  %1889 = load %struct.qtree*, %struct.qtree** %1888, align 8
  %1890 = icmp ne %struct.qtree* %1889, null
  br i1 %1890, label %1891, label %1922

1891:                                             ; preds = %1886
  %1892 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1893 = getelementptr inbounds %struct.qtree, %struct.qtree* %1892, i32 0, i32 2
  %1894 = load %struct.qtree*, %struct.qtree** %1893, align 8
  %1895 = getelementptr inbounds %struct.qtree, %struct.qtree* %1894, i32 0, i32 0
  %1896 = load %struct.quad*, %struct.quad** %1895, align 8
  %1897 = getelementptr inbounds %struct.quad, %struct.quad* %1896, i32 0, i32 3
  %1898 = load %struct.centroid*, %struct.centroid** %1897, align 8
  %1899 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1900 = getelementptr inbounds %struct.qtree, %struct.qtree* %1899, i32 0, i32 3
  %1901 = load %struct.qtree*, %struct.qtree** %1900, align 8
  %1902 = getelementptr inbounds %struct.qtree, %struct.qtree* %1901, i32 0, i32 0
  %1903 = load %struct.quad*, %struct.quad** %1902, align 8
  %1904 = getelementptr inbounds %struct.quad, %struct.quad* %1903, i32 0, i32 3
  %1905 = load %struct.centroid*, %struct.centroid** %1904, align 8
  %1906 = call %struct.centroid* @centroid_sum(%struct.centroid* %1898, %struct.centroid* %1905)
  store %struct.centroid* %1906, %struct.centroid** %41, align 8
  %1907 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1908 = getelementptr inbounds %struct.qtree, %struct.qtree* %1907, i32 0, i32 4
  %1909 = load %struct.qtree*, %struct.qtree** %1908, align 8
  %1910 = icmp ne %struct.qtree* %1909, null
  br i1 %1910, label %1911, label %1921

1911:                                             ; preds = %1891
  %1912 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1913 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1914 = getelementptr inbounds %struct.qtree, %struct.qtree* %1913, i32 0, i32 4
  %1915 = load %struct.qtree*, %struct.qtree** %1914, align 8
  %1916 = getelementptr inbounds %struct.qtree, %struct.qtree* %1915, i32 0, i32 0
  %1917 = load %struct.quad*, %struct.quad** %1916, align 8
  %1918 = getelementptr inbounds %struct.quad, %struct.quad* %1917, i32 0, i32 3
  %1919 = load %struct.centroid*, %struct.centroid** %1918, align 8
  %1920 = call %struct.centroid* @centroid_sum(%struct.centroid* %1912, %struct.centroid* %1919)
  store %struct.centroid* %1920, %struct.centroid** %41, align 8
  br label %1921

1921:                                             ; preds = %1911, %1891
  br label %1952

1922:                                             ; preds = %1886
  %1923 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1924 = getelementptr inbounds %struct.qtree, %struct.qtree* %1923, i32 0, i32 4
  %1925 = load %struct.qtree*, %struct.qtree** %1924, align 8
  %1926 = icmp ne %struct.qtree* %1925, null
  br i1 %1926, label %1927, label %1943

1927:                                             ; preds = %1922
  %1928 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1929 = getelementptr inbounds %struct.qtree, %struct.qtree* %1928, i32 0, i32 3
  %1930 = load %struct.qtree*, %struct.qtree** %1929, align 8
  %1931 = getelementptr inbounds %struct.qtree, %struct.qtree* %1930, i32 0, i32 0
  %1932 = load %struct.quad*, %struct.quad** %1931, align 8
  %1933 = getelementptr inbounds %struct.quad, %struct.quad* %1932, i32 0, i32 3
  %1934 = load %struct.centroid*, %struct.centroid** %1933, align 8
  %1935 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1936 = getelementptr inbounds %struct.qtree, %struct.qtree* %1935, i32 0, i32 4
  %1937 = load %struct.qtree*, %struct.qtree** %1936, align 8
  %1938 = getelementptr inbounds %struct.qtree, %struct.qtree* %1937, i32 0, i32 0
  %1939 = load %struct.quad*, %struct.quad** %1938, align 8
  %1940 = getelementptr inbounds %struct.quad, %struct.quad* %1939, i32 0, i32 3
  %1941 = load %struct.centroid*, %struct.centroid** %1940, align 8
  %1942 = call %struct.centroid* @centroid_sum(%struct.centroid* %1934, %struct.centroid* %1941)
  store %struct.centroid* %1942, %struct.centroid** %41, align 8
  br label %1951

1943:                                             ; preds = %1922
  %1944 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1945 = getelementptr inbounds %struct.qtree, %struct.qtree* %1944, i32 0, i32 3
  %1946 = load %struct.qtree*, %struct.qtree** %1945, align 8
  %1947 = getelementptr inbounds %struct.qtree, %struct.qtree* %1946, i32 0, i32 0
  %1948 = load %struct.quad*, %struct.quad** %1947, align 8
  %1949 = getelementptr inbounds %struct.quad, %struct.quad* %1948, i32 0, i32 3
  %1950 = load %struct.centroid*, %struct.centroid** %1949, align 8
  store %struct.centroid* %1950, %struct.centroid** %41, align 8
  br label %1951

1951:                                             ; preds = %1943, %1927
  br label %1952

1952:                                             ; preds = %1951, %1921
  br label %1953

1953:                                             ; preds = %1952, %1885
  %1954 = load %struct.centroid*, %struct.centroid** %41, align 8
  %1955 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1956 = getelementptr inbounds %struct.qtree, %struct.qtree* %1955, i32 0, i32 0
  %1957 = load %struct.quad*, %struct.quad** %1956, align 8
  %1958 = getelementptr inbounds %struct.quad, %struct.quad* %1957, i32 0, i32 3
  store %struct.centroid* %1954, %struct.centroid** %1958, align 8
  br label %2101

1959:                                             ; preds = %1818
  %1960 = load float, float* %5, align 4
  %1961 = load float, float* %6, align 4
  %1962 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1963 = getelementptr inbounds %struct.qtree, %struct.qtree* %1962, i32 0, i32 0
  %1964 = load %struct.quad*, %struct.quad** %1963, align 8
  %1965 = call i32 @which_quad(float %1960, float %1961, %struct.quad* %1964)
  %1966 = icmp eq i32 %1965, 4
  br i1 %1966, label %1967, label %2100

1967:                                             ; preds = %1959
  %1968 = load float, float* %5, align 4
  %1969 = load float, float* %6, align 4
  %1970 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1971 = getelementptr inbounds %struct.qtree, %struct.qtree* %1970, i32 0, i32 4
  %1972 = load %struct.qtree*, %struct.qtree** %1971, align 8
  %1973 = load float, float* %8, align 4
  %1974 = call %struct.qtree* @insertPoint(float %1968, float %1969, %struct.qtree* %1972, float %1973)
  %1975 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1976 = getelementptr inbounds %struct.qtree, %struct.qtree* %1975, i32 0, i32 4
  store %struct.qtree* %1974, %struct.qtree** %1976, align 8
  %1977 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1978 = getelementptr inbounds %struct.qtree, %struct.qtree* %1977, i32 0, i32 1
  %1979 = load %struct.qtree*, %struct.qtree** %1978, align 8
  %1980 = icmp ne %struct.qtree* %1979, null
  br i1 %1980, label %1981, label %2027

1981:                                             ; preds = %1967
  %1982 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1983 = getelementptr inbounds %struct.qtree, %struct.qtree* %1982, i32 0, i32 1
  %1984 = load %struct.qtree*, %struct.qtree** %1983, align 8
  %1985 = getelementptr inbounds %struct.qtree, %struct.qtree* %1984, i32 0, i32 0
  %1986 = load %struct.quad*, %struct.quad** %1985, align 8
  %1987 = getelementptr inbounds %struct.quad, %struct.quad* %1986, i32 0, i32 3
  %1988 = load %struct.centroid*, %struct.centroid** %1987, align 8
  %1989 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1990 = getelementptr inbounds %struct.qtree, %struct.qtree* %1989, i32 0, i32 4
  %1991 = load %struct.qtree*, %struct.qtree** %1990, align 8
  %1992 = getelementptr inbounds %struct.qtree, %struct.qtree* %1991, i32 0, i32 0
  %1993 = load %struct.quad*, %struct.quad** %1992, align 8
  %1994 = getelementptr inbounds %struct.quad, %struct.quad* %1993, i32 0, i32 3
  %1995 = load %struct.centroid*, %struct.centroid** %1994, align 8
  %1996 = call %struct.centroid* @centroid_sum(%struct.centroid* %1988, %struct.centroid* %1995)
  store %struct.centroid* %1996, %struct.centroid** %42, align 8
  %1997 = load %struct.qtree*, %struct.qtree** %7, align 8
  %1998 = getelementptr inbounds %struct.qtree, %struct.qtree* %1997, i32 0, i32 2
  %1999 = load %struct.qtree*, %struct.qtree** %1998, align 8
  %2000 = icmp ne %struct.qtree* %1999, null
  br i1 %2000, label %2001, label %2011

2001:                                             ; preds = %1981
  %2002 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2003 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2004 = getelementptr inbounds %struct.qtree, %struct.qtree* %2003, i32 0, i32 2
  %2005 = load %struct.qtree*, %struct.qtree** %2004, align 8
  %2006 = getelementptr inbounds %struct.qtree, %struct.qtree* %2005, i32 0, i32 0
  %2007 = load %struct.quad*, %struct.quad** %2006, align 8
  %2008 = getelementptr inbounds %struct.quad, %struct.quad* %2007, i32 0, i32 3
  %2009 = load %struct.centroid*, %struct.centroid** %2008, align 8
  %2010 = call %struct.centroid* @centroid_sum(%struct.centroid* %2002, %struct.centroid* %2009)
  store %struct.centroid* %2010, %struct.centroid** %42, align 8
  br label %2011

2011:                                             ; preds = %2001, %1981
  %2012 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2013 = getelementptr inbounds %struct.qtree, %struct.qtree* %2012, i32 0, i32 3
  %2014 = load %struct.qtree*, %struct.qtree** %2013, align 8
  %2015 = icmp ne %struct.qtree* %2014, null
  br i1 %2015, label %2016, label %2026

2016:                                             ; preds = %2011
  %2017 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2018 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2019 = getelementptr inbounds %struct.qtree, %struct.qtree* %2018, i32 0, i32 3
  %2020 = load %struct.qtree*, %struct.qtree** %2019, align 8
  %2021 = getelementptr inbounds %struct.qtree, %struct.qtree* %2020, i32 0, i32 0
  %2022 = load %struct.quad*, %struct.quad** %2021, align 8
  %2023 = getelementptr inbounds %struct.quad, %struct.quad* %2022, i32 0, i32 3
  %2024 = load %struct.centroid*, %struct.centroid** %2023, align 8
  %2025 = call %struct.centroid* @centroid_sum(%struct.centroid* %2017, %struct.centroid* %2024)
  store %struct.centroid* %2025, %struct.centroid** %42, align 8
  br label %2026

2026:                                             ; preds = %2016, %2011
  br label %2094

2027:                                             ; preds = %1967
  %2028 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2029 = getelementptr inbounds %struct.qtree, %struct.qtree* %2028, i32 0, i32 2
  %2030 = load %struct.qtree*, %struct.qtree** %2029, align 8
  %2031 = icmp ne %struct.qtree* %2030, null
  br i1 %2031, label %2032, label %2063

2032:                                             ; preds = %2027
  %2033 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2034 = getelementptr inbounds %struct.qtree, %struct.qtree* %2033, i32 0, i32 2
  %2035 = load %struct.qtree*, %struct.qtree** %2034, align 8
  %2036 = getelementptr inbounds %struct.qtree, %struct.qtree* %2035, i32 0, i32 0
  %2037 = load %struct.quad*, %struct.quad** %2036, align 8
  %2038 = getelementptr inbounds %struct.quad, %struct.quad* %2037, i32 0, i32 3
  %2039 = load %struct.centroid*, %struct.centroid** %2038, align 8
  %2040 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2041 = getelementptr inbounds %struct.qtree, %struct.qtree* %2040, i32 0, i32 4
  %2042 = load %struct.qtree*, %struct.qtree** %2041, align 8
  %2043 = getelementptr inbounds %struct.qtree, %struct.qtree* %2042, i32 0, i32 0
  %2044 = load %struct.quad*, %struct.quad** %2043, align 8
  %2045 = getelementptr inbounds %struct.quad, %struct.quad* %2044, i32 0, i32 3
  %2046 = load %struct.centroid*, %struct.centroid** %2045, align 8
  %2047 = call %struct.centroid* @centroid_sum(%struct.centroid* %2039, %struct.centroid* %2046)
  store %struct.centroid* %2047, %struct.centroid** %42, align 8
  %2048 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2049 = getelementptr inbounds %struct.qtree, %struct.qtree* %2048, i32 0, i32 3
  %2050 = load %struct.qtree*, %struct.qtree** %2049, align 8
  %2051 = icmp ne %struct.qtree* %2050, null
  br i1 %2051, label %2052, label %2062

2052:                                             ; preds = %2032
  %2053 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2054 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2055 = getelementptr inbounds %struct.qtree, %struct.qtree* %2054, i32 0, i32 3
  %2056 = load %struct.qtree*, %struct.qtree** %2055, align 8
  %2057 = getelementptr inbounds %struct.qtree, %struct.qtree* %2056, i32 0, i32 0
  %2058 = load %struct.quad*, %struct.quad** %2057, align 8
  %2059 = getelementptr inbounds %struct.quad, %struct.quad* %2058, i32 0, i32 3
  %2060 = load %struct.centroid*, %struct.centroid** %2059, align 8
  %2061 = call %struct.centroid* @centroid_sum(%struct.centroid* %2053, %struct.centroid* %2060)
  store %struct.centroid* %2061, %struct.centroid** %42, align 8
  br label %2062

2062:                                             ; preds = %2052, %2032
  br label %2093

2063:                                             ; preds = %2027
  %2064 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2065 = getelementptr inbounds %struct.qtree, %struct.qtree* %2064, i32 0, i32 2
  %2066 = load %struct.qtree*, %struct.qtree** %2065, align 8
  %2067 = icmp ne %struct.qtree* %2066, null
  br i1 %2067, label %2068, label %2084

2068:                                             ; preds = %2063
  %2069 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2070 = getelementptr inbounds %struct.qtree, %struct.qtree* %2069, i32 0, i32 2
  %2071 = load %struct.qtree*, %struct.qtree** %2070, align 8
  %2072 = getelementptr inbounds %struct.qtree, %struct.qtree* %2071, i32 0, i32 0
  %2073 = load %struct.quad*, %struct.quad** %2072, align 8
  %2074 = getelementptr inbounds %struct.quad, %struct.quad* %2073, i32 0, i32 3
  %2075 = load %struct.centroid*, %struct.centroid** %2074, align 8
  %2076 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2077 = getelementptr inbounds %struct.qtree, %struct.qtree* %2076, i32 0, i32 4
  %2078 = load %struct.qtree*, %struct.qtree** %2077, align 8
  %2079 = getelementptr inbounds %struct.qtree, %struct.qtree* %2078, i32 0, i32 0
  %2080 = load %struct.quad*, %struct.quad** %2079, align 8
  %2081 = getelementptr inbounds %struct.quad, %struct.quad* %2080, i32 0, i32 3
  %2082 = load %struct.centroid*, %struct.centroid** %2081, align 8
  %2083 = call %struct.centroid* @centroid_sum(%struct.centroid* %2075, %struct.centroid* %2082)
  store %struct.centroid* %2083, %struct.centroid** %42, align 8
  br label %2092

2084:                                             ; preds = %2063
  %2085 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2086 = getelementptr inbounds %struct.qtree, %struct.qtree* %2085, i32 0, i32 4
  %2087 = load %struct.qtree*, %struct.qtree** %2086, align 8
  %2088 = getelementptr inbounds %struct.qtree, %struct.qtree* %2087, i32 0, i32 0
  %2089 = load %struct.quad*, %struct.quad** %2088, align 8
  %2090 = getelementptr inbounds %struct.quad, %struct.quad* %2089, i32 0, i32 3
  %2091 = load %struct.centroid*, %struct.centroid** %2090, align 8
  store %struct.centroid* %2091, %struct.centroid** %42, align 8
  br label %2092

2092:                                             ; preds = %2084, %2068
  br label %2093

2093:                                             ; preds = %2092, %2062
  br label %2094

2094:                                             ; preds = %2093, %2026
  %2095 = load %struct.centroid*, %struct.centroid** %42, align 8
  %2096 = load %struct.qtree*, %struct.qtree** %7, align 8
  %2097 = getelementptr inbounds %struct.qtree, %struct.qtree* %2096, i32 0, i32 0
  %2098 = load %struct.quad*, %struct.quad** %2097, align 8
  %2099 = getelementptr inbounds %struct.quad, %struct.quad* %2098, i32 0, i32 3
  store %struct.centroid* %2095, %struct.centroid** %2099, align 8
  br label %2100

2100:                                             ; preds = %2094, %1959
  br label %2101

2101:                                             ; preds = %2100, %1953
  br label %2102

2102:                                             ; preds = %2101, %1812
  br label %2103

2103:                                             ; preds = %2102, %1671
  br label %2104

2104:                                             ; preds = %2103, %1530
  br label %2105

2105:                                             ; preds = %2104, %1166
  br label %2106

2106:                                             ; preds = %2105, %805
  br label %2107

2107:                                             ; preds = %2106, %444
  br label %2108

2108:                                             ; preds = %2107, %76
  br label %2109

2109:                                             ; preds = %2108, %45
  %2110 = load %struct.qtree*, %struct.qtree** %7, align 8
  ret %struct.qtree* %2110
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
  ret i32 %7
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

; ASSERT EQ: i32 1 = call i32 @main(i32 0, i8** null)
