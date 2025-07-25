; ModuleID = 'variable_arrays.c'
source_filename = "variable_arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: write) uwtable
define void @use_arrays(i32 noundef %0, i32 noundef %1, ptr nocapture noundef writeonly %2) local_unnamed_addr #0 {
  %4 = mul i32 %0, %0
  %5 = zext i32 %4 to i64
  %6 = zext i32 %1 to i64
  %7 = icmp sgt i32 %4, 0
  %8 = icmp sgt i32 %1, 0
  %9 = mul nuw i64 %5, %6
  br i1 %7, label %10, label %81

10:                                               ; preds = %3
  %11 = icmp ult i32 %1, 8
  %12 = and i64 %6, 2147483640
  %13 = trunc nuw nsw i64 %12 to i32
  %14 = icmp eq i64 %12, %6
  br label %15

15:                                               ; preds = %10, %82
  %16 = phi i64 [ %84, %82 ], [ 0, %10 ]
  %17 = phi i32 [ %83, %82 ], [ 1, %10 ]
  br i1 %8, label %18, label %82

18:                                               ; preds = %15
  %19 = mul nuw nsw i64 %16, %6
  %20 = getelementptr i32, ptr %2, i64 %19
  br i1 %11, label %21, label %24

21:                                               ; preds = %38, %18
  %22 = phi i64 [ 0, %18 ], [ %12, %38 ]
  %23 = phi i32 [ %17, %18 ], [ %25, %38 ]
  br label %86

24:                                               ; preds = %18
  %25 = add i32 %17, %13
  %26 = insertelement <4 x i32> poison, i32 %17, i64 0
  %27 = shufflevector <4 x i32> %26, <4 x i32> poison, <4 x i32> zeroinitializer
  %28 = add <4 x i32> %27, <i32 0, i32 1, i32 2, i32 3>
  br label %29

29:                                               ; preds = %29, %24
  %30 = phi i64 [ 0, %24 ], [ %35, %29 ]
  %31 = phi <4 x i32> [ %28, %24 ], [ %36, %29 ]
  %32 = add <4 x i32> %31, <i32 4, i32 4, i32 4, i32 4>
  %33 = getelementptr i32, ptr %20, i64 %30
  %34 = getelementptr i8, ptr %33, i64 16
  store <4 x i32> %31, ptr %33, align 4, !tbaa !5
  store <4 x i32> %32, ptr %34, align 4, !tbaa !5
  %35 = add nuw i64 %30, 8
  %36 = add <4 x i32> %31, <i32 8, i32 8, i32 8, i32 8>
  %37 = icmp eq i64 %35, %12
  br i1 %37, label %38, label %29, !llvm.loop !9

38:                                               ; preds = %29
  br i1 %14, label %82, label %21

39:                                               ; preds = %82
  br i1 %7, label %40, label %81

40:                                               ; preds = %39
  %41 = getelementptr i32, ptr %2, i64 %9
  %42 = icmp ult i32 %1, 8
  %43 = and i64 %6, 2147483640
  %44 = trunc nuw nsw i64 %43 to i32
  %45 = icmp eq i64 %43, %6
  br label %46

46:                                               ; preds = %77, %40
  %47 = phi i64 [ 0, %40 ], [ %79, %77 ]
  %48 = phi i32 [ %83, %40 ], [ %78, %77 ]
  br i1 %8, label %49, label %77

49:                                               ; preds = %46
  %50 = mul nuw nsw i64 %47, %6
  %51 = getelementptr i32, ptr %41, i64 %50
  br i1 %42, label %67, label %52

52:                                               ; preds = %49
  %53 = add i32 %48, %44
  %54 = insertelement <4 x i32> poison, i32 %48, i64 0
  %55 = shufflevector <4 x i32> %54, <4 x i32> poison, <4 x i32> zeroinitializer
  %56 = add <4 x i32> %55, <i32 0, i32 1, i32 2, i32 3>
  br label %57

57:                                               ; preds = %57, %52
  %58 = phi i64 [ 0, %52 ], [ %63, %57 ]
  %59 = phi <4 x i32> [ %56, %52 ], [ %64, %57 ]
  %60 = add <4 x i32> %59, <i32 4, i32 4, i32 4, i32 4>
  %61 = getelementptr i32, ptr %51, i64 %58
  %62 = getelementptr i8, ptr %61, i64 16
  store <4 x i32> %59, ptr %61, align 4, !tbaa !5
  store <4 x i32> %60, ptr %62, align 4, !tbaa !5
  %63 = add nuw i64 %58, 8
  %64 = add <4 x i32> %59, <i32 8, i32 8, i32 8, i32 8>
  %65 = icmp eq i64 %63, %43
  br i1 %65, label %66, label %57, !llvm.loop !13

66:                                               ; preds = %57
  br i1 %45, label %77, label %67

67:                                               ; preds = %66, %49
  %68 = phi i64 [ 0, %49 ], [ %43, %66 ]
  %69 = phi i32 [ %48, %49 ], [ %53, %66 ]
  br label %70

70:                                               ; preds = %67, %70
  %71 = phi i64 [ %75, %70 ], [ %68, %67 ]
  %72 = phi i32 [ %73, %70 ], [ %69, %67 ]
  %73 = add i32 %72, 1
  %74 = getelementptr i32, ptr %51, i64 %71
  store i32 %72, ptr %74, align 4, !tbaa !5
  %75 = add nuw nsw i64 %71, 1
  %76 = icmp eq i64 %75, %6
  br i1 %76, label %77, label %70, !llvm.loop !14

77:                                               ; preds = %70, %66, %46
  %78 = phi i32 [ %48, %46 ], [ %53, %66 ], [ %73, %70 ]
  %79 = add nuw nsw i64 %47, 1
  %80 = icmp eq i64 %79, %5
  br i1 %80, label %81, label %46, !llvm.loop !15

81:                                               ; preds = %77, %3, %39
  ret void

82:                                               ; preds = %86, %38, %15
  %83 = phi i32 [ %17, %15 ], [ %25, %38 ], [ %89, %86 ]
  %84 = add nuw nsw i64 %16, 1
  %85 = icmp eq i64 %84, %5
  br i1 %85, label %39, label %15, !llvm.loop !15

86:                                               ; preds = %21, %86
  %87 = phi i64 [ %91, %86 ], [ %22, %21 ]
  %88 = phi i32 [ %89, %86 ], [ %23, %21 ]
  %89 = add i32 %88, 1
  %90 = getelementptr i32, ptr %20, i64 %87
  store i32 %88, ptr %90, align 4, !tbaa !5
  %91 = add nuw nsw i64 %87, 1
  %92 = icmp eq i64 %91, %6
  br i1 %92, label %82, label %86, !llvm.loop !16
}

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: write) uwtable
define void @use_arrays2(i32 noundef %0, i32 noundef %1, ptr nocapture noundef writeonly %2) local_unnamed_addr #0 {
  %4 = mul i32 %0, %0
  %5 = zext i32 %4 to i64
  %6 = zext i32 %1 to i64
  %7 = icmp sgt i32 %4, 0
  %8 = icmp sgt i32 %1, 0
  %9 = mul nuw i64 %5, %6
  br i1 %7, label %10, label %81

10:                                               ; preds = %3
  %11 = icmp ult i32 %1, 8
  %12 = and i64 %6, 2147483640
  %13 = trunc nuw nsw i64 %12 to i32
  %14 = icmp eq i64 %12, %6
  br label %15

15:                                               ; preds = %10, %82
  %16 = phi i64 [ %84, %82 ], [ 0, %10 ]
  %17 = phi i32 [ %83, %82 ], [ 1, %10 ]
  br i1 %8, label %18, label %82

18:                                               ; preds = %15
  %19 = mul nuw nsw i64 %16, %6
  %20 = getelementptr i32, ptr %2, i64 %19
  br i1 %11, label %21, label %24

21:                                               ; preds = %38, %18
  %22 = phi i64 [ 0, %18 ], [ %12, %38 ]
  %23 = phi i32 [ %17, %18 ], [ %25, %38 ]
  br label %86

24:                                               ; preds = %18
  %25 = add i32 %17, %13
  %26 = insertelement <4 x i32> poison, i32 %17, i64 0
  %27 = shufflevector <4 x i32> %26, <4 x i32> poison, <4 x i32> zeroinitializer
  %28 = add <4 x i32> %27, <i32 0, i32 1, i32 2, i32 3>
  br label %29

29:                                               ; preds = %29, %24
  %30 = phi i64 [ 0, %24 ], [ %35, %29 ]
  %31 = phi <4 x i32> [ %28, %24 ], [ %36, %29 ]
  %32 = add <4 x i32> %31, <i32 4, i32 4, i32 4, i32 4>
  %33 = getelementptr i32, ptr %20, i64 %30
  %34 = getelementptr i8, ptr %33, i64 16
  store <4 x i32> %31, ptr %33, align 4, !tbaa !5
  store <4 x i32> %32, ptr %34, align 4, !tbaa !5
  %35 = add nuw i64 %30, 8
  %36 = add <4 x i32> %31, <i32 8, i32 8, i32 8, i32 8>
  %37 = icmp eq i64 %35, %12
  br i1 %37, label %38, label %29, !llvm.loop !17

38:                                               ; preds = %29
  br i1 %14, label %82, label %21

39:                                               ; preds = %82
  br i1 %7, label %40, label %81

40:                                               ; preds = %39
  %41 = getelementptr i32, ptr %2, i64 %9
  %42 = icmp ult i32 %1, 8
  %43 = and i64 %6, 2147483640
  %44 = trunc nuw nsw i64 %43 to i32
  %45 = icmp eq i64 %43, %6
  br label %46

46:                                               ; preds = %77, %40
  %47 = phi i64 [ 0, %40 ], [ %79, %77 ]
  %48 = phi i32 [ %83, %40 ], [ %78, %77 ]
  br i1 %8, label %49, label %77

49:                                               ; preds = %46
  %50 = mul nuw nsw i64 %47, %6
  %51 = getelementptr i32, ptr %41, i64 %50
  br i1 %42, label %67, label %52

52:                                               ; preds = %49
  %53 = add i32 %48, %44
  %54 = insertelement <4 x i32> poison, i32 %48, i64 0
  %55 = shufflevector <4 x i32> %54, <4 x i32> poison, <4 x i32> zeroinitializer
  %56 = add <4 x i32> %55, <i32 0, i32 1, i32 2, i32 3>
  br label %57

57:                                               ; preds = %57, %52
  %58 = phi i64 [ 0, %52 ], [ %63, %57 ]
  %59 = phi <4 x i32> [ %56, %52 ], [ %64, %57 ]
  %60 = add <4 x i32> %59, <i32 4, i32 4, i32 4, i32 4>
  %61 = getelementptr i32, ptr %51, i64 %58
  %62 = getelementptr i8, ptr %61, i64 16
  store <4 x i32> %59, ptr %61, align 4, !tbaa !5
  store <4 x i32> %60, ptr %62, align 4, !tbaa !5
  %63 = add nuw i64 %58, 8
  %64 = add <4 x i32> %59, <i32 8, i32 8, i32 8, i32 8>
  %65 = icmp eq i64 %63, %43
  br i1 %65, label %66, label %57, !llvm.loop !18

66:                                               ; preds = %57
  br i1 %45, label %77, label %67

67:                                               ; preds = %66, %49
  %68 = phi i64 [ 0, %49 ], [ %43, %66 ]
  %69 = phi i32 [ %48, %49 ], [ %53, %66 ]
  br label %70

70:                                               ; preds = %67, %70
  %71 = phi i64 [ %75, %70 ], [ %68, %67 ]
  %72 = phi i32 [ %73, %70 ], [ %69, %67 ]
  %73 = add i32 %72, 1
  %74 = getelementptr i32, ptr %51, i64 %71
  store i32 %72, ptr %74, align 4, !tbaa !5
  %75 = add nuw nsw i64 %71, 1
  %76 = icmp eq i64 %75, %6
  br i1 %76, label %77, label %70, !llvm.loop !19

77:                                               ; preds = %70, %66, %46
  %78 = phi i32 [ %48, %46 ], [ %53, %66 ], [ %73, %70 ]
  %79 = add nuw nsw i64 %47, 1
  %80 = icmp eq i64 %79, %5
  br i1 %80, label %81, label %46, !llvm.loop !20

81:                                               ; preds = %77, %3, %39
  ret void

82:                                               ; preds = %86, %38, %15
  %83 = phi i32 [ %17, %15 ], [ %25, %38 ], [ %89, %86 ]
  %84 = add nuw nsw i64 %16, 1
  %85 = icmp eq i64 %84, %5
  br i1 %85, label %39, label %15, !llvm.loop !20

86:                                               ; preds = %21, %86
  %87 = phi i64 [ %91, %86 ], [ %22, %21 ]
  %88 = phi i32 [ %89, %86 ], [ %23, %21 ]
  %89 = add i32 %88, 1
  %90 = getelementptr i32, ptr %20, i64 %87
  store i32 %88, ptr %90, align 4, !tbaa !5
  %91 = add nuw nsw i64 %87, 1
  %92 = icmp eq i64 %91, %6
  br i1 %92, label %82, label %86, !llvm.loop !21
}

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: write) uwtable
define void @variable_arrays(ptr nocapture noundef writeonly %0) local_unnamed_addr #0 {
  %2 = getelementptr i8, ptr %0, i64 64
  %3 = getelementptr i8, ptr %0, i64 48
  %4 = getelementptr i8, ptr %0, i64 32
  %5 = getelementptr i8, ptr %0, i64 16
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %0, align 4, !tbaa !5
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, ptr %5, align 4, !tbaa !5
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, ptr %4, align 4, !tbaa !5
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, ptr %3, align 4, !tbaa !5
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, ptr %2, align 4, !tbaa !5
  %6 = getelementptr i8, ptr %0, i64 80
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, ptr %6, align 4, !tbaa !5
  %7 = getelementptr i8, ptr %0, i64 96
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, ptr %7, align 4, !tbaa !5
  %8 = getelementptr i8, ptr %0, i64 112
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, ptr %8, align 4, !tbaa !5
  %9 = getelementptr i8, ptr %0, i64 128
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, ptr %9, align 4, !tbaa !5
  %10 = getelementptr i8, ptr %0, i64 144
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, ptr %10, align 4, !tbaa !5
  %11 = getelementptr i8, ptr %0, i64 160
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %11, align 4, !tbaa !5
  %12 = getelementptr i8, ptr %0, i64 176
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, ptr %12, align 4, !tbaa !5
  %13 = getelementptr i8, ptr %0, i64 192
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, ptr %13, align 4, !tbaa !5
  %14 = getelementptr i8, ptr %0, i64 208
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, ptr %14, align 4, !tbaa !5
  %15 = getelementptr i8, ptr %0, i64 224
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, ptr %15, align 4, !tbaa !5
  %16 = getelementptr i8, ptr %0, i64 240
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, ptr %16, align 4, !tbaa !5
  %17 = getelementptr i8, ptr %0, i64 256
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, ptr %17, align 4, !tbaa !5
  %18 = getelementptr i8, ptr %0, i64 272
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, ptr %18, align 4, !tbaa !5
  %19 = getelementptr i8, ptr %0, i64 288
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, ptr %19, align 4, !tbaa !5
  %20 = getelementptr i8, ptr %0, i64 304
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, ptr %20, align 4, !tbaa !5
  %21 = getelementptr i8, ptr %0, i64 320
  store <4 x i32> <i32 0, i32 3, i32 6, i32 9>, ptr %21, align 4, !tbaa !5
  %22 = getelementptr i8, ptr %0, i64 336
  store <4 x i32> <i32 12, i32 15, i32 18, i32 21>, ptr %22, align 4, !tbaa !5
  ret void
}

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: write) uwtable
define void @alloca_arrays(ptr nocapture noundef writeonly %0) local_unnamed_addr #0 {
  %2 = getelementptr i8, ptr %0, i64 64
  %3 = getelementptr i8, ptr %0, i64 48
  %4 = getelementptr i8, ptr %0, i64 32
  %5 = getelementptr i8, ptr %0, i64 16
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %0, align 4, !tbaa !5
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, ptr %5, align 4, !tbaa !5
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, ptr %4, align 4, !tbaa !5
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, ptr %3, align 4, !tbaa !5
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, ptr %2, align 4, !tbaa !5
  %6 = getelementptr i8, ptr %0, i64 80
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, ptr %6, align 4, !tbaa !5
  %7 = getelementptr i8, ptr %0, i64 96
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, ptr %7, align 4, !tbaa !5
  %8 = getelementptr i8, ptr %0, i64 112
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, ptr %8, align 4, !tbaa !5
  %9 = getelementptr i8, ptr %0, i64 128
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, ptr %9, align 4, !tbaa !5
  %10 = getelementptr i8, ptr %0, i64 144
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, ptr %10, align 4, !tbaa !5
  %11 = getelementptr i8, ptr %0, i64 160
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, ptr %11, align 4, !tbaa !5
  %12 = getelementptr i8, ptr %0, i64 176
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, ptr %12, align 4, !tbaa !5
  %13 = getelementptr i8, ptr %0, i64 192
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, ptr %13, align 4, !tbaa !5
  %14 = getelementptr i8, ptr %0, i64 208
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, ptr %14, align 4, !tbaa !5
  %15 = getelementptr i8, ptr %0, i64 224
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, ptr %15, align 4, !tbaa !5
  %16 = getelementptr i8, ptr %0, i64 240
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, ptr %16, align 4, !tbaa !5
  %17 = getelementptr i8, ptr %0, i64 256
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, ptr %17, align 4, !tbaa !5
  %18 = getelementptr i8, ptr %0, i64 272
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, ptr %18, align 4, !tbaa !5
  %19 = getelementptr i8, ptr %0, i64 288
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, ptr %19, align 4, !tbaa !5
  %20 = getelementptr i8, ptr %0, i64 304
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, ptr %20, align 4, !tbaa !5
  %21 = getelementptr i8, ptr %0, i64 320
  store <4 x i32> <i32 0, i32 3, i32 6, i32 9>, ptr %21, align 4, !tbaa !5
  %22 = getelementptr i8, ptr %0, i64 336
  store <4 x i32> <i32 12, i32 15, i32 18, i32 21>, ptr %22, align 4, !tbaa !5
  ret void
}

attributes #0 = { nofree norecurse nosync nounwind sspstrong memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 4, !"probe-stack", !"inline-asm"}
!2 = !{i32 8, !"PIC Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"clang version 19.1.7"}
!5 = !{!6, !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
!9 = distinct !{!9, !10, !11, !12}
!10 = !{!"llvm.loop.mustprogress"}
!11 = !{!"llvm.loop.isvectorized", i32 1}
!12 = !{!"llvm.loop.unroll.runtime.disable"}
!13 = distinct !{!13, !10, !11, !12}
!14 = distinct !{!14, !10, !12, !11}
!15 = distinct !{!15, !10}
!16 = distinct !{!16, !10, !12, !11}
!17 = distinct !{!17, !10, !11, !12}
!18 = distinct !{!18, !10, !11, !12}
!19 = distinct !{!19, !10, !12, !11}
!20 = distinct !{!20, !10}
!21 = distinct !{!21, !10, !12, !11}
