; ModuleID = 'incomplete_arrays.c'
source_filename = "incomplete_arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.sized_array = type { i64, [0 x i32] }

@SOME_INTS = external local_unnamed_addr global [0 x i32], align 4

; Function Attrs: mustprogress nofree norecurse nosync nounwind readonly sspstrong uwtable willreturn
define zeroext i1 @check_some_ints() local_unnamed_addr #0 {
  %1 = load i32, i32* getelementptr inbounds ([0 x i32], [0 x i32]* @SOME_INTS, i64 0, i64 0), align 4, !tbaa !5
  %2 = icmp eq i32 %1, 2
  br i1 %2, label %3, label %12

3:                                                ; preds = %0
  %4 = load i32, i32* getelementptr inbounds ([0 x i32], [0 x i32]* @SOME_INTS, i64 0, i64 1), align 4, !tbaa !5
  %5 = icmp eq i32 %4, 0
  br i1 %5, label %6, label %12

6:                                                ; preds = %3
  %7 = load i32, i32* getelementptr inbounds ([0 x i32], [0 x i32]* @SOME_INTS, i64 0, i64 2), align 4, !tbaa !5
  %8 = icmp eq i32 %7, 1
  br i1 %8, label %9, label %12

9:                                                ; preds = %6
  %10 = load i32, i32* getelementptr inbounds ([0 x i32], [0 x i32]* @SOME_INTS, i64 0, i64 3), align 4, !tbaa !5
  %11 = icmp eq i32 %10, 8
  br label %12

12:                                               ; preds = %9, %6, %3, %0
  %13 = phi i1 [ false, %6 ], [ false, %3 ], [ false, %0 ], [ %11, %9 ]
  ret i1 %13
}

; Function Attrs: mustprogress nofree nounwind sspstrong uwtable willreturn
define noalias %struct.sized_array* @new_sized_array(i64 noundef %0) local_unnamed_addr #1 {
  %2 = shl i64 %0, 2
  %3 = add i64 %2, 8
  %4 = tail call noalias i8* @malloc(i64 noundef %3) #7
  %5 = bitcast i8* %4 to %struct.sized_array*
  %6 = getelementptr inbounds %struct.sized_array, %struct.sized_array* %5, i64 0, i32 0
  store i64 %0, i64* %6, align 8, !tbaa !9
  ret %struct.sized_array* %5
}

; Function Attrs: inaccessiblememonly mustprogress nofree nounwind willreturn
declare noalias noundef i8* @malloc(i64 noundef) local_unnamed_addr #2

; Function Attrs: nofree norecurse nosync nounwind readonly sspstrong uwtable
define i32 @sized_array_sum_last_n(%struct.sized_array* nocapture noundef readonly %0, i64 noundef %1) local_unnamed_addr #3 {
  %3 = getelementptr inbounds %struct.sized_array, %struct.sized_array* %0, i64 0, i32 0
  %4 = load i64, i64* %3, align 8, !tbaa !9
  %5 = sub i64 %4, %1
  %6 = icmp ult i64 %5, %4
  br i1 %6, label %7, label %99

7:                                                ; preds = %2
  %8 = icmp ult i64 %1, 8
  br i1 %8, label %96, label %9

9:                                                ; preds = %7
  %10 = and i64 %1, -8
  %11 = add i64 %5, %10
  %12 = add i64 %10, -8
  %13 = lshr exact i64 %12, 3
  %14 = add nuw nsw i64 %13, 1
  %15 = and i64 %14, 3
  %16 = icmp ult i64 %12, 24
  br i1 %16, label %66, label %17

17:                                               ; preds = %9
  %18 = and i64 %14, 4611686018427387900
  br label %19

19:                                               ; preds = %19, %17
  %20 = phi i64 [ 0, %17 ], [ %63, %19 ]
  %21 = phi <4 x i32> [ zeroinitializer, %17 ], [ %61, %19 ]
  %22 = phi <4 x i32> [ zeroinitializer, %17 ], [ %62, %19 ]
  %23 = phi i64 [ 0, %17 ], [ %64, %19 ]
  %24 = add i64 %5, %20
  %25 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %24
  %26 = bitcast i32* %25 to <4 x i32>*
  %27 = load <4 x i32>, <4 x i32>* %26, align 4, !tbaa !5
  %28 = getelementptr i32, i32* %25, i64 4
  %29 = bitcast i32* %28 to <4 x i32>*
  %30 = load <4 x i32>, <4 x i32>* %29, align 4, !tbaa !5
  %31 = add <4 x i32> %27, %21
  %32 = add <4 x i32> %30, %22
  %33 = or i64 %20, 8
  %34 = add i64 %5, %33
  %35 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %34
  %36 = bitcast i32* %35 to <4 x i32>*
  %37 = load <4 x i32>, <4 x i32>* %36, align 4, !tbaa !5
  %38 = getelementptr i32, i32* %35, i64 4
  %39 = bitcast i32* %38 to <4 x i32>*
  %40 = load <4 x i32>, <4 x i32>* %39, align 4, !tbaa !5
  %41 = add <4 x i32> %37, %31
  %42 = add <4 x i32> %40, %32
  %43 = or i64 %20, 16
  %44 = add i64 %5, %43
  %45 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %44
  %46 = bitcast i32* %45 to <4 x i32>*
  %47 = load <4 x i32>, <4 x i32>* %46, align 4, !tbaa !5
  %48 = getelementptr i32, i32* %45, i64 4
  %49 = bitcast i32* %48 to <4 x i32>*
  %50 = load <4 x i32>, <4 x i32>* %49, align 4, !tbaa !5
  %51 = add <4 x i32> %47, %41
  %52 = add <4 x i32> %50, %42
  %53 = or i64 %20, 24
  %54 = add i64 %5, %53
  %55 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %54
  %56 = bitcast i32* %55 to <4 x i32>*
  %57 = load <4 x i32>, <4 x i32>* %56, align 4, !tbaa !5
  %58 = getelementptr i32, i32* %55, i64 4
  %59 = bitcast i32* %58 to <4 x i32>*
  %60 = load <4 x i32>, <4 x i32>* %59, align 4, !tbaa !5
  %61 = add <4 x i32> %57, %51
  %62 = add <4 x i32> %60, %52
  %63 = add nuw i64 %20, 32
  %64 = add i64 %23, 4
  %65 = icmp eq i64 %64, %18
  br i1 %65, label %66, label %19, !llvm.loop !11

66:                                               ; preds = %19, %9
  %67 = phi <4 x i32> [ undef, %9 ], [ %61, %19 ]
  %68 = phi <4 x i32> [ undef, %9 ], [ %62, %19 ]
  %69 = phi i64 [ 0, %9 ], [ %63, %19 ]
  %70 = phi <4 x i32> [ zeroinitializer, %9 ], [ %61, %19 ]
  %71 = phi <4 x i32> [ zeroinitializer, %9 ], [ %62, %19 ]
  %72 = icmp eq i64 %15, 0
  br i1 %72, label %90, label %73

73:                                               ; preds = %66, %73
  %74 = phi i64 [ %87, %73 ], [ %69, %66 ]
  %75 = phi <4 x i32> [ %85, %73 ], [ %70, %66 ]
  %76 = phi <4 x i32> [ %86, %73 ], [ %71, %66 ]
  %77 = phi i64 [ %88, %73 ], [ 0, %66 ]
  %78 = add i64 %5, %74
  %79 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %78
  %80 = bitcast i32* %79 to <4 x i32>*
  %81 = load <4 x i32>, <4 x i32>* %80, align 4, !tbaa !5
  %82 = getelementptr i32, i32* %79, i64 4
  %83 = bitcast i32* %82 to <4 x i32>*
  %84 = load <4 x i32>, <4 x i32>* %83, align 4, !tbaa !5
  %85 = add <4 x i32> %81, %75
  %86 = add <4 x i32> %84, %76
  %87 = add nuw i64 %74, 8
  %88 = add i64 %77, 1
  %89 = icmp eq i64 %88, %15
  br i1 %89, label %90, label %73, !llvm.loop !14

90:                                               ; preds = %73, %66
  %91 = phi <4 x i32> [ %67, %66 ], [ %85, %73 ]
  %92 = phi <4 x i32> [ %68, %66 ], [ %86, %73 ]
  %93 = add <4 x i32> %92, %91
  %94 = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %93)
  %95 = icmp eq i64 %10, %1
  br i1 %95, label %99, label %96

96:                                               ; preds = %7, %90
  %97 = phi i64 [ %5, %7 ], [ %11, %90 ]
  %98 = phi i32 [ 0, %7 ], [ %94, %90 ]
  br label %101

99:                                               ; preds = %101, %90, %2
  %100 = phi i32 [ 0, %2 ], [ %94, %90 ], [ %106, %101 ]
  ret i32 %100

101:                                              ; preds = %96, %101
  %102 = phi i64 [ %107, %101 ], [ %97, %96 ]
  %103 = phi i32 [ %106, %101 ], [ %98, %96 ]
  %104 = getelementptr %struct.sized_array, %struct.sized_array* %0, i64 0, i32 1, i64 %102
  %105 = load i32, i32* %104, align 4, !tbaa !5
  %106 = add i32 %105, %103
  %107 = add nuw i64 %102, 1
  %108 = icmp eq i64 %107, %4
  br i1 %108, label %99, label %101, !llvm.loop !16
}

; Function Attrs: nounwind sspstrong uwtable
define i32 @test_sized_array() local_unnamed_addr #4 {
  ret i32 30
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong uwtable willreturn writeonly
define void @entry2(i32 noundef %0, i32* nocapture noundef writeonly %1) local_unnamed_addr #5 {
  store i32 1, i32* %1, align 4, !tbaa !5
  %3 = getelementptr i32, i32* %1, i64 1
  store i32 1, i32* %3, align 4, !tbaa !5
  ret void
}

; Function Attrs: nofree nosync nounwind readnone willreturn
declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>) #6

attributes #0 = { mustprogress nofree norecurse nosync nounwind readonly sspstrong uwtable willreturn "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress nofree nounwind sspstrong uwtable willreturn "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { inaccessiblememonly mustprogress nofree nounwind willreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nofree norecurse nosync nounwind readonly sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { mustprogress nofree norecurse nosync nounwind sspstrong uwtable willreturn writeonly "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #6 = { nofree nosync nounwind readnone willreturn }
attributes #7 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"clang version 14.0.6"}
!5 = !{!6, !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
!9 = !{!10, !10, i64 0}
!10 = !{!"long", !7, i64 0}
!11 = distinct !{!11, !12, !13}
!12 = !{!"llvm.loop.mustprogress"}
!13 = !{!"llvm.loop.isvectorized", i32 1}
!14 = distinct !{!14, !15}
!15 = !{!"llvm.loop.unroll.disable"}
!16 = distinct !{!16, !12, !17, !13}
!17 = !{!"llvm.loop.unroll.runtime.disable"}
