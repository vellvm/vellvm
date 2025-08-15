; ModuleID = 'arrays.c'
source_filename = "arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong uwtable willreturn writeonly
define void @entry(i32 noundef %0, i32* noundef writeonly %1) local_unnamed_addr #0 {
  %3 = bitcast i32* %1 to <4 x i32>*
  store <4 x i32> <i32 97, i32 98, i32 99, i32 0>, <4 x i32>* %3, align 4, !tbaa !5
  %4 = getelementptr i32, i32* %1, i64 4
  %5 = bitcast i32* %4 to <4 x i32>*
  store <4 x i32> <i32 100, i32 101, i32 102, i32 1>, <4 x i32>* %5, align 4, !tbaa !5
  %6 = getelementptr i32, i32* %1, i64 8
  %7 = bitcast i32* %6 to <4 x i32>*
  store <4 x i32> <i32 0, i32 97, i32 98, i32 99>, <4 x i32>* %7, align 4, !tbaa !5
  %8 = getelementptr i32, i32* %1, i64 12
  %9 = bitcast i32* %8 to <4 x i32>*
  store <4 x i32> <i32 0, i32 97, i32 98, i32 99>, <4 x i32>* %9, align 4, !tbaa !5
  %10 = getelementptr i32, i32* %1, i64 16
  %11 = bitcast i32* %10 to <4 x i32>*
  store <4 x i32> <i32 100, i32 97, i32 98, i32 99>, <4 x i32>* %11, align 4, !tbaa !5
  %12 = getelementptr i32, i32* %1, i64 20
  store i32 97, i32* %12, align 4, !tbaa !5
  %13 = getelementptr i32, i32* %1, i64 21
  store i32 98, i32* %13, align 4, !tbaa !5
  %14 = getelementptr i32, i32* %1, i64 22
  store i32 99, i32* %14, align 4, !tbaa !5
  %15 = getelementptr i32, i32* %1, i64 23
  %16 = getelementptr i32, i32* %1, i64 27
  %17 = bitcast i32* %15 to i8*
  call void @llvm.memset.p0i8.i64(i8* noundef nonnull align 4 dereferenceable(16) %17, i8 0, i64 16, i1 false)
  %18 = bitcast i32* %16 to <4 x i32>*
  store <4 x i32> <i32 120, i32 0, i32 120, i32 0>, <4 x i32>* %18, align 4, !tbaa !5
  %19 = getelementptr i32, i32* %1, i64 31
  %20 = bitcast i32* %19 to <4 x i32>*
  store <4 x i32> <i32 0, i32 120, i32 109, i32 121>, <4 x i32>* %20, align 4, !tbaa !5
  %21 = getelementptr i32, i32* %1, i64 35
  %22 = bitcast i32* %21 to <4 x i32>*
  store <4 x i32> <i32 115, i32 116, i32 114, i32 105>, <4 x i32>* %22, align 4, !tbaa !5
  %23 = getelementptr i32, i32* %1, i64 39
  %24 = bitcast i32* %23 to <4 x i32>*
  store <4 x i32> <i32 110, i32 103, i32 109, i32 121>, <4 x i32>* %24, align 4, !tbaa !5
  %25 = getelementptr i32, i32* %1, i64 43
  %26 = bitcast i32* %25 to <4 x i32>*
  store <4 x i32> <i32 115, i32 116, i32 114, i32 105>, <4 x i32>* %26, align 4, !tbaa !5
  %27 = getelementptr i32, i32* %1, i64 47
  store i32 110, i32* %27, align 4, !tbaa !5
  %28 = getelementptr i32, i32* %1, i64 48
  store i32 103, i32* %28, align 4, !tbaa !5
  ret void
}

; Function Attrs: argmemonly mustprogress nofree nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong uwtable willreturn writeonly "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { argmemonly mustprogress nofree nounwind willreturn writeonly }

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
