; ModuleID = 'incomplete_arrays.c'
source_filename = "incomplete_arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@SOME_INTS = external local_unnamed_addr global [0 x i32], align 4

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(read, argmem: none, inaccessiblemem: none) uwtable
define zeroext i1 @check_some_ints() local_unnamed_addr #0 {
  %1 = load i32, ptr @SOME_INTS, align 4, !tbaa !5
  %2 = icmp eq i32 %1, 2
  br i1 %2, label %3, label %12

3:                                                ; preds = %0
  %4 = load i32, ptr getelementptr (i8, ptr @SOME_INTS, i64 4), align 4, !tbaa !5
  %5 = icmp eq i32 %4, 0
  br i1 %5, label %6, label %12

6:                                                ; preds = %3
  %7 = load i32, ptr getelementptr (i8, ptr @SOME_INTS, i64 8), align 4, !tbaa !5
  %8 = icmp eq i32 %7, 1
  br i1 %8, label %9, label %12

9:                                                ; preds = %6
  %10 = load i32, ptr getelementptr (i8, ptr @SOME_INTS, i64 12), align 4, !tbaa !5
  %11 = icmp eq i32 %10, 8
  br label %12

12:                                               ; preds = %9, %6, %3, %0
  %13 = phi i1 [ false, %6 ], [ false, %3 ], [ false, %0 ], [ %11, %9 ]
  ret i1 %13
}

; Function Attrs: mustprogress nofree nounwind sspstrong willreturn memory(write, argmem: none, inaccessiblemem: readwrite) uwtable
define noalias noundef ptr @new_sized_array(i64 noundef %0) local_unnamed_addr #1 {
  %2 = shl i64 %0, 2
  %3 = add i64 %2, 8
  %4 = tail call noalias ptr @malloc(i64 noundef %3) #7
  store i64 %0, ptr %4, align 8, !tbaa !9
  ret ptr %4
}

; Function Attrs: mustprogress nofree nounwind willreturn allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite)
declare noalias noundef ptr @malloc(i64 noundef) local_unnamed_addr #2

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: read) uwtable
define i32 @sized_array_sum_last_n(ptr nocapture noundef readonly %0, i64 noundef %1) local_unnamed_addr #3 {
  %3 = load i64, ptr %0, align 8, !tbaa !9
  %4 = sub i64 %3, %1
  %5 = icmp ult i64 %4, %3
  br i1 %5, label %6, label %32

6:                                                ; preds = %2
  %7 = getelementptr inbounds i8, ptr %0, i64 8
  %8 = icmp ult i64 %1, 8
  br i1 %8, label %9, label %12

9:                                                ; preds = %28, %6
  %10 = phi i64 [ %4, %6 ], [ %14, %28 ]
  %11 = phi i32 [ 0, %6 ], [ %30, %28 ]
  br label %34

12:                                               ; preds = %6
  %13 = and i64 %1, -8
  %14 = add i64 %4, %13
  br label %15

15:                                               ; preds = %15, %12
  %16 = phi i64 [ 0, %12 ], [ %26, %15 ]
  %17 = phi <4 x i32> [ zeroinitializer, %12 ], [ %24, %15 ]
  %18 = phi <4 x i32> [ zeroinitializer, %12 ], [ %25, %15 ]
  %19 = add i64 %4, %16
  %20 = getelementptr [0 x i32], ptr %7, i64 0, i64 %19
  %21 = getelementptr i8, ptr %20, i64 16
  %22 = load <4 x i32>, ptr %20, align 4, !tbaa !5
  %23 = load <4 x i32>, ptr %21, align 4, !tbaa !5
  %24 = add <4 x i32> %22, %17
  %25 = add <4 x i32> %23, %18
  %26 = add nuw i64 %16, 8
  %27 = icmp eq i64 %26, %13
  br i1 %27, label %28, label %15, !llvm.loop !11

28:                                               ; preds = %15
  %29 = add <4 x i32> %25, %24
  %30 = tail call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> %29)
  %31 = icmp eq i64 %13, %1
  br i1 %31, label %32, label %9

32:                                               ; preds = %34, %28, %2
  %33 = phi i32 [ 0, %2 ], [ %30, %28 ], [ %39, %34 ]
  ret i32 %33

34:                                               ; preds = %9, %34
  %35 = phi i64 [ %40, %34 ], [ %10, %9 ]
  %36 = phi i32 [ %39, %34 ], [ %11, %9 ]
  %37 = getelementptr [0 x i32], ptr %7, i64 0, i64 %35
  %38 = load i32, ptr %37, align 4, !tbaa !5
  %39 = add i32 %38, %36
  %40 = add nuw i64 %35, 1
  %41 = icmp eq i64 %40, %3
  br i1 %41, label %32, label %34, !llvm.loop !15
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(none) uwtable
define noundef i32 @test_sized_array() local_unnamed_addr #4 {
  ret i32 30
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: write) uwtable
define void @entry2(i32 noundef %0, ptr nocapture noundef writeonly %1) local_unnamed_addr #5 {
  store i32 1, ptr %1, align 4, !tbaa !5
  %3 = getelementptr i8, ptr %1, i64 4
  store i32 1, ptr %3, align 4, !tbaa !5
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>) #6

attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(read, argmem: none, inaccessiblemem: none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #1 = { mustprogress nofree nounwind sspstrong willreturn memory(write, argmem: none, inaccessiblemem: readwrite) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #2 = { mustprogress nofree nounwind willreturn allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite) "alloc-family"="malloc" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #3 = { nofree norecurse nosync nounwind sspstrong memory(argmem: read) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #4 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #5 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #6 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #7 = { nounwind allocsize(0) }

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
!9 = !{!10, !10, i64 0}
!10 = !{!"long", !7, i64 0}
!11 = distinct !{!11, !12, !13, !14}
!12 = !{!"llvm.loop.mustprogress"}
!13 = !{!"llvm.loop.isvectorized", i32 1}
!14 = !{!"llvm.loop.unroll.runtime.disable"}
!15 = distinct !{!15, !12, !14, !13}
