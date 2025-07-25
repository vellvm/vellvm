; ModuleID = 'arrays.c'
source_filename = "arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: write) uwtable
define void @entry(i32 noundef %0, ptr nocapture noundef writeonly %1) local_unnamed_addr #0 {
  store <4 x i32> <i32 97, i32 98, i32 99, i32 0>, ptr %1, align 4, !tbaa !5
  %3 = getelementptr i8, ptr %1, i64 16
  store <4 x i32> <i32 100, i32 101, i32 102, i32 1>, ptr %3, align 4, !tbaa !5
  %4 = getelementptr i8, ptr %1, i64 32
  store <4 x i32> <i32 0, i32 97, i32 98, i32 99>, ptr %4, align 4, !tbaa !5
  %5 = getelementptr i8, ptr %1, i64 48
  store <4 x i32> <i32 0, i32 97, i32 98, i32 99>, ptr %5, align 4, !tbaa !5
  %6 = getelementptr i8, ptr %1, i64 64
  store <4 x i32> <i32 100, i32 97, i32 98, i32 99>, ptr %6, align 4, !tbaa !5
  %7 = getelementptr i8, ptr %1, i64 80
  store i32 97, ptr %7, align 4, !tbaa !5
  %8 = getelementptr i8, ptr %1, i64 84
  store i32 98, ptr %8, align 4, !tbaa !5
  %9 = getelementptr i8, ptr %1, i64 88
  store i32 99, ptr %9, align 4, !tbaa !5
  %10 = getelementptr i8, ptr %1, i64 92
  %11 = getelementptr i8, ptr %1, i64 108
  tail call void @llvm.memset.p0.i64(ptr noundef nonnull align 4 dereferenceable(16) %10, i8 0, i64 16, i1 false)
  store <4 x i32> <i32 120, i32 0, i32 120, i32 0>, ptr %11, align 4, !tbaa !5
  %12 = getelementptr i8, ptr %1, i64 124
  store <4 x i32> <i32 0, i32 120, i32 109, i32 121>, ptr %12, align 4, !tbaa !5
  %13 = getelementptr i8, ptr %1, i64 140
  store <4 x i32> <i32 115, i32 116, i32 114, i32 105>, ptr %13, align 4, !tbaa !5
  %14 = getelementptr i8, ptr %1, i64 156
  store <4 x i32> <i32 110, i32 103, i32 109, i32 121>, ptr %14, align 4, !tbaa !5
  %15 = getelementptr i8, ptr %1, i64 172
  store <4 x i32> <i32 115, i32 116, i32 114, i32 105>, ptr %15, align 4, !tbaa !5
  %16 = getelementptr i8, ptr %1, i64 188
  store i32 110, ptr %16, align 4, !tbaa !5
  %17 = getelementptr i8, ptr %1, i64 192
  store i32 103, ptr %17, align 4, !tbaa !5
  ret void
}

define void @lbls() #2 {
  br label %start
start:
  ret void
}

; Function Attrs: mustprogress nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #1

attributes #0 = { mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "zero-call-used-regs"="used-gpr" }
attributes #1 = { mustprogress nocallback nofree nounwind willreturn memory(argmem : write) }
attributes #2 = { mustprogress nocallback nofree nounwind willreturn memory(argmem:write) }

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
