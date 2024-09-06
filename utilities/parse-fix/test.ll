; ModuleID = 'printf.c'
source_filename = "printf.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx14.0.0"

%struct.out_fct_wrap_type = type { void (i8, i8*)*, i8* }
%union.anon = type { i64 }

@_ftoa.pow10 = internal constant [10 x double] [double 1.000000e+00, double 1.000000e+01, double 1.000000e+02, double 1.000000e+03, double 1.000000e+04, double 1.000000e+05, double 1.000000e+06, double 1.000000e+07, double 1.000000e+08, double 1.000000e+09], align 8
@.str = private unnamed_addr constant [4 x i8] c"nan\00", align 1
@.str.1 = private unnamed_addr constant [5 x i8] c"fni-\00", align 1
@.str.2 = private unnamed_addr constant [5 x i8] c"fni+\00", align 1
@.str.3 = private unnamed_addr constant [4 x i8] c"fni\00", align 1

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @_putchar(i8 noundef signext %0) #0 {
  %2 = alloca i8, align 1
  store i8 %0, i8* %2, align 1
  %3 = load i8, i8* %2, align 1
  %4 = sext i8 %3 to i32
  %5 = call i32 @putchar(i32 noundef %4)
  ret void
}

declare i32 @putchar(i32 noundef) #1

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @printf_(i8* noundef %0, ...) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i8*, align 8
  %4 = alloca [1 x i8], align 1
  %5 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %6 = bitcast i8** %3 to i8*
  call void @llvm.va_start(i8* %6)
  %7 = getelementptr inbounds [1 x i8], [1 x i8]* %4, i64 0, i64 0
  %8 = load i8*, i8** %2, align 8
  %9 = load i8*, i8** %3, align 8
  %10 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_char, i8* noundef %7, i64 noundef -1, i8* noundef %8, i8* noundef %9)
  store i32 %10, i32* %5, align 4
  %11 = bitcast i8** %3 to i8*
  call void @llvm.va_end(i8* %11)
  %12 = load i32, i32* %5, align 4
  ret i32 %12
}

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_start(i8*) #2

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i8* noundef %3, i8* noundef %4) #0 {
  %6 = alloca void (i8, i8*, i64, i64)*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i64, align 8
  %9 = alloca i8*, align 8
  %10 = alloca i8*, align 8
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i64, align 8
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i64, align 8
  %22 = alloca i64, align 8
  %23 = alloca i64, align 8
  %24 = alloca i64, align 8
  %25 = alloca i32, align 4
  %26 = alloca i32, align 4
  %27 = alloca i32, align 4
  %28 = alloca i32, align 4
  %29 = alloca i64, align 8
  %30 = alloca i64, align 8
  %31 = alloca i32, align 4
  %32 = alloca i32, align 4
  %33 = alloca i32, align 4
  %34 = alloca i32, align 4
  %35 = alloca double, align 8
  %36 = alloca double, align 8
  %37 = alloca i32, align 4
  %38 = alloca i32, align 4
  %39 = alloca i8*, align 8
  %40 = alloca i8*, align 8
  %41 = alloca i32, align 4
  %42 = alloca i8, align 1
  %43 = alloca i8*, align 8
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %6, align 8
  store i8* %1, i8** %7, align 8
  store i64 %2, i64* %8, align 8
  store i8* %3, i8** %9, align 8
  store i8* %4, i8** %10, align 8
  store i64 0, i64* %15, align 8
  %44 = load i8*, i8** %7, align 8
  %45 = icmp ne i8* %44, null
  br i1 %45, label %47, label %46

46:                                               ; preds = %5
  store void (i8, i8*, i64, i64)* @_out_null, void (i8, i8*, i64, i64)** %6, align 8
  br label %47

47:                                               ; preds = %46, %5
  br label %48

48:                                               ; preds = %696, %57, %47
  %49 = load i8*, i8** %9, align 8
  %50 = load i8, i8* %49, align 1
  %51 = icmp ne i8 %50, 0
  br i1 %51, label %52, label %697

52:                                               ; preds = %48
  %53 = load i8*, i8** %9, align 8
  %54 = load i8, i8* %53, align 1
  %55 = sext i8 %54 to i32
  %56 = icmp ne i32 %55, 37
  br i1 %56, label %57, label %67

57:                                               ; preds = %52
  %58 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %59 = load i8*, i8** %9, align 8
  %60 = load i8, i8* %59, align 1
  %61 = load i8*, i8** %7, align 8
  %62 = load i64, i64* %15, align 8
  %63 = add i64 %62, 1
  store i64 %63, i64* %15, align 8
  %64 = load i64, i64* %8, align 8
  call void %58(i8 noundef signext %60, i8* noundef %61, i64 noundef %62, i64 noundef %64)
  %65 = load i8*, i8** %9, align 8
  %66 = getelementptr inbounds i8, i8* %65, i32 1
  store i8* %66, i8** %9, align 8
  br label %48, !llvm.loop !9

67:                                               ; preds = %52
  %68 = load i8*, i8** %9, align 8
  %69 = getelementptr inbounds i8, i8* %68, i32 1
  store i8* %69, i8** %9, align 8
  br label %70

70:                                               ; preds = %67
  store i32 0, i32* %11, align 4
  br label %71

71:                                               ; preds = %102, %70
  %72 = load i8*, i8** %9, align 8
  %73 = load i8, i8* %72, align 1
  %74 = sext i8 %73 to i32
  switch i32 %74, label %100 [
    i32 48, label %75
    i32 45, label %80
    i32 43, label %85
    i32 32, label %90
    i32 35, label %95
  ]

75:                                               ; preds = %71
  %76 = load i32, i32* %11, align 4
  %77 = or i32 %76, 1
  store i32 %77, i32* %11, align 4
  %78 = load i8*, i8** %9, align 8
  %79 = getelementptr inbounds i8, i8* %78, i32 1
  store i8* %79, i8** %9, align 8
  store i32 1, i32* %14, align 4
  br label %101

80:                                               ; preds = %71
  %81 = load i32, i32* %11, align 4
  %82 = or i32 %81, 2
  store i32 %82, i32* %11, align 4
  %83 = load i8*, i8** %9, align 8
  %84 = getelementptr inbounds i8, i8* %83, i32 1
  store i8* %84, i8** %9, align 8
  store i32 1, i32* %14, align 4
  br label %101

85:                                               ; preds = %71
  %86 = load i32, i32* %11, align 4
  %87 = or i32 %86, 4
  store i32 %87, i32* %11, align 4
  %88 = load i8*, i8** %9, align 8
  %89 = getelementptr inbounds i8, i8* %88, i32 1
  store i8* %89, i8** %9, align 8
  store i32 1, i32* %14, align 4
  br label %101

90:                                               ; preds = %71
  %91 = load i32, i32* %11, align 4
  %92 = or i32 %91, 8
  store i32 %92, i32* %11, align 4
  %93 = load i8*, i8** %9, align 8
  %94 = getelementptr inbounds i8, i8* %93, i32 1
  store i8* %94, i8** %9, align 8
  store i32 1, i32* %14, align 4
  br label %101

95:                                               ; preds = %71
  %96 = load i32, i32* %11, align 4
  %97 = or i32 %96, 16
  store i32 %97, i32* %11, align 4
  %98 = load i8*, i8** %9, align 8
  %99 = getelementptr inbounds i8, i8* %98, i32 1
  store i8* %99, i8** %9, align 8
  store i32 1, i32* %14, align 4
  br label %101

100:                                              ; preds = %71
  store i32 0, i32* %14, align 4
  br label %101

101:                                              ; preds = %100, %95, %90, %85, %80, %75
  br label %102

102:                                              ; preds = %101
  %103 = load i32, i32* %14, align 4
  %104 = icmp ne i32 %103, 0
  br i1 %104, label %71, label %105, !llvm.loop !11

105:                                              ; preds = %102
  store i32 0, i32* %12, align 4
  %106 = load i8*, i8** %9, align 8
  %107 = load i8, i8* %106, align 1
  %108 = call zeroext i1 @_is_digit(i8 noundef signext %107)
  br i1 %108, label %109, label %111

109:                                              ; preds = %105
  %110 = call i32 @_atoi(i8** noundef %9)
  store i32 %110, i32* %12, align 4
  br label %132

111:                                              ; preds = %105
  %112 = load i8*, i8** %9, align 8
  %113 = load i8, i8* %112, align 1
  %114 = sext i8 %113 to i32
  %115 = icmp eq i32 %114, 42
  br i1 %115, label %116, label %131

116:                                              ; preds = %111
  %117 = va_arg i8** %10, i32
  store i32 %117, i32* %17, align 4
  %118 = load i32, i32* %17, align 4
  store i32 %118, i32* %16, align 4
  %119 = load i32, i32* %16, align 4
  %120 = icmp slt i32 %119, 0
  br i1 %120, label %121, label %126

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare double @llvm.fmuladd.f64(double, double, double) #3

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
attributes #1 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
attributes #2 = { nofree nosync nounwind willreturn }
attributes #3 = { nofree nosync nounwind readnone speculatable willreturn }

!llvm.module.flags = !{!0, !1, !2, !3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"branch-target-enforcement", i32 0}
!2 = !{i32 1, !"sign-return-address", i32 0}
!3 = !{i32 1, !"sign-return-address-all", i32 0}
!4 = !{i32 1, !"sign-return-address-with-bkey", i32 0}
!5 = !{i32 7, !"PIC Level", i32 2}
!6 = !{i32 7, !"uwtable", i32 1}
!7 = !{i32 7, !"frame-pointer", i32 1}
!8 = !{!"Homebrew clang version 14.0.6"}
!9 = distinct !{!9, !10}
!10 = !{!"llvm.loop.mustprogress"}
!11 = distinct !{!11, !10}
!12 = distinct !{!12, !10}
!13 = distinct !{!13, !10}
!14 = distinct !{!14, !10}
!15 = distinct !{!15, !10}
!16 = distinct !{!16, !10}
!17 = distinct !{!17, !10}
!18 = distinct !{!18, !10}
!19 = distinct !{!19, !10}
!20 = distinct !{!20, !10}
!21 = distinct !{!21, !10}
!22 = distinct !{!22, !10}
!23 = distinct !{!23, !10}
!24 = distinct !{!24, !10}
!25 = distinct !{!25, !10}
!26 = distinct !{!26, !10}
!27 = distinct !{!27, !10}
!28 = distinct !{!28, !10}
!29 = distinct !{!29, !10}
!30 = distinct !{!30, !10}
!31 = distinct !{!31, !10}
