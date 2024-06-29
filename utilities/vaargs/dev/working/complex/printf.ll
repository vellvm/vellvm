; ModuleID = 'printf.c'
source_filename = "printf.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx14.0.0"

%struct.output_gadget_t = type { void (i8, i8*)*, i8*, i8*, i32, i32 }
%struct.scaling_factor = type { double, i8 }
%struct.double_components = type { i64, i64, i8 }
%union.double_with_bit_access = type { i64 }

@.str = private unnamed_addr constant [7 x i8] c")llun(\00", align 1
@.str.1 = private unnamed_addr constant [6 x i8] c")lin(\00", align 1
@.str.2 = private unnamed_addr constant [4 x i8] c"nan\00", align 1
@.str.3 = private unnamed_addr constant [5 x i8] c"fni-\00", align 1
@.str.4 = private unnamed_addr constant [5 x i8] c"fni+\00", align 1
@.str.5 = private unnamed_addr constant [4 x i8] c"fni\00", align 1
@powers_of_10 = internal constant [18 x double] [double 1.000000e+00, double 1.000000e+01, double 1.000000e+02, double 1.000000e+03, double 1.000000e+04, double 1.000000e+05, double 1.000000e+06, double 1.000000e+07, double 1.000000e+08, double 1.000000e+09, double 1.000000e+10, double 1.000000e+11, double 1.000000e+12, double 1.000000e+13, double 1.000000e+14, double 1.000000e+15, double 1.000000e+16, double 1.000000e+17], align 8

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vprintf_(i8* noundef %0, i8* noundef %1) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i8*, align 8
  %5 = alloca %struct.output_gadget_t, align 8
  store i8* %0, i8** %3, align 8
  store i8* %1, i8** %4, align 8
  call void @extern_putchar_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %5)
  %6 = load i8*, i8** %3, align 8
  %7 = load i8*, i8** %4, align 8
  %8 = call i32 @vsnprintf_impl(%struct.output_gadget_t* noundef %5, i8* noundef %6, i8* noundef %7)
  ret i32 %8
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @extern_putchar_gadget(%struct.output_gadget_t* noalias sret(%struct.output_gadget_t) align 8 %0) #0 {
  call void @function_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %0, void (i8, i8*)* noundef @putchar_wrapper, i8* noundef null)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @vsnprintf_impl(%struct.output_gadget_t* noundef %0, i8* noundef %1, i8* noundef %2) #0 {
  %4 = alloca %struct.output_gadget_t*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  %7 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %8 = load i8*, i8** %5, align 8
  %9 = load i8*, i8** %6, align 8
  call void @format_string_loop(%struct.output_gadget_t* noundef %7, i8* noundef %8, i8* noundef %9)
  %10 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @append_termination_with_gadget(%struct.output_gadget_t* noundef %10)
  %11 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %12 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %11, i32 0, i32 3
  %13 = load i32, i32* %12, align 8
  ret i32 %13
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vsnprintf_(i8* noundef %0, i64 noundef %1, i8* noundef %2, i8* noundef %3) #0 {
  %5 = alloca i8*, align 8
  %6 = alloca i64, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i8*, align 8
  %9 = alloca %struct.output_gadget_t, align 8
  store i8* %0, i8** %5, align 8
  store i64 %1, i64* %6, align 8
  store i8* %2, i8** %7, align 8
  store i8* %3, i8** %8, align 8
  %10 = load i8*, i8** %5, align 8
  %11 = load i64, i64* %6, align 8
  call void @buffer_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %9, i8* noundef %10, i64 noundef %11)
  %12 = load i8*, i8** %7, align 8
  %13 = load i8*, i8** %8, align 8
  %14 = call i32 @vsnprintf_impl(%struct.output_gadget_t* noundef %9, i8* noundef %12, i8* noundef %13)
  ret i32 %14
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @buffer_gadget(%struct.output_gadget_t* noalias sret(%struct.output_gadget_t) align 8 %0, i8* noundef %1, i64 noundef %2) #0 {
  %4 = alloca i8*, align 8
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  store i8* %1, i8** %4, align 8
  store i64 %2, i64* %5, align 8
  %7 = load i64, i64* %5, align 8
  %8 = icmp ugt i64 %7, 2147483647
  br i1 %8, label %9, label %10

9:                                                ; preds = %3
  br label %13

10:                                               ; preds = %3
  %11 = load i64, i64* %5, align 8
  %12 = trunc i64 %11 to i32
  br label %13

13:                                               ; preds = %10, %9
  %14 = phi i32 [ 2147483647, %9 ], [ %12, %10 ]
  store i32 %14, i32* %6, align 4
  call void @discarding_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %0)
  %15 = load i8*, i8** %4, align 8
  %16 = icmp ne i8* %15, null
  br i1 %16, label %17, label %22

17:                                               ; preds = %13
  %18 = load i8*, i8** %4, align 8
  %19 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 2
  store i8* %18, i8** %19, align 8
  %20 = load i32, i32* %6, align 4
  %21 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 4
  store i32 %20, i32* %21, align 4
  br label %22

22:                                               ; preds = %17, %13
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vsprintf_(i8* noundef %0, i8* noundef %1, i8* noundef %2) #0 {
  %4 = alloca i8*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  store i8* %0, i8** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  %7 = load i8*, i8** %4, align 8
  %8 = load i8*, i8** %5, align 8
  %9 = load i8*, i8** %6, align 8
  %10 = call i32 @vsnprintf_(i8* noundef %7, i64 noundef 2147483647, i8* noundef %8, i8* noundef %9)
  ret i32 %10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vfctprintf(void (i8, i8*)* noundef %0, i8* noundef %1, i8* noundef %2, i8* noundef %3) #0 {
  %5 = alloca void (i8, i8*)*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i8*, align 8
  %9 = alloca %struct.output_gadget_t, align 8
  store void (i8, i8*)* %0, void (i8, i8*)** %5, align 8
  store i8* %1, i8** %6, align 8
  store i8* %2, i8** %7, align 8
  store i8* %3, i8** %8, align 8
  %10 = load void (i8, i8*)*, void (i8, i8*)** %5, align 8
  %11 = load i8*, i8** %6, align 8
  call void @function_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %9, void (i8, i8*)* noundef %10, i8* noundef %11)
  %12 = load i8*, i8** %7, align 8
  %13 = load i8*, i8** %8, align 8
  %14 = call i32 @vsnprintf_impl(%struct.output_gadget_t* noundef %9, i8* noundef %12, i8* noundef %13)
  ret i32 %14
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @function_gadget(%struct.output_gadget_t* noalias sret(%struct.output_gadget_t) align 8 %0, void (i8, i8*)* noundef %1, i8* noundef %2) #0 {
  %4 = alloca void (i8, i8*)*, align 8
  %5 = alloca i8*, align 8
  store void (i8, i8*)* %1, void (i8, i8*)** %4, align 8
  store i8* %2, i8** %5, align 8
  call void @discarding_gadget(%struct.output_gadget_t* sret(%struct.output_gadget_t) align 8 %0)
  %6 = load void (i8, i8*)*, void (i8, i8*)** %4, align 8
  %7 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 0
  store void (i8, i8*)* %6, void (i8, i8*)** %7, align 8
  %8 = load i8*, i8** %5, align 8
  %9 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 1
  store i8* %8, i8** %9, align 8
  %10 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 4
  store i32 2147483647, i32* %10, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @printf_(i8* noundef %0, ...) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i8*, align 8
  %4 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  %5 = bitcast i8** %3 to i8*
  call void @llvm.va_start(i8* %5)
  %6 = load i8*, i8** %2, align 8
  %7 = load i8*, i8** %3, align 8
  %8 = call i32 @vprintf_(i8* noundef %6, i8* noundef %7)
  store i32 %8, i32* %4, align 4
  %9 = bitcast i8** %3 to i8*
  call void @llvm.va_end(i8* %9)
  %10 = load i32, i32* %4, align 4
  ret i32 %10
}

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_start(i8*) #1

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_end(i8*) #1

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @sprintf_(i8* noundef %0, i8* noundef %1, ...) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i8*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i32, align 4
  store i8* %0, i8** %3, align 8
  store i8* %1, i8** %4, align 8
  %7 = bitcast i8** %5 to i8*
  call void @llvm.va_start(i8* %7)
  %8 = load i8*, i8** %3, align 8
  %9 = load i8*, i8** %4, align 8
  %10 = load i8*, i8** %5, align 8
  %11 = call i32 @vsprintf_(i8* noundef %8, i8* noundef %9, i8* noundef %10)
  store i32 %11, i32* %6, align 4
  %12 = bitcast i8** %5 to i8*
  call void @llvm.va_end(i8* %12)
  %13 = load i32, i32* %6, align 4
  ret i32 %13
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @snprintf_(i8* noundef %0, i64 noundef %1, i8* noundef %2, ...) #0 {
  %4 = alloca i8*, align 8
  %5 = alloca i64, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i32, align 4
  store i8* %0, i8** %4, align 8
  store i64 %1, i64* %5, align 8
  store i8* %2, i8** %6, align 8
  %9 = bitcast i8** %7 to i8*
  call void @llvm.va_start(i8* %9)
  %10 = load i8*, i8** %4, align 8
  %11 = load i64, i64* %5, align 8
  %12 = load i8*, i8** %6, align 8
  %13 = load i8*, i8** %7, align 8
  %14 = call i32 @vsnprintf_(i8* noundef %10, i64 noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @fctprintf(void (i8, i8*)* noundef %0, i8* noundef %1, i8* noundef %2, ...) #0 {
  %4 = alloca void (i8, i8*)*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i32, align 4
  store void (i8, i8*)* %0, void (i8, i8*)** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  %9 = bitcast i8** %7 to i8*
  call void @llvm.va_start(i8* %9)
  %10 = load void (i8, i8*)*, void (i8, i8*)** %4, align 8
  %11 = load i8*, i8** %5, align 8
  %12 = load i8*, i8** %6, align 8
  %13 = load i8*, i8** %7, align 8
  %14 = call i32 @vfctprintf(void (i8, i8*)* noundef %10, i8* noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @putchar_wrapper(i8 noundef signext %0, i8* noundef %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i8*, align 8
  store i8 %0, i8* %3, align 1
  store i8* %1, i8** %4, align 8
  %5 = load i8*, i8** %4, align 8
  %6 = load i8, i8* %3, align 1
  call void @putchar_(i8 noundef signext %6)
  ret void
}

declare void @putchar_(i8 noundef signext) #2

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @format_string_loop(%struct.output_gadget_t* noundef %0, i8* noundef %1, i8* noundef %2) #0 {
  %4 = alloca %struct.output_gadget_t*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i8, align 1
  %15 = alloca i64, align 8
  %16 = alloca i64, align 8
  %17 = alloca i64, align 8
  %18 = alloca i64, align 8
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  %22 = alloca i32, align 4
  %23 = alloca i64, align 8
  %24 = alloca i64, align 8
  %25 = alloca i32, align 4
  %26 = alloca i32, align 4
  %27 = alloca i32, align 4
  %28 = alloca i32, align 4
  %29 = alloca double, align 8
  %30 = alloca double, align 8
  %31 = alloca i32, align 4
  %32 = alloca i32, align 4
  %33 = alloca i8*, align 8
  %34 = alloca i8*, align 8
  %35 = alloca i32, align 4
  %36 = alloca i64, align 8
  %37 = alloca i8*, align 8
  %38 = alloca i8*, align 8
  %39 = alloca i16*, align 8
  %40 = alloca i64*, align 8
  %41 = alloca i64*, align 8
  %42 = alloca i32*, align 8
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  br label %43

43:                                               ; preds = %725, %52, %3
  %44 = load i8*, i8** %5, align 8
  %45 = load i8, i8* %44, align 1
  %46 = icmp ne i8 %45, 0
  br i1 %46, label %47, label %726

47:                                               ; preds = %43
  %48 = load i8*, i8** %5, align 8
  %49 = load i8, i8* %48, align 1
  %50 = sext i8 %49 to i32
  %51 = icmp ne i32 %50, 37
  br i1 %51, label %52, label %58

52:                                               ; preds = %47
  %53 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %54 = load i8*, i8** %5, align 8
  %55 = load i8, i8* %54, align 1
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %53, i8 noundef signext %55)
  %56 = load i8*, i8** %5, align 8
  %57 = getelementptr inbounds i8, i8* %56, i32 1
  store i8* %57, i8** %5, align 8
  br label %43, !llvm.loop !9

58:                                               ; preds = %47
  br label %59

59:                                               ; preds = %58
  %60 = load i8*, i8** %5, align 8
  %61 = getelementptr inbounds i8, i8* %60, i32 1
  store i8* %61, i8** %5, align 8
  %62 = load i8*, i8** %5, align 8
  %63 = load i8, i8* %62, align 1
  %64 = icmp ne i8 %63, 0
  br i1 %64, label %66, label %65

65:                                               ; preds = %59
  br label %726

66:                                               ; preds = %59
  br label %67

67:                                               ; preds = %66
  %68 = call i32 @parse_flags(i8** noundef %5)
  store i32 %68, i32* %7, align 4
  store i32 0, i32* %8, align 4
  %69 = load i8*, i8** %5, align 8
  %70 = load i8, i8* %69, align 1
  %71 = call zeroext i1 @is_digit_(i8 noundef signext %70)
  br i1 %71, label %72, label %74

72:                                               ; preds = %67
  %73 = call i32 @atou_(i8** noundef %5)
  store i32 %73, i32* %8, align 4
  br label %102

74:                                               ; preds = %67
  %75 = load i8*, i8** %5, align 8
  %76 = load i8, i8* %75, align 1
  %77 = sext i8 %76 to i32
  %78 = icmp eq i32 %77, 42
  br i1 %78, label %79, label %101

79:                                               ; preds = %74
  %80 = va_arg i8** %6, i32
  store i32 %80, i32* %10, align 4
  %81 = load i32, i32* %10, align 4
  store i32 %81, i32* %9, align 4
  %82 = load i32, i32* %9, align 4
  %83 = icmp slt i32 %82, 0
  br i1 %83, label %84, label %89

84:                                               ; preds = %79
  %85 = load i32, i32* %7, align 4
  %86 = or i32 %85, 2
  store i32 %86, i32* %7, align 4
  %87 = load i32, i32* %9, align 4
  %88 = sub nsw i32 0, %87
  store i32 %88, i32* %8, align 4
  br label %91

89:                                               ; preds = %79
  %90 = load i32, i32* %9, align 4
  store i32 %90, i32* %8, align 4
  br label %91

91:                                               ; preds = %89, %84
  br label %92

92:                                               ; preds = %91
  %93 = load i8*, i8** %5, align 8
  %94 = getelementptr inbounds i8, i8* %93, i32 1
  store i8* %94, i8** %5, align 8
  %95 = load i8*, i8** %5, align 8
  %96 = load i8, i8* %95, align 1
  %97 = icmp ne i8 %96, 0
  br i1 %97, label %99, label %98

98:                                               ; preds = %92
  br label %726

99:                                               ; preds = %92
  br label %100

100:                                              ; preds = %99
  br label %101

101:                                              ; preds = %100, %74
  br label %102

102:                                              ; preds = %101, %72
  store i32 0, i32* %11, align 4
  %103 = load i8*, i8** %5, align 8
  %104 = load i8, i8* %103, align 1
  %105 = sext i8 %104 to i32
  %106 = icmp eq i32 %105, 46
  br i1 %106, label %107, label %150

107:                                              ; preds = %102
  %108 = load i32, i32* %7, align 4
  %109 = or i32 %108, 2048
  store i32 %109, i32* %7, align 4
  br label %110

110:                                              ; preds = %107
  %111 = load i8*, i8** %5, align 8
  %112 = getelementptr inbounds i8, i8* %111, i32 1
  store i8* %112, i8** %5, align 8
  %113 = load i8*, i8** %5, align 8
  %114 = load i8, i8* %113, align 1
  %115 = icmp ne i8 %114, 0
  br i1 %115, label %117, label %116

116:                                              ; preds = %110
  br label %726

117:                                              ; preds = %110
  br label %118

118:                                              ; preds = %117
  %119 = load i8*, i8** %5, align 8
  %120 = load i8, i8* %119, align 1
  %121 = call zeroext i1 @is_digit_(i8 noundef signext %120)
  br i1 %121, label %122, label %124

122:                                              ; preds = %118
  %123 = call i32 @atou_(i8** noundef %5)
  store i32 %123, i32* %11, align 4
  br label %149

124:                                              ; preds = %118
  %125 = load i8*, i8** %5, align 8
  %126 = load i8, i8* %125, align 1
  %127 = sext i8 %126 to i32
  %128 = icmp eq i32 %127, 42
  br i1 %128, label %129, label %148

129:                                              ; preds = %124
  %130 = va_arg i8** %6, i32
  store i32 %130, i32* %13, align 4
  %131 = load i32, i32* %13, align 4
  store i32 %131, i32* %12, align 4
  %132 = load i32, i32* %12, align 4
  %133 = icmp sgt i32 %132, 0
  br i1 %133, label %134, label %136

134:                                              ; preds = %129
  %135 = load i32, i32* %12, align 4
  br label %137

136:                                              ; preds = %129
  br label %137

137:                                              ; preds = %136, %134
  %138 = phi i32 [ %135, %134 ], [ 0, %136 ]
  store i32 %138, i32* %11, align 4
  br label %139

139:                                              ; preds = %137
  %140 = load i8*, i8** %5, align 8
  %141 = getelementptr inbounds i8, i8* %140, i32 1
  store i8* %141, i8** %5, align 8
  %142 = load i8*, i8** %5, align 8
  %143 = load i8, i8* %142, align 1
  %144 = icmp ne i8 %143, 0
  br i1 %144, label %146, label %145

145:                                              ; preds = %139
  br label %726

146:                                              ; preds = %139
  br label %147

147:                                              ; preds = %146
  br label %148

148:                                              ; preds = %147, %124
  br label %149

149:                                              ; preds = %148, %122
  br label %150

150:                                              ; preds = %149, %102
  %151 = load i8*, i8** %5, align 8
  %152 = load i8, i8* %151, align 1
  %153 = sext i8 %152 to i32
  switch i32 %153, label %248 [
    i32 108, label %154
    i32 104, label %183
    i32 116, label %212
    i32 106, label %224
    i32 122, label %236
  ]

154:                                              ; preds = %150
  %155 = load i32, i32* %7, align 4
  %156 = or i32 %155, 512
  store i32 %156, i32* %7, align 4
  br label %157

157:                                              ; preds = %154
  %158 = load i8*, i8** %5, align 8
  %159 = getelementptr inbounds i8, i8* %158, i32 1
  store i8* %159, i8** %5, align 8
  %160 = load i8*, i8** %5, align 8
  %161 = load i8, i8* %160, align 1
  %162 = icmp ne i8 %161, 0
  br i1 %162, label %164, label %163

163:                                              ; preds = %157
  br label %726

164:                                              ; preds = %157
  br label %165

165:                                              ; preds = %164
  %166 = load i8*, i8** %5, align 8
  %167 = load i8, i8* %166, align 1
  %168 = sext i8 %167 to i32
  %169 = icmp eq i32 %168, 108
  br i1 %169, label %170, label %182

170:                                              ; preds = %165
  %171 = load i32, i32* %7, align 4
  %172 = or i32 %171, 1024
  store i32 %172, i32* %7, align 4
  br label %173

173:                                              ; preds = %170
  %174 = load i8*, i8** %5, align 8
  %175 = getelementptr inbounds i8, i8* %174, i32 1
  store i8* %175, i8** %5, align 8
  %176 = load i8*, i8** %5, align 8
  %177 = load i8, i8* %176, align 1
  %178 = icmp ne i8 %177, 0
  br i1 %178, label %180, label %179

179:                                              ; preds = %173
  br label %726

180:                                              ; preds = %173
  br label %181

181:                                              ; preds = %180
  br label %182

182:                                              ; preds = %181, %165
  br label %249

183:                                              ; preds = %150
  %184 = load i32, i32* %7, align 4
  %185 = or i32 %184, 128
  store i32 %185, i32* %7, align 4
  br label %186

186:                                              ; preds = %183
  %187 = load i8*, i8** %5, align 8
  %188 = getelementptr inbounds i8, i8* %187, i32 1
  store i8* %188, i8** %5, align 8
  %189 = load i8*, i8** %5, align 8
  %190 = load i8, i8* %189, align 1
  %191 = icmp ne i8 %190, 0
  br i1 %191, label %193, label %192

192:                                              ; preds = %186
  br label %726

193:                                              ; preds = %186
  br label %194

194:                                              ; preds = %193
  %195 = load i8*, i8** %5, align 8
  %196 = load i8, i8* %195, align 1
  %197 = sext i8 %196 to i32
  %198 = icmp eq i32 %197, 104
  br i1 %198, label %199, label %211

199:                                              ; preds = %194
  %200 = load i32, i32* %7, align 4
  %201 = or i32 %200, 64
  store i32 %201, i32* %7, align 4
  br label %202

202:                                              ; preds = %199
  %203 = load i8*, i8** %5, align 8
  %204 = getelementptr inbounds i8, i8* %203, i32 1
  store i8* %204, i8** %5, align 8
  %205 = load i8*, i8** %5, align 8
  %206 = load i8, i8* %205, align 1
  %207 = icmp ne i8 %206, 0
  br i1 %207, label %209, label %208

208:                                              ; preds = %202
  br label %726

209:                                              ; preds = %202
  br label %210

210:                                              ; preds = %209
  br label %211

211:                                              ; preds = %210, %194
  br label %249

212:                                              ; preds = %150
  %213 = load i32, i32* %7, align 4
  %214 = or i32 %213, 512
  store i32 %214, i32* %7, align 4
  br label %215

215:                                              ; preds = %212
  %216 = load i8*, i8** %5, align 8
  %217 = getelementptr inbounds i8, i8* %216, i32 1
  store i8* %217, i8** %5, align 8
  %218 = load i8*, i8** %5, align 8
  %219 = load i8, i8* %218, align 1
  %220 = icmp ne i8 %219, 0
  br i1 %220, label %222, label %221

221:                                              ; preds = %215
  br label %726

222:                                              ; preds = %215
  br label %223

223:                                              ; preds = %222
  br label %249

224:                                              ; preds = %150
  %225 = load i32, i32* %7, align 4
  %226 = or i32 %225, 512
  store i32 %226, i32* %7, align 4
  br label %227

227:                                              ; preds = %224
  %228 = load i8*, i8** %5, align 8
  %229 = getelementptr inbounds i8, i8* %228, i32 1
  store i8* %229, i8** %5, align 8
  %230 = load i8*, i8** %5, align 8
  %231 = load i8, i8* %230, align 1
  %232 = icmp ne i8 %231, 0
  br i1 %232, label %234, label %233

233:                                              ; preds = %227
  br label %726

234:                                              ; preds = %227
  br label %235

235:                                              ; preds = %234
  br label %249

236:                                              ; preds = %150
  %237 = load i32, i32* %7, align 4
  %238 = or i32 %237, 512
  store i32 %238, i32* %7, align 4
  br label %239

239:                                              ; preds = %236
  %240 = load i8*, i8** %5, align 8
  %241 = getelementptr inbounds i8, i8* %240, i32 1
  store i8* %241, i8** %5, align 8
  %242 = load i8*, i8** %5, align 8
  %243 = load i8, i8* %242, align 1
  %244 = icmp ne i8 %243, 0
  br i1 %244, label %246, label %245

245:                                              ; preds = %239
  br label %726

246:                                              ; preds = %239
  br label %247

247:                                              ; preds = %246
  br label %249

248:                                              ; preds = %150
  br label %249

249:                                              ; preds = %248, %247, %235, %223, %211, %182
  %250 = load i8*, i8** %5, align 8
  %251 = load i8, i8* %250, align 1
  %252 = sext i8 %251 to i32
  switch i32 %252, label %719 [
    i32 100, label %253
    i32 105, label %253
    i32 117, label %253
    i32 120, label %253
    i32 88, label %253
    i32 111, label %253
    i32 98, label %253
    i32 102, label %467
    i32 70, label %467
    i32 101, label %484
    i32 69, label %484
    i32 103, label %484
    i32 71, label %484
    i32 99, label %519
    i32 115, label %552
    i32 112, label %638
    i32 37, label %659
    i32 110, label %663
  ]

253:                                              ; preds = %249, %249, %249, %249, %249, %249, %249
  %254 = load i8*, i8** %5, align 8
  %255 = load i8, i8* %254, align 1
  %256 = sext i8 %255 to i32
  %257 = icmp eq i32 %256, 100
  br i1 %257, label %263, label %258

258:                                              ; preds = %253
  %259 = load i8*, i8** %5, align 8
  %260 = load i8, i8* %259, align 1
  %261 = sext i8 %260 to i32
  %262 = icmp eq i32 %261, 105
  br i1 %262, label %263, label %266

263:                                              ; preds = %258, %253
  %264 = load i32, i32* %7, align 4
  %265 = or i32 %264, 16384
  store i32 %265, i32* %7, align 4
  br label %266

266:                                              ; preds = %263, %258
  %267 = load i8*, i8** %5, align 8
  %268 = load i8, i8* %267, align 1
  %269 = sext i8 %268 to i32
  %270 = icmp eq i32 %269, 120
  br i1 %270, label %276, label %271

271:                                              ; preds = %266
  %272 = load i8*, i8** %5, align 8
  %273 = load i8, i8* %272, align 1
  %274 = sext i8 %273 to i32
  %275 = icmp eq i32 %274, 88
  br i1 %275, label %276, label %277

276:                                              ; preds = %271, %266
  store i8 16, i8* %14, align 1
  br label %294

277:                                              ; preds = %271
  %278 = load i8*, i8** %5, align 8
  %279 = load i8, i8* %278, align 1
  %280 = sext i8 %279 to i32
  %281 = icmp eq i32 %280, 111
  br i1 %281, label %282, label %283

282:                                              ; preds = %277
  store i8 8, i8* %14, align 1
  br label %293

283:                                              ; preds = %277
  %284 = load i8*, i8** %5, align 8
  %285 = load i8, i8* %284, align 1
  %286 = sext i8 %285 to i32
  %287 = icmp eq i32 %286, 98
  br i1 %287, label %288, label %289

288:                                              ; preds = %283
  store i8 2, i8* %14, align 1
  br label %292

289:                                              ; preds = %283
  store i8 10, i8* %14, align 1
  %290 = load i32, i32* %7, align 4
  %291 = and i32 %290, -17
  store i32 %291, i32* %7, align 4
  br label %292

292:                                              ; preds = %289, %288
  br label %293

293:                                              ; preds = %292, %282
  br label %294

294:                                              ; preds = %293, %276
  %295 = load i8*, i8** %5, align 8
  %296 = load i8, i8* %295, align 1
  %297 = sext i8 %296 to i32
  %298 = icmp eq i32 %297, 88
  br i1 %298, label %299, label %302

299:                                              ; preds = %294
  %300 = load i32, i32* %7, align 4
  %301 = or i32 %300, 32
  store i32 %301, i32* %7, align 4
  br label %302

302:                                              ; preds = %299, %294
  %303 = load i8*, i8** %5, align 8
  %304 = getelementptr inbounds i8, i8* %303, i32 1
  store i8* %304, i8** %5, align 8
  %305 = load i32, i32* %7, align 4
  %306 = and i32 %305, 2048
  %307 = icmp ne i32 %306, 0
  br i1 %307, label %308, label %311

308:                                              ; preds = %302
  %309 = load i32, i32* %7, align 4
  %310 = and i32 %309, -2
  store i32 %310, i32* %7, align 4
  br label %311

311:                                              ; preds = %308, %302
  %312 = load i32, i32* %7, align 4
  %313 = and i32 %312, 16384
  %314 = icmp ne i32 %313, 0
  br i1 %314, label %315, label %406

315:                                              ; preds = %311
  %316 = load i32, i32* %7, align 4
  %317 = and i32 %316, 1024
  %318 = icmp ne i32 %317, 0
  br i1 %318, label %319, label %338

319:                                              ; preds = %315
  %320 = va_arg i8** %6, i64
  store i64 %320, i64* %16, align 8
  %321 = load i64, i64* %16, align 8
  store i64 %321, i64* %15, align 8
  %322 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %323 = load i64, i64* %15, align 8
  %324 = icmp sgt i64 %323, 0
  br i1 %324, label %325, label %327

325:                                              ; preds = %319
  %326 = load i64, i64* %15, align 8
  br label %330

327:                                              ; preds = %319
  %328 = load i64, i64* %15, align 8
  %329 = sub nsw i64 0, %328
  br label %330

330:                                              ; preds = %327, %325
  %331 = phi i64 [ %326, %325 ], [ %329, %327 ]
  %332 = load i64, i64* %15, align 8
  %333 = icmp slt i64 %332, 0
  %334 = load i8, i8* %14, align 1
  %335 = load i32, i32* %11, align 4
  %336 = load i32, i32* %8, align 4
  %337 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %322, i64 noundef %331, i1 noundef zeroext %333, i8 noundef zeroext %334, i32 noundef %335, i32 noundef %336, i32 noundef %337)
  br label %405

338:                                              ; preds = %315
  %339 = load i32, i32* %7, align 4
  %340 = and i32 %339, 512
  %341 = icmp ne i32 %340, 0
  br i1 %341, label %342, label %361

342:                                              ; preds = %338
  %343 = va_arg i8** %6, i64
  store i64 %343, i64* %18, align 8
  %344 = load i64, i64* %18, align 8
  store i64 %344, i64* %17, align 8
  %345 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %346 = load i64, i64* %17, align 8
  %347 = icmp sgt i64 %346, 0
  br i1 %347, label %348, label %350

348:                                              ; preds = %342
  %349 = load i64, i64* %17, align 8
  br label %353

350:                                              ; preds = %342
  %351 = load i64, i64* %17, align 8
  %352 = sub nsw i64 0, %351
  br label %353

353:                                              ; preds = %350, %348
  %354 = phi i64 [ %349, %348 ], [ %352, %350 ]
  %355 = load i64, i64* %17, align 8
  %356 = icmp slt i64 %355, 0
  %357 = load i8, i8* %14, align 1
  %358 = load i32, i32* %11, align 4
  %359 = load i32, i32* %8, align 4
  %360 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %345, i64 noundef %354, i1 noundef zeroext %356, i8 noundef zeroext %357, i32 noundef %358, i32 noundef %359, i32 noundef %360)
  br label %404

361:                                              ; preds = %338
  %362 = load i32, i32* %7, align 4
  %363 = and i32 %362, 64
  %364 = icmp ne i32 %363, 0
  br i1 %364, label %365, label %370

365:                                              ; preds = %361
  %366 = va_arg i8** %6, i32
  store i32 %366, i32* %20, align 4
  %367 = load i32, i32* %20, align 4
  %368 = trunc i32 %367 to i8
  %369 = sext i8 %368 to i32
  br label %384

370:                                              ; preds = %361
  %371 = load i32, i32* %7, align 4
  %372 = and i32 %371, 128
  %373 = icmp ne i32 %372, 0
  br i1 %373, label %374, label %379

374:                                              ; preds = %370
  %375 = va_arg i8** %6, i32
  store i32 %375, i32* %21, align 4
  %376 = load i32, i32* %21, align 4
  %377 = trunc i32 %376 to i16
  %378 = sext i16 %377 to i32
  br label %382

379:                                              ; preds = %370
  %380 = va_arg i8** %6, i32
  store i32 %380, i32* %22, align 4
  %381 = load i32, i32* %22, align 4
  br label %382

382:                                              ; preds = %379, %374
  %383 = phi i32 [ %378, %374 ], [ %381, %379 ]
  br label %384

384:                                              ; preds = %382, %365
  %385 = phi i32 [ %369, %365 ], [ %383, %382 ]
  store i32 %385, i32* %19, align 4
  %386 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %387 = load i32, i32* %19, align 4
  %388 = icmp sgt i32 %387, 0
  br i1 %388, label %389, label %392

389:                                              ; preds = %384
  %390 = load i32, i32* %19, align 4
  %391 = sext i32 %390 to i64
  br label %396

392:                                              ; preds = %384
  %393 = load i32, i32* %19, align 4
  %394 = sext i32 %393 to i64
  %395 = sub nsw i64 0, %394
  br label %396

396:                                              ; preds = %392, %389
  %397 = phi i64 [ %391, %389 ], [ %395, %392 ]
  %398 = load i32, i32* %19, align 4
  %399 = icmp slt i32 %398, 0
  %400 = load i8, i8* %14, align 1
  %401 = load i32, i32* %11, align 4
  %402 = load i32, i32* %8, align 4
  %403 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %386, i64 noundef %397, i1 noundef zeroext %399, i8 noundef zeroext %400, i32 noundef %401, i32 noundef %402, i32 noundef %403)
  br label %404

404:                                              ; preds = %396, %353
  br label %405

405:                                              ; preds = %404, %330
  br label %466

406:                                              ; preds = %311
  %407 = load i32, i32* %7, align 4
  %408 = and i32 %407, -13
  store i32 %408, i32* %7, align 4
  %409 = load i32, i32* %7, align 4
  %410 = and i32 %409, 1024
  %411 = icmp ne i32 %410, 0
  br i1 %411, label %412, label %420

412:                                              ; preds = %406
  %413 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %414 = va_arg i8** %6, i64
  store i64 %414, i64* %23, align 8
  %415 = load i64, i64* %23, align 8
  %416 = load i8, i8* %14, align 1
  %417 = load i32, i32* %11, align 4
  %418 = load i32, i32* %8, align 4
  %419 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %413, i64 noundef %415, i1 noundef zeroext false, i8 noundef zeroext %416, i32 noundef %417, i32 noundef %418, i32 noundef %419)
  br label %465

420:                                              ; preds = %406
  %421 = load i32, i32* %7, align 4
  %422 = and i32 %421, 512
  %423 = icmp ne i32 %422, 0
  br i1 %423, label %424, label %432

424:                                              ; preds = %420
  %425 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %426 = va_arg i8** %6, i64
  store i64 %426, i64* %24, align 8
  %427 = load i64, i64* %24, align 8
  %428 = load i8, i8* %14, align 1
  %429 = load i32, i32* %11, align 4
  %430 = load i32, i32* %8, align 4
  %431 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %425, i64 noundef %427, i1 noundef zeroext false, i8 noundef zeroext %428, i32 noundef %429, i32 noundef %430, i32 noundef %431)
  br label %464

432:                                              ; preds = %420
  %433 = load i32, i32* %7, align 4
  %434 = and i32 %433, 64
  %435 = icmp ne i32 %434, 0
  br i1 %435, label %436, label %441

436:                                              ; preds = %432
  %437 = va_arg i8** %6, i32
  store i32 %437, i32* %26, align 4
  %438 = load i32, i32* %26, align 4
  %439 = trunc i32 %438 to i8
  %440 = zext i8 %439 to i32
  br label %455

441:                                              ; preds = %432
  %442 = load i32, i32* %7, align 4
  %443 = and i32 %442, 128
  %444 = icmp ne i32 %443, 0
  br i1 %444, label %445, label %450

445:                                              ; preds = %441
  %446 = va_arg i8** %6, i32
  store i32 %446, i32* %27, align 4
  %447 = load i32, i32* %27, align 4
  %448 = trunc i32 %447 to i16
  %449 = zext i16 %448 to i32
  br label %453

450:                                              ; preds = %441
  %451 = va_arg i8** %6, i32
  store i32 %451, i32* %28, align 4
  %452 = load i32, i32* %28, align 4
  br label %453

453:                                              ; preds = %450, %445
  %454 = phi i32 [ %449, %445 ], [ %452, %450 ]
  br label %455

455:                                              ; preds = %453, %436
  %456 = phi i32 [ %440, %436 ], [ %454, %453 ]
  store i32 %456, i32* %25, align 4
  %457 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %458 = load i32, i32* %25, align 4
  %459 = zext i32 %458 to i64
  %460 = load i8, i8* %14, align 1
  %461 = load i32, i32* %11, align 4
  %462 = load i32, i32* %8, align 4
  %463 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %457, i64 noundef %459, i1 noundef zeroext false, i8 noundef zeroext %460, i32 noundef %461, i32 noundef %462, i32 noundef %463)
  br label %464

464:                                              ; preds = %455, %424
  br label %465

465:                                              ; preds = %464, %412
  br label %466

466:                                              ; preds = %465, %405
  br label %725

467:                                              ; preds = %249, %249
  %468 = load i8*, i8** %5, align 8
  %469 = load i8, i8* %468, align 1
  %470 = sext i8 %469 to i32
  %471 = icmp eq i32 %470, 70
  br i1 %471, label %472, label %475

472:                                              ; preds = %467
  %473 = load i32, i32* %7, align 4
  %474 = or i32 %473, 32
  store i32 %474, i32* %7, align 4
  br label %475

475:                                              ; preds = %472, %467
  %476 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %477 = va_arg i8** %6, double
  store double %477, double* %29, align 8
  %478 = load double, double* %29, align 8
  %479 = load i32, i32* %11, align 4
  %480 = load i32, i32* %8, align 4
  %481 = load i32, i32* %7, align 4
  call void @print_floating_point(%struct.output_gadget_t* noundef %476, double noundef %478, i32 noundef %479, i32 noundef %480, i32 noundef %481, i1 noundef zeroext false)
  %482 = load i8*, i8** %5, align 8
  %483 = getelementptr inbounds i8, i8* %482, i32 1
  store i8* %483, i8** %5, align 8
  br label %725

484:                                              ; preds = %249, %249, %249, %249
  %485 = load i8*, i8** %5, align 8
  %486 = load i8, i8* %485, align 1
  %487 = sext i8 %486 to i32
  %488 = icmp eq i32 %487, 103
  br i1 %488, label %494, label %489

489:                                              ; preds = %484
  %490 = load i8*, i8** %5, align 8
  %491 = load i8, i8* %490, align 1
  %492 = sext i8 %491 to i32
  %493 = icmp eq i32 %492, 71
  br i1 %493, label %494, label %497

494:                                              ; preds = %489, %484
  %495 = load i32, i32* %7, align 4
  %496 = or i32 %495, 4096
  store i32 %496, i32* %7, align 4
  br label %497

497:                                              ; preds = %494, %489
  %498 = load i8*, i8** %5, align 8
  %499 = load i8, i8* %498, align 1
  %500 = sext i8 %499 to i32
  %501 = icmp eq i32 %500, 69
  br i1 %501, label %507, label %502

502:                                              ; preds = %497
  %503 = load i8*, i8** %5, align 8
  %504 = load i8, i8* %503, align 1
  %505 = sext i8 %504 to i32
  %506 = icmp eq i32 %505, 71
  br i1 %506, label %507, label %510

507:                                              ; preds = %502, %497
  %508 = load i32, i32* %7, align 4
  %509 = or i32 %508, 32
  store i32 %509, i32* %7, align 4
  br label %510

510:                                              ; preds = %507, %502
  %511 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %512 = va_arg i8** %6, double
  store double %512, double* %30, align 8
  %513 = load double, double* %30, align 8
  %514 = load i32, i32* %11, align 4
  %515 = load i32, i32* %8, align 4
  %516 = load i32, i32* %7, align 4
  call void @print_floating_point(%struct.output_gadget_t* noundef %511, double noundef %513, i32 noundef %514, i32 noundef %515, i32 noundef %516, i1 noundef zeroext true)
  %517 = load i8*, i8** %5, align 8
  %518 = getelementptr inbounds i8, i8* %517, i32 1
  store i8* %518, i8** %5, align 8
  br label %725

519:                                              ; preds = %249
  store i32 1, i32* %31, align 4
  %520 = load i32, i32* %7, align 4
  %521 = and i32 %520, 2
  %522 = icmp ne i32 %521, 0
  br i1 %522, label %532, label %523

523:                                              ; preds = %519
  br label %524

524:                                              ; preds = %529, %523
  %525 = load i32, i32* %31, align 4
  %526 = add i32 %525, 1
  store i32 %526, i32* %31, align 4
  %527 = load i32, i32* %8, align 4
  %528 = icmp ult i32 %525, %527
  br i1 %528, label %529, label %531

529:                                              ; preds = %524
  %530 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %530, i8 noundef signext 32)
  br label %524, !llvm.loop !11

531:                                              ; preds = %524
  br label %532

532:                                              ; preds = %531, %519
  %533 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %534 = va_arg i8** %6, i32
  store i32 %534, i32* %32, align 4
  %535 = load i32, i32* %32, align 4
  %536 = trunc i32 %535 to i8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %533, i8 noundef signext %536)
  %537 = load i32, i32* %7, align 4
  %538 = and i32 %537, 2
  %539 = icmp ne i32 %538, 0
  br i1 %539, label %540, label %549

540:                                              ; preds = %532
  br label %541

541:                                              ; preds = %546, %540
  %542 = load i32, i32* %31, align 4
  %543 = add i32 %542, 1
  store i32 %543, i32* %31, align 4
  %544 = load i32, i32* %8, align 4
  %545 = icmp ult i32 %542, %544
  br i1 %545, label %546, label %548

546:                                              ; preds = %541
  %547 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %547, i8 noundef signext 32)
  br label %541, !llvm.loop !12

548:                                              ; preds = %541
  br label %549

549:                                              ; preds = %548, %532
  %550 = load i8*, i8** %5, align 8
  %551 = getelementptr inbounds i8, i8* %550, i32 1
  store i8* %551, i8** %5, align 8
  br label %725

552:                                              ; preds = %249
  %553 = va_arg i8** %6, i8*
  store i8* %553, i8** %34, align 8
  %554 = load i8*, i8** %34, align 8
  store i8* %554, i8** %33, align 8
  %555 = load i8*, i8** %33, align 8
  %556 = icmp eq i8* %555, null
  br i1 %556, label %557, label %561

557:                                              ; preds = %552
  %558 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %559 = load i32, i32* %8, align 4
  %560 = load i32, i32* %7, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %558, i8* noundef getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32 noundef 6, i32 noundef %559, i32 noundef %560)
  br label %635

561:                                              ; preds = %552
  %562 = load i8*, i8** %33, align 8
  %563 = load i32, i32* %11, align 4
  %564 = icmp ne i32 %563, 0
  br i1 %564, label %565, label %567

565:                                              ; preds = %561
  %566 = load i32, i32* %11, align 4
  br label %568

567:                                              ; preds = %561
  br label %568

568:                                              ; preds = %567, %565
  %569 = phi i32 [ %566, %565 ], [ 2147483647, %567 ]
  %570 = call i32 @strnlen_s_(i8* noundef %562, i32 noundef %569)
  store i32 %570, i32* %35, align 4
  %571 = load i32, i32* %7, align 4
  %572 = and i32 %571, 2048
  %573 = icmp ne i32 %572, 0
  br i1 %573, label %574, label %584

574:                                              ; preds = %568
  %575 = load i32, i32* %35, align 4
  %576 = load i32, i32* %11, align 4
  %577 = icmp ult i32 %575, %576
  br i1 %577, label %578, label %580

578:                                              ; preds = %574
  %579 = load i32, i32* %35, align 4
  br label %582

580:                                              ; preds = %574
  %581 = load i32, i32* %11, align 4
  br label %582

582:                                              ; preds = %580, %578
  %583 = phi i32 [ %579, %578 ], [ %581, %580 ]
  store i32 %583, i32* %35, align 4
  br label %584

584:                                              ; preds = %582, %568
  %585 = load i32, i32* %7, align 4
  %586 = and i32 %585, 2
  %587 = icmp ne i32 %586, 0
  br i1 %587, label %597, label %588

588:                                              ; preds = %584
  br label %589

589:                                              ; preds = %594, %588
  %590 = load i32, i32* %35, align 4
  %591 = add i32 %590, 1
  store i32 %591, i32* %35, align 4
  %592 = load i32, i32* %8, align 4
  %593 = icmp ult i32 %590, %592
  br i1 %593, label %594, label %596

594:                                              ; preds = %589
  %595 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %595, i8 noundef signext 32)
  br label %589, !llvm.loop !13

596:                                              ; preds = %589
  br label %597

597:                                              ; preds = %596, %584
  br label %598

598:                                              ; preds = %614, %597
  %599 = load i8*, i8** %33, align 8
  %600 = load i8, i8* %599, align 1
  %601 = sext i8 %600 to i32
  %602 = icmp ne i32 %601, 0
  br i1 %602, label %603, label %612

603:                                              ; preds = %598
  %604 = load i32, i32* %7, align 4
  %605 = and i32 %604, 2048
  %606 = icmp ne i32 %605, 0
  br i1 %606, label %607, label %610

607:                                              ; preds = %603
  %608 = load i32, i32* %11, align 4
  %609 = icmp ne i32 %608, 0
  br label %610

610:                                              ; preds = %607, %603
  %611 = phi i1 [ true, %603 ], [ %609, %607 ]
  br label %612

612:                                              ; preds = %610, %598
  %613 = phi i1 [ false, %598 ], [ %611, %610 ]
  br i1 %613, label %614, label %621

614:                                              ; preds = %612
  %615 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %616 = load i8*, i8** %33, align 8
  %617 = getelementptr inbounds i8, i8* %616, i32 1
  store i8* %617, i8** %33, align 8
  %618 = load i8, i8* %616, align 1
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %615, i8 noundef signext %618)
  %619 = load i32, i32* %11, align 4
  %620 = add i32 %619, -1
  store i32 %620, i32* %11, align 4
  br label %598, !llvm.loop !14

621:                                              ; preds = %612
  %622 = load i32, i32* %7, align 4
  %623 = and i32 %622, 2
  %624 = icmp ne i32 %623, 0
  br i1 %624, label %625, label %634

625:                                              ; preds = %621
  br label %626

626:                                              ; preds = %631, %625
  %627 = load i32, i32* %35, align 4
  %628 = add i32 %627, 1
  store i32 %628, i32* %35, align 4
  %629 = load i32, i32* %8, align 4
  %630 = icmp ult i32 %627, %629
  br i1 %630, label %631, label %633

631:                                              ; preds = %626
  %632 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %632, i8 noundef signext 32)
  br label %626, !llvm.loop !15

633:                                              ; preds = %626
  br label %634

634:                                              ; preds = %633, %621
  br label %635

635:                                              ; preds = %634, %557
  %636 = load i8*, i8** %5, align 8
  %637 = getelementptr inbounds i8, i8* %636, i32 1
  store i8* %637, i8** %5, align 8
  br label %725

638:                                              ; preds = %249
  store i32 18, i32* %8, align 4
  %639 = load i32, i32* %7, align 4
  %640 = or i32 %639, 8193
  store i32 %640, i32* %7, align 4
  %641 = va_arg i8** %6, i8*
  store i8* %641, i8** %37, align 8
  %642 = load i8*, i8** %37, align 8
  %643 = ptrtoint i8* %642 to i64
  store i64 %643, i64* %36, align 8
  %644 = load i64, i64* %36, align 8
  %645 = icmp eq i64 %644, 0
  br i1 %645, label %646, label %650

646:                                              ; preds = %638
  %647 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %648 = load i32, i32* %8, align 4
  %649 = load i32, i32* %7, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %647, i8* noundef getelementptr inbounds ([6 x i8], [6 x i8]* @.str.1, i64 0, i64 0), i32 noundef 5, i32 noundef %648, i32 noundef %649)
  br label %656

650:                                              ; preds = %638
  %651 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %652 = load i64, i64* %36, align 8
  %653 = load i32, i32* %11, align 4
  %654 = load i32, i32* %8, align 4
  %655 = load i32, i32* %7, align 4
  call void @print_integer(%struct.output_gadget_t* noundef %651, i64 noundef %652, i1 noundef zeroext false, i8 noundef zeroext 16, i32 noundef %653, i32 noundef %654, i32 noundef %655)
  br label %656

656:                                              ; preds = %650, %646
  %657 = load i8*, i8** %5, align 8
  %658 = getelementptr inbounds i8, i8* %657, i32 1
  store i8* %658, i8** %5, align 8
  br label %725

659:                                              ; preds = %249
  %660 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %660, i8 noundef signext 37)
  %661 = load i8*, i8** %5, align 8
  %662 = getelementptr inbounds i8, i8* %661, i32 1
  store i8* %662, i8** %5, align 8
  br label %725

663:                                              ; preds = %249
  %664 = load i32, i32* %7, align 4
  %665 = and i32 %664, 64
  %666 = icmp ne i32 %665, 0
  br i1 %666, label %667, label %674

667:                                              ; preds = %663
  %668 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %669 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %668, i32 0, i32 3
  %670 = load i32, i32* %669, align 8
  %671 = trunc i32 %670 to i8
  %672 = va_arg i8** %6, i8*
  store i8* %672, i8** %38, align 8
  %673 = load i8*, i8** %38, align 8
  store i8 %671, i8* %673, align 1
  br label %716

674:                                              ; preds = %663
  %675 = load i32, i32* %7, align 4
  %676 = and i32 %675, 128
  %677 = icmp ne i32 %676, 0
  br i1 %677, label %678, label %685

678:                                              ; preds = %674
  %679 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %680 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %679, i32 0, i32 3
  %681 = load i32, i32* %680, align 8
  %682 = trunc i32 %681 to i16
  %683 = va_arg i8** %6, i16*
  store i16* %683, i16** %39, align 8
  %684 = load i16*, i16** %39, align 8
  store i16 %682, i16* %684, align 2
  br label %715

685:                                              ; preds = %674
  %686 = load i32, i32* %7, align 4
  %687 = and i32 %686, 512
  %688 = icmp ne i32 %687, 0
  br i1 %688, label %689, label %696

689:                                              ; preds = %685
  %690 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %691 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %690, i32 0, i32 3
  %692 = load i32, i32* %691, align 8
  %693 = zext i32 %692 to i64
  %694 = va_arg i8** %6, i64*
  store i64* %694, i64** %40, align 8
  %695 = load i64*, i64** %40, align 8
  store i64 %693, i64* %695, align 8
  br label %714

696:                                              ; preds = %685
  %697 = load i32, i32* %7, align 4
  %698 = and i32 %697, 1024
  %699 = icmp ne i32 %698, 0
  br i1 %699, label %700, label %707

700:                                              ; preds = %696
  %701 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %702 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %701, i32 0, i32 3
  %703 = load i32, i32* %702, align 8
  %704 = zext i32 %703 to i64
  %705 = va_arg i8** %6, i64*
  store i64* %705, i64** %41, align 8
  %706 = load i64*, i64** %41, align 8
  store i64 %704, i64* %706, align 8
  br label %713

707:                                              ; preds = %696
  %708 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %709 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %708, i32 0, i32 3
  %710 = load i32, i32* %709, align 8
  %711 = va_arg i8** %6, i32*
  store i32* %711, i32** %42, align 8
  %712 = load i32*, i32** %42, align 8
  store i32 %710, i32* %712, align 4
  br label %713

713:                                              ; preds = %707, %700
  br label %714

714:                                              ; preds = %713, %689
  br label %715

715:                                              ; preds = %714, %678
  br label %716

716:                                              ; preds = %715, %667
  %717 = load i8*, i8** %5, align 8
  %718 = getelementptr inbounds i8, i8* %717, i32 1
  store i8* %718, i8** %5, align 8
  br label %725

719:                                              ; preds = %249
  %720 = load %struct.output_gadget_t*, %struct.output_gadget_t** %4, align 8
  %721 = load i8*, i8** %5, align 8
  %722 = load i8, i8* %721, align 1
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %720, i8 noundef signext %722)
  %723 = load i8*, i8** %5, align 8
  %724 = getelementptr inbounds i8, i8* %723, i32 1
  store i8* %724, i8** %5, align 8
  br label %725

725:                                              ; preds = %719, %716, %659, %656, %635, %549, %510, %475, %466
  br label %43, !llvm.loop !9

726:                                              ; preds = %65, %98, %116, %145, %163, %179, %192, %208, %221, %233, %245, %43
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @append_termination_with_gadget(%struct.output_gadget_t* noundef %0) #0 {
  %2 = alloca %struct.output_gadget_t*, align 8
  %3 = alloca i32, align 4
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %2, align 8
  %4 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %5 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %4, i32 0, i32 0
  %6 = load void (i8, i8*)*, void (i8, i8*)** %5, align 8
  %7 = icmp ne void (i8, i8*)* %6, null
  br i1 %7, label %13, label %8

8:                                                ; preds = %1
  %9 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %10 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %9, i32 0, i32 4
  %11 = load i32, i32* %10, align 4
  %12 = icmp eq i32 %11, 0
  br i1 %12, label %13, label %14

13:                                               ; preds = %8, %1
  br label %45

14:                                               ; preds = %8
  %15 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %16 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %15, i32 0, i32 2
  %17 = load i8*, i8** %16, align 8
  %18 = icmp eq i8* %17, null
  br i1 %18, label %19, label %20

19:                                               ; preds = %14
  br label %45

20:                                               ; preds = %14
  %21 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %22 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %21, i32 0, i32 3
  %23 = load i32, i32* %22, align 8
  %24 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %25 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %24, i32 0, i32 4
  %26 = load i32, i32* %25, align 4
  %27 = icmp ult i32 %23, %26
  br i1 %27, label %28, label %32

28:                                               ; preds = %20
  %29 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %30 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %29, i32 0, i32 3
  %31 = load i32, i32* %30, align 8
  br label %37

32:                                               ; preds = %20
  %33 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %34 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %33, i32 0, i32 4
  %35 = load i32, i32* %34, align 4
  %36 = sub i32 %35, 1
  br label %37

37:                                               ; preds = %32, %28
  %38 = phi i32 [ %31, %28 ], [ %36, %32 ]
  store i32 %38, i32* %3, align 4
  %39 = load %struct.output_gadget_t*, %struct.output_gadget_t** %2, align 8
  %40 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %39, i32 0, i32 2
  %41 = load i8*, i8** %40, align 8
  %42 = load i32, i32* %3, align 4
  %43 = zext i32 %42 to i64
  %44 = getelementptr inbounds i8, i8* %41, i64 %43
  store i8 0, i8* %44, align 1
  br label %45

45:                                               ; preds = %37, %19, %13
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @putchar_via_gadget(%struct.output_gadget_t* noundef %0, i8 noundef signext %1) #0 {
  %3 = alloca %struct.output_gadget_t*, align 8
  %4 = alloca i8, align 1
  %5 = alloca i32, align 4
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %3, align 8
  store i8 %1, i8* %4, align 1
  %6 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %7 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %6, i32 0, i32 3
  %8 = load i32, i32* %7, align 8
  %9 = add i32 %8, 1
  store i32 %9, i32* %7, align 8
  store i32 %8, i32* %5, align 4
  %10 = load i32, i32* %5, align 4
  %11 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %12 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %11, i32 0, i32 4
  %13 = load i32, i32* %12, align 4
  %14 = icmp uge i32 %10, %13
  br i1 %14, label %15, label %16

15:                                               ; preds = %2
  br label %37

16:                                               ; preds = %2
  %17 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %18 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %17, i32 0, i32 0
  %19 = load void (i8, i8*)*, void (i8, i8*)** %18, align 8
  %20 = icmp ne void (i8, i8*)* %19, null
  br i1 %20, label %21, label %29

21:                                               ; preds = %16
  %22 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %23 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %22, i32 0, i32 0
  %24 = load void (i8, i8*)*, void (i8, i8*)** %23, align 8
  %25 = load i8, i8* %4, align 1
  %26 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %27 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %26, i32 0, i32 1
  %28 = load i8*, i8** %27, align 8
  call void %24(i8 noundef signext %25, i8* noundef %28)
  br label %37

29:                                               ; preds = %16
  %30 = load i8, i8* %4, align 1
  %31 = load %struct.output_gadget_t*, %struct.output_gadget_t** %3, align 8
  %32 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %31, i32 0, i32 2
  %33 = load i8*, i8** %32, align 8
  %34 = load i32, i32* %5, align 4
  %35 = zext i32 %34 to i64
  %36 = getelementptr inbounds i8, i8* %33, i64 %35
  store i8 %30, i8* %36, align 1
  br label %37

37:                                               ; preds = %15, %29, %21
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @parse_flags(i8** noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i8**, align 8
  %4 = alloca i32, align 4
  store i8** %0, i8*** %3, align 8
  store i32 0, i32* %4, align 4
  br label %5

5:                                                ; preds = %43, %1
  %6 = load i8**, i8*** %3, align 8
  %7 = load i8*, i8** %6, align 8
  %8 = load i8, i8* %7, align 1
  %9 = sext i8 %8 to i32
  switch i32 %9, label %40 [
    i32 48, label %10
    i32 45, label %16
    i32 43, label %22
    i32 32, label %28
    i32 35, label %34
  ]

10:                                               ; preds = %5
  %11 = load i32, i32* %4, align 4
  %12 = or i32 %11, 1
  store i32 %12, i32* %4, align 4
  %13 = load i8**, i8*** %3, align 8
  %14 = load i8*, i8** %13, align 8
  %15 = getelementptr inbounds i8, i8* %14, i32 1
  store i8* %15, i8** %13, align 8
  br label %42

16:                                               ; preds = %5
  %17 = load i32, i32* %4, align 4
  %18 = or i32 %17, 2
  store i32 %18, i32* %4, align 4
  %19 = load i8**, i8*** %3, align 8
  %20 = load i8*, i8** %19, align 8
  %21 = getelementptr inbounds i8, i8* %20, i32 1
  store i8* %21, i8** %19, align 8
  br label %42

22:                                               ; preds = %5
  %23 = load i32, i32* %4, align 4
  %24 = or i32 %23, 4
  store i32 %24, i32* %4, align 4
  %25 = load i8**, i8*** %3, align 8
  %26 = load i8*, i8** %25, align 8
  %27 = getelementptr inbounds i8, i8* %26, i32 1
  store i8* %27, i8** %25, align 8
  br label %42

28:                                               ; preds = %5
  %29 = load i32, i32* %4, align 4
  %30 = or i32 %29, 8
  store i32 %30, i32* %4, align 4
  %31 = load i8**, i8*** %3, align 8
  %32 = load i8*, i8** %31, align 8
  %33 = getelementptr inbounds i8, i8* %32, i32 1
  store i8* %33, i8** %31, align 8
  br label %42

34:                                               ; preds = %5
  %35 = load i32, i32* %4, align 4
  %36 = or i32 %35, 16
  store i32 %36, i32* %4, align 4
  %37 = load i8**, i8*** %3, align 8
  %38 = load i8*, i8** %37, align 8
  %39 = getelementptr inbounds i8, i8* %38, i32 1
  store i8* %39, i8** %37, align 8
  br label %42

40:                                               ; preds = %5
  %41 = load i32, i32* %4, align 4
  store i32 %41, i32* %2, align 4
  br label %44

42:                                               ; preds = %34, %28, %22, %16, %10
  br label %43

43:                                               ; preds = %42
  br i1 true, label %5, label %44

44:                                               ; preds = %40, %43
  %45 = load i32, i32* %2, align 4
  ret i32 %45
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal zeroext i1 @is_digit_(i8 noundef signext %0) #0 {
  %2 = alloca i8, align 1
  store i8 %0, i8* %2, align 1
  %3 = load i8, i8* %2, align 1
  %4 = sext i8 %3 to i32
  %5 = icmp sge i32 %4, 48
  br i1 %5, label %6, label %10

6:                                                ; preds = %1
  %7 = load i8, i8* %2, align 1
  %8 = sext i8 %7 to i32
  %9 = icmp sle i32 %8, 57
  br label %10

10:                                               ; preds = %6, %1
  %11 = phi i1 [ false, %1 ], [ %9, %6 ]
  ret i1 %11
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @atou_(i8** noundef %0) #0 {
  %2 = alloca i8**, align 8
  %3 = alloca i32, align 4
  store i8** %0, i8*** %2, align 8
  store i32 0, i32* %3, align 4
  br label %4

4:                                                ; preds = %9, %1
  %5 = load i8**, i8*** %2, align 8
  %6 = load i8*, i8** %5, align 8
  %7 = load i8, i8* %6, align 1
  %8 = call zeroext i1 @is_digit_(i8 noundef signext %7)
  br i1 %8, label %9, label %19

9:                                                ; preds = %4
  %10 = load i32, i32* %3, align 4
  %11 = mul i32 %10, 10
  %12 = load i8**, i8*** %2, align 8
  %13 = load i8*, i8** %12, align 8
  %14 = getelementptr inbounds i8, i8* %13, i32 1
  store i8* %14, i8** %12, align 8
  %15 = load i8, i8* %13, align 1
  %16 = sext i8 %15 to i32
  %17 = sub nsw i32 %16, 48
  %18 = add i32 %11, %17
  store i32 %18, i32* %3, align 4
  br label %4, !llvm.loop !16

19:                                               ; preds = %4
  %20 = load i32, i32* %3, align 4
  ret i32 %20
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_integer(%struct.output_gadget_t* noundef %0, i64 noundef %1, i1 noundef zeroext %2, i8 noundef zeroext %3, i32 noundef %4, i32 noundef %5, i32 noundef %6) #0 {
  %8 = alloca %struct.output_gadget_t*, align 8
  %9 = alloca i64, align 8
  %10 = alloca i8, align 1
  %11 = alloca i8, align 1
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca [32 x i8], align 1
  %16 = alloca i32, align 4
  %17 = alloca i8, align 1
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %8, align 8
  store i64 %1, i64* %9, align 8
  %18 = zext i1 %2 to i8
  store i8 %18, i8* %10, align 1
  store i8 %3, i8* %11, align 1
  store i32 %4, i32* %12, align 4
  store i32 %5, i32* %13, align 4
  store i32 %6, i32* %14, align 4
  store i32 0, i32* %16, align 4
  %19 = load i64, i64* %9, align 8
  %20 = icmp ne i64 %19, 0
  br i1 %20, label %41, label %21

21:                                               ; preds = %7
  %22 = load i32, i32* %14, align 4
  %23 = and i32 %22, 2048
  %24 = icmp ne i32 %23, 0
  br i1 %24, label %32, label %25

25:                                               ; preds = %21
  %26 = load i32, i32* %16, align 4
  %27 = add i32 %26, 1
  store i32 %27, i32* %16, align 4
  %28 = zext i32 %26 to i64
  %29 = getelementptr inbounds [32 x i8], [32 x i8]* %15, i64 0, i64 %28
  store i8 48, i8* %29, align 1
  %30 = load i32, i32* %14, align 4
  %31 = and i32 %30, -17
  store i32 %31, i32* %14, align 4
  br label %40

32:                                               ; preds = %21
  %33 = load i8, i8* %11, align 1
  %34 = zext i8 %33 to i32
  %35 = icmp eq i32 %34, 16
  br i1 %35, label %36, label %39

36:                                               ; preds = %32
  %37 = load i32, i32* %14, align 4
  %38 = and i32 %37, -17
  store i32 %38, i32* %14, align 4
  br label %39

39:                                               ; preds = %36, %32
  br label %40

40:                                               ; preds = %39, %25
  br label %85

41:                                               ; preds = %7
  br label %42

42:                                               ; preds = %82, %41
  %43 = load i64, i64* %9, align 8
  %44 = load i8, i8* %11, align 1
  %45 = zext i8 %44 to i64
  %46 = urem i64 %43, %45
  %47 = trunc i64 %46 to i8
  store i8 %47, i8* %17, align 1
  %48 = load i8, i8* %17, align 1
  %49 = sext i8 %48 to i32
  %50 = icmp slt i32 %49, 10
  br i1 %50, label %51, label %55

51:                                               ; preds = %42
  %52 = load i8, i8* %17, align 1
  %53 = sext i8 %52 to i32
  %54 = add nsw i32 48, %53
  br label %65

55:                                               ; preds = %42
  %56 = load i32, i32* %14, align 4
  %57 = and i32 %56, 32
  %58 = icmp ne i32 %57, 0
  %59 = zext i1 %58 to i64
  %60 = select i1 %58, i32 65, i32 97
  %61 = load i8, i8* %17, align 1
  %62 = sext i8 %61 to i32
  %63 = add nsw i32 %60, %62
  %64 = sub nsw i32 %63, 10
  br label %65

65:                                               ; preds = %55, %51
  %66 = phi i32 [ %54, %51 ], [ %64, %55 ]
  %67 = trunc i32 %66 to i8
  %68 = load i32, i32* %16, align 4
  %69 = add i32 %68, 1
  store i32 %69, i32* %16, align 4
  %70 = zext i32 %68 to i64
  %71 = getelementptr inbounds [32 x i8], [32 x i8]* %15, i64 0, i64 %70
  store i8 %67, i8* %71, align 1
  %72 = load i8, i8* %11, align 1
  %73 = zext i8 %72 to i64
  %74 = load i64, i64* %9, align 8
  %75 = udiv i64 %74, %73
  store i64 %75, i64* %9, align 8
  br label %76

76:                                               ; preds = %65
  %77 = load i64, i64* %9, align 8
  %78 = icmp ne i64 %77, 0
  br i1 %78, label %79, label %82

79:                                               ; preds = %76
  %80 = load i32, i32* %16, align 4
  %81 = icmp ult i32 %80, 32
  br label %82

82:                                               ; preds = %79, %76
  %83 = phi i1 [ false, %76 ], [ %81, %79 ]
  br i1 %83, label %42, label %84, !llvm.loop !17

84:                                               ; preds = %82
  br label %85

85:                                               ; preds = %84, %40
  %86 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %87 = getelementptr inbounds [32 x i8], [32 x i8]* %15, i64 0, i64 0
  %88 = load i32, i32* %16, align 4
  %89 = load i8, i8* %10, align 1
  %90 = trunc i8 %89 to i1
  %91 = load i8, i8* %11, align 1
  %92 = load i32, i32* %12, align 4
  %93 = load i32, i32* %13, align 4
  %94 = load i32, i32* %14, align 4
  call void @print_integer_finalization(%struct.output_gadget_t* noundef %86, i8* noundef %87, i32 noundef %88, i1 noundef zeroext %90, i8 noundef zeroext %91, i32 noundef %92, i32 noundef %93, i32 noundef %94)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_floating_point(%struct.output_gadget_t* noundef %0, double noundef %1, i32 noundef %2, i32 noundef %3, i32 noundef %4, i1 noundef zeroext %5) #0 {
  %7 = alloca %struct.output_gadget_t*, align 8
  %8 = alloca double, align 8
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i8, align 1
  %13 = alloca [32 x i8], align 1
  %14 = alloca i32, align 4
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %7, align 8
  store double %1, double* %8, align 8
  store i32 %2, i32* %9, align 4
  store i32 %3, i32* %10, align 4
  store i32 %4, i32* %11, align 4
  %15 = zext i1 %5 to i8
  store i8 %15, i8* %12, align 1
  store i32 0, i32* %14, align 4
  %16 = load double, double* %8, align 8
  %17 = load double, double* %8, align 8
  %18 = fcmp une double %16, %17
  br i1 %18, label %19, label %23

19:                                               ; preds = %6
  %20 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %21 = load i32, i32* %10, align 4
  %22 = load i32, i32* %11, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %20, i8* noundef getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2, i64 0, i64 0), i32 noundef 3, i32 noundef %21, i32 noundef %22)
  br label %104

23:                                               ; preds = %6
  %24 = load double, double* %8, align 8
  %25 = fcmp olt double %24, 0xFFEFFFFFFFFFFFFF
  br i1 %25, label %26, label %30

26:                                               ; preds = %23
  %27 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %28 = load i32, i32* %10, align 4
  %29 = load i32, i32* %11, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %27, i8* noundef getelementptr inbounds ([5 x i8], [5 x i8]* @.str.3, i64 0, i64 0), i32 noundef 4, i32 noundef %28, i32 noundef %29)
  br label %104

30:                                               ; preds = %23
  %31 = load double, double* %8, align 8
  %32 = fcmp ogt double %31, 0x7FEFFFFFFFFFFFFF
  br i1 %32, label %33, label %47

33:                                               ; preds = %30
  %34 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %35 = load i32, i32* %11, align 4
  %36 = and i32 %35, 4
  %37 = icmp ne i32 %36, 0
  %38 = zext i1 %37 to i64
  %39 = select i1 %37, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.4, i64 0, i64 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.5, i64 0, i64 0)
  %40 = load i32, i32* %11, align 4
  %41 = and i32 %40, 4
  %42 = icmp ne i32 %41, 0
  %43 = zext i1 %42 to i64
  %44 = select i1 %42, i32 4, i32 3
  %45 = load i32, i32* %10, align 4
  %46 = load i32, i32* %11, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %34, i8* noundef %39, i32 noundef %44, i32 noundef %45, i32 noundef %46)
  br label %104

47:                                               ; preds = %30
  %48 = load i8, i8* %12, align 1
  %49 = trunc i8 %48 to i1
  br i1 %49, label %64, label %50

50:                                               ; preds = %47
  %51 = load double, double* %8, align 8
  %52 = fcmp ogt double %51, 1.000000e+09
  br i1 %52, label %56, label %53

53:                                               ; preds = %50
  %54 = load double, double* %8, align 8
  %55 = fcmp olt double %54, -1.000000e+09
  br i1 %55, label %56, label %64

56:                                               ; preds = %53, %50
  %57 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %58 = load double, double* %8, align 8
  %59 = load i32, i32* %9, align 4
  %60 = load i32, i32* %10, align 4
  %61 = load i32, i32* %11, align 4
  %62 = getelementptr inbounds [32 x i8], [32 x i8]* %13, i64 0, i64 0
  %63 = load i32, i32* %14, align 4
  call void @print_exponential_number(%struct.output_gadget_t* noundef %57, double noundef %58, i32 noundef %59, i32 noundef %60, i32 noundef %61, i8* noundef %62, i32 noundef %63)
  br label %104

64:                                               ; preds = %53, %47
  %65 = load i32, i32* %11, align 4
  %66 = and i32 %65, 2048
  %67 = icmp ne i32 %66, 0
  br i1 %67, label %69, label %68

68:                                               ; preds = %64
  store i32 6, i32* %9, align 4
  br label %69

69:                                               ; preds = %68, %64
  br label %70

70:                                               ; preds = %78, %69
  %71 = load i32, i32* %14, align 4
  %72 = icmp ult i32 %71, 32
  br i1 %72, label %73, label %76

73:                                               ; preds = %70
  %74 = load i32, i32* %9, align 4
  %75 = icmp ugt i32 %74, 17
  br label %76

76:                                               ; preds = %73, %70
  %77 = phi i1 [ false, %70 ], [ %75, %73 ]
  br i1 %77, label %78, label %85

78:                                               ; preds = %76
  %79 = load i32, i32* %14, align 4
  %80 = add i32 %79, 1
  store i32 %80, i32* %14, align 4
  %81 = zext i32 %79 to i64
  %82 = getelementptr inbounds [32 x i8], [32 x i8]* %13, i64 0, i64 %81
  store i8 48, i8* %82, align 1
  %83 = load i32, i32* %9, align 4
  %84 = add i32 %83, -1
  store i32 %84, i32* %9, align 4
  br label %70, !llvm.loop !18

85:                                               ; preds = %76
  %86 = load i8, i8* %12, align 1
  %87 = trunc i8 %86 to i1
  br i1 %87, label %88, label %96

88:                                               ; preds = %85
  %89 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %90 = load double, double* %8, align 8
  %91 = load i32, i32* %9, align 4
  %92 = load i32, i32* %10, align 4
  %93 = load i32, i32* %11, align 4
  %94 = getelementptr inbounds [32 x i8], [32 x i8]* %13, i64 0, i64 0
  %95 = load i32, i32* %14, align 4
  call void @print_exponential_number(%struct.output_gadget_t* noundef %89, double noundef %90, i32 noundef %91, i32 noundef %92, i32 noundef %93, i8* noundef %94, i32 noundef %95)
  br label %104

96:                                               ; preds = %85
  %97 = load %struct.output_gadget_t*, %struct.output_gadget_t** %7, align 8
  %98 = load double, double* %8, align 8
  %99 = load i32, i32* %9, align 4
  %100 = load i32, i32* %10, align 4
  %101 = load i32, i32* %11, align 4
  %102 = getelementptr inbounds [32 x i8], [32 x i8]* %13, i64 0, i64 0
  %103 = load i32, i32* %14, align 4
  call void @print_decimal_number(%struct.output_gadget_t* noundef %97, double noundef %98, i32 noundef %99, i32 noundef %100, i32 noundef %101, i8* noundef %102, i32 noundef %103)
  br label %104

104:                                              ; preds = %19, %26, %33, %56, %96, %88
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @out_rev_(%struct.output_gadget_t* noundef %0, i8* noundef %1, i32 noundef %2, i32 noundef %3, i32 noundef %4) #0 {
  %6 = alloca %struct.output_gadget_t*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %6, align 8
  store i8* %1, i8** %7, align 8
  store i32 %2, i32* %8, align 4
  store i32 %3, i32* %9, align 4
  store i32 %4, i32* %10, align 4
  %13 = load %struct.output_gadget_t*, %struct.output_gadget_t** %6, align 8
  %14 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %13, i32 0, i32 3
  %15 = load i32, i32* %14, align 8
  store i32 %15, i32* %11, align 4
  %16 = load i32, i32* %10, align 4
  %17 = and i32 %16, 2
  %18 = icmp ne i32 %17, 0
  br i1 %18, label %35, label %19

19:                                               ; preds = %5
  %20 = load i32, i32* %10, align 4
  %21 = and i32 %20, 1
  %22 = icmp ne i32 %21, 0
  br i1 %22, label %35, label %23

23:                                               ; preds = %19
  %24 = load i32, i32* %8, align 4
  store i32 %24, i32* %12, align 4
  br label %25

25:                                               ; preds = %31, %23
  %26 = load i32, i32* %12, align 4
  %27 = load i32, i32* %9, align 4
  %28 = icmp ult i32 %26, %27
  br i1 %28, label %29, label %34

29:                                               ; preds = %25
  %30 = load %struct.output_gadget_t*, %struct.output_gadget_t** %6, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %30, i8 noundef signext 32)
  br label %31

31:                                               ; preds = %29
  %32 = load i32, i32* %12, align 4
  %33 = add i32 %32, 1
  store i32 %33, i32* %12, align 4
  br label %25, !llvm.loop !19

34:                                               ; preds = %25
  br label %35

35:                                               ; preds = %34, %19, %5
  br label %36

36:                                               ; preds = %39, %35
  %37 = load i32, i32* %8, align 4
  %38 = icmp ne i32 %37, 0
  br i1 %38, label %39, label %47

39:                                               ; preds = %36
  %40 = load %struct.output_gadget_t*, %struct.output_gadget_t** %6, align 8
  %41 = load i8*, i8** %7, align 8
  %42 = load i32, i32* %8, align 4
  %43 = add i32 %42, -1
  store i32 %43, i32* %8, align 4
  %44 = zext i32 %43 to i64
  %45 = getelementptr inbounds i8, i8* %41, i64 %44
  %46 = load i8, i8* %45, align 1
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %40, i8 noundef signext %46)
  br label %36, !llvm.loop !20

47:                                               ; preds = %36
  %48 = load i32, i32* %10, align 4
  %49 = and i32 %48, 2
  %50 = icmp ne i32 %49, 0
  br i1 %50, label %51, label %63

51:                                               ; preds = %47
  br label %52

52:                                               ; preds = %60, %51
  %53 = load %struct.output_gadget_t*, %struct.output_gadget_t** %6, align 8
  %54 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %53, i32 0, i32 3
  %55 = load i32, i32* %54, align 8
  %56 = load i32, i32* %11, align 4
  %57 = sub i32 %55, %56
  %58 = load i32, i32* %9, align 4
  %59 = icmp ult i32 %57, %58
  br i1 %59, label %60, label %62

60:                                               ; preds = %52
  %61 = load %struct.output_gadget_t*, %struct.output_gadget_t** %6, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %61, i8 noundef signext 32)
  br label %52, !llvm.loop !21

62:                                               ; preds = %52
  br label %63

63:                                               ; preds = %62, %47
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @strnlen_s_(i8* noundef %0, i32 noundef %1) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i32, align 4
  %5 = alloca i8*, align 8
  store i8* %0, i8** %3, align 8
  store i32 %1, i32* %4, align 4
  %6 = load i8*, i8** %3, align 8
  store i8* %6, i8** %5, align 8
  br label %7

7:                                                ; preds = %19, %2
  %8 = load i8*, i8** %5, align 8
  %9 = load i8, i8* %8, align 1
  %10 = sext i8 %9 to i32
  %11 = icmp ne i32 %10, 0
  br i1 %11, label %12, label %16

12:                                               ; preds = %7
  %13 = load i32, i32* %4, align 4
  %14 = add i32 %13, -1
  store i32 %14, i32* %4, align 4
  %15 = icmp ne i32 %13, 0
  br label %16

16:                                               ; preds = %12, %7
  %17 = phi i1 [ false, %7 ], [ %15, %12 ]
  br i1 %17, label %18, label %22

18:                                               ; preds = %16
  br label %19

19:                                               ; preds = %18
  %20 = load i8*, i8** %5, align 8
  %21 = getelementptr inbounds i8, i8* %20, i32 1
  store i8* %21, i8** %5, align 8
  br label %7, !llvm.loop !22

22:                                               ; preds = %16
  %23 = load i8*, i8** %5, align 8
  %24 = load i8*, i8** %3, align 8
  %25 = ptrtoint i8* %23 to i64
  %26 = ptrtoint i8* %24 to i64
  %27 = sub i64 %25, %26
  %28 = trunc i64 %27 to i32
  ret i32 %28
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_integer_finalization(%struct.output_gadget_t* noundef %0, i8* noundef %1, i32 noundef %2, i1 noundef zeroext %3, i8 noundef zeroext %4, i32 noundef %5, i32 noundef %6, i32 noundef %7) #0 {
  %9 = alloca %struct.output_gadget_t*, align 8
  %10 = alloca i8*, align 8
  %11 = alloca i32, align 4
  %12 = alloca i8, align 1
  %13 = alloca i8, align 1
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %9, align 8
  store i8* %1, i8** %10, align 8
  store i32 %2, i32* %11, align 4
  %18 = zext i1 %3 to i8
  store i8 %18, i8* %12, align 1
  store i8 %4, i8* %13, align 1
  store i32 %5, i32* %14, align 4
  store i32 %6, i32* %15, align 4
  store i32 %7, i32* %16, align 4
  %19 = load i32, i32* %11, align 4
  store i32 %19, i32* %17, align 4
  %20 = load i32, i32* %16, align 4
  %21 = and i32 %20, 2
  %22 = icmp ne i32 %21, 0
  br i1 %22, label %61, label %23

23:                                               ; preds = %8
  %24 = load i32, i32* %15, align 4
  %25 = icmp ne i32 %24, 0
  br i1 %25, label %26, label %40

26:                                               ; preds = %23
  %27 = load i32, i32* %16, align 4
  %28 = and i32 %27, 1
  %29 = icmp ne i32 %28, 0
  br i1 %29, label %30, label %40

30:                                               ; preds = %26
  %31 = load i8, i8* %12, align 1
  %32 = trunc i8 %31 to i1
  br i1 %32, label %37, label %33

33:                                               ; preds = %30
  %34 = load i32, i32* %16, align 4
  %35 = and i32 %34, 12
  %36 = icmp ne i32 %35, 0
  br i1 %36, label %37, label %40

37:                                               ; preds = %33, %30
  %38 = load i32, i32* %15, align 4
  %39 = add i32 %38, -1
  store i32 %39, i32* %15, align 4
  br label %40

40:                                               ; preds = %37, %33, %26, %23
  br label %41

41:                                               ; preds = %54, %40
  %42 = load i32, i32* %16, align 4
  %43 = and i32 %42, 1
  %44 = icmp ne i32 %43, 0
  br i1 %44, label %45, label %52

45:                                               ; preds = %41
  %46 = load i32, i32* %11, align 4
  %47 = load i32, i32* %15, align 4
  %48 = icmp ult i32 %46, %47
  br i1 %48, label %49, label %52

49:                                               ; preds = %45
  %50 = load i32, i32* %11, align 4
  %51 = icmp ult i32 %50, 32
  br label %52

52:                                               ; preds = %49, %45, %41
  %53 = phi i1 [ false, %45 ], [ false, %41 ], [ %51, %49 ]
  br i1 %53, label %54, label %60

54:                                               ; preds = %52
  %55 = load i8*, i8** %10, align 8
  %56 = load i32, i32* %11, align 4
  %57 = add i32 %56, 1
  store i32 %57, i32* %11, align 4
  %58 = zext i32 %56 to i64
  %59 = getelementptr inbounds i8, i8* %55, i64 %58
  store i8 48, i8* %59, align 1
  br label %41, !llvm.loop !23

60:                                               ; preds = %52
  br label %61

61:                                               ; preds = %60, %8
  br label %62

62:                                               ; preds = %71, %61
  %63 = load i32, i32* %11, align 4
  %64 = load i32, i32* %14, align 4
  %65 = icmp ult i32 %63, %64
  br i1 %65, label %66, label %69

66:                                               ; preds = %62
  %67 = load i32, i32* %11, align 4
  %68 = icmp ult i32 %67, 32
  br label %69

69:                                               ; preds = %66, %62
  %70 = phi i1 [ false, %62 ], [ %68, %66 ]
  br i1 %70, label %71, label %77

71:                                               ; preds = %69
  %72 = load i8*, i8** %10, align 8
  %73 = load i32, i32* %11, align 4
  %74 = add i32 %73, 1
  store i32 %74, i32* %11, align 4
  %75 = zext i32 %73 to i64
  %76 = getelementptr inbounds i8, i8* %72, i64 %75
  store i8 48, i8* %76, align 1
  br label %62, !llvm.loop !24

77:                                               ; preds = %69
  %78 = load i8, i8* %13, align 1
  %79 = zext i8 %78 to i32
  %80 = icmp eq i32 %79, 8
  br i1 %80, label %81, label %88

81:                                               ; preds = %77
  %82 = load i32, i32* %11, align 4
  %83 = load i32, i32* %17, align 4
  %84 = icmp ugt i32 %82, %83
  br i1 %84, label %85, label %88

85:                                               ; preds = %81
  %86 = load i32, i32* %16, align 4
  %87 = and i32 %86, -17
  store i32 %87, i32* %16, align 4
  br label %88

88:                                               ; preds = %85, %81, %77
  %89 = load i32, i32* %16, align 4
  %90 = and i32 %89, 8208
  %91 = icmp ne i32 %90, 0
  br i1 %91, label %92, label %192

92:                                               ; preds = %88
  %93 = load i32, i32* %16, align 4
  %94 = and i32 %93, 2048
  %95 = icmp ne i32 %94, 0
  br i1 %95, label %133, label %96

96:                                               ; preds = %92
  %97 = load i32, i32* %11, align 4
  %98 = icmp ne i32 %97, 0
  br i1 %98, label %99, label %133

99:                                               ; preds = %96
  %100 = load i32, i32* %11, align 4
  %101 = load i32, i32* %14, align 4
  %102 = icmp eq i32 %100, %101
  br i1 %102, label %107, label %103

103:                                              ; preds = %99
  %104 = load i32, i32* %11, align 4
  %105 = load i32, i32* %15, align 4
  %106 = icmp eq i32 %104, %105
  br i1 %106, label %107, label %133

107:                                              ; preds = %103, %99
  %108 = load i32, i32* %17, align 4
  %109 = load i32, i32* %11, align 4
  %110 = icmp ult i32 %108, %109
  br i1 %110, label %111, label %114

111:                                              ; preds = %107
  %112 = load i32, i32* %11, align 4
  %113 = add i32 %112, -1
  store i32 %113, i32* %11, align 4
  br label %114

114:                                              ; preds = %111, %107
  %115 = load i32, i32* %11, align 4
  %116 = icmp ne i32 %115, 0
  br i1 %116, label %117, label %132

117:                                              ; preds = %114
  %118 = load i8, i8* %13, align 1
  %119 = zext i8 %118 to i32
  %120 = icmp eq i32 %119, 16
  br i1 %120, label %125, label %121

121:                                              ; preds = %117
  %122 = load i8, i8* %13, align 1
  %123 = zext i8 %122 to i32
  %124 = icmp eq i32 %123, 2
  br i1 %124, label %125, label %132

125:                                              ; preds = %121, %117
  %126 = load i32, i32* %17, align 4
  %127 = load i32, i32* %11, align 4
  %128 = icmp ult i32 %126, %127
  br i1 %128, label %129, label %132

129:                                              ; preds = %125
  %130 = load i32, i32* %11, align 4
  %131 = add i32 %130, -1
  store i32 %131, i32* %11, align 4
  br label %132

132:                                              ; preds = %129, %125, %121, %114
  br label %133

133:                                              ; preds = %132, %103, %96, %92
  %134 = load i8, i8* %13, align 1
  %135 = zext i8 %134 to i32
  %136 = icmp eq i32 %135, 16
  br i1 %136, label %137, label %150

137:                                              ; preds = %133
  %138 = load i32, i32* %16, align 4
  %139 = and i32 %138, 32
  %140 = icmp ne i32 %139, 0
  br i1 %140, label %150, label %141

141:                                              ; preds = %137
  %142 = load i32, i32* %11, align 4
  %143 = icmp ult i32 %142, 32
  br i1 %143, label %144, label %150

144:                                              ; preds = %141
  %145 = load i8*, i8** %10, align 8
  %146 = load i32, i32* %11, align 4
  %147 = add i32 %146, 1
  store i32 %147, i32* %11, align 4
  %148 = zext i32 %146 to i64
  %149 = getelementptr inbounds i8, i8* %145, i64 %148
  store i8 120, i8* %149, align 1
  br label %182

150:                                              ; preds = %141, %137, %133
  %151 = load i8, i8* %13, align 1
  %152 = zext i8 %151 to i32
  %153 = icmp eq i32 %152, 16
  br i1 %153, label %154, label %167

154:                                              ; preds = %150
  %155 = load i32, i32* %16, align 4
  %156 = and i32 %155, 32
  %157 = icmp ne i32 %156, 0
  br i1 %157, label %158, label %167

158:                                              ; preds = %154
  %159 = load i32, i32* %11, align 4
  %160 = icmp ult i32 %159, 32
  br i1 %160, label %161, label %167

161:                                              ; preds = %158
  %162 = load i8*, i8** %10, align 8
  %163 = load i32, i32* %11, align 4
  %164 = add i32 %163, 1
  store i32 %164, i32* %11, align 4
  %165 = zext i32 %163 to i64
  %166 = getelementptr inbounds i8, i8* %162, i64 %165
  store i8 88, i8* %166, align 1
  br label %181

167:                                              ; preds = %158, %154, %150
  %168 = load i8, i8* %13, align 1
  %169 = zext i8 %168 to i32
  %170 = icmp eq i32 %169, 2
  br i1 %170, label %171, label %180

171:                                              ; preds = %167
  %172 = load i32, i32* %11, align 4
  %173 = icmp ult i32 %172, 32
  br i1 %173, label %174, label %180

174:                                              ; preds = %171
  %175 = load i8*, i8** %10, align 8
  %176 = load i32, i32* %11, align 4
  %177 = add i32 %176, 1
  store i32 %177, i32* %11, align 4
  %178 = zext i32 %176 to i64
  %179 = getelementptr inbounds i8, i8* %175, i64 %178
  store i8 98, i8* %179, align 1
  br label %180

180:                                              ; preds = %174, %171, %167
  br label %181

181:                                              ; preds = %180, %161
  br label %182

182:                                              ; preds = %181, %144
  %183 = load i32, i32* %11, align 4
  %184 = icmp ult i32 %183, 32
  br i1 %184, label %185, label %191

185:                                              ; preds = %182
  %186 = load i8*, i8** %10, align 8
  %187 = load i32, i32* %11, align 4
  %188 = add i32 %187, 1
  store i32 %188, i32* %11, align 4
  %189 = zext i32 %187 to i64
  %190 = getelementptr inbounds i8, i8* %186, i64 %189
  store i8 48, i8* %190, align 1
  br label %191

191:                                              ; preds = %185, %182
  br label %192

192:                                              ; preds = %191, %88
  %193 = load i32, i32* %11, align 4
  %194 = icmp ult i32 %193, 32
  br i1 %194, label %195, label %227

195:                                              ; preds = %192
  %196 = load i8, i8* %12, align 1
  %197 = trunc i8 %196 to i1
  br i1 %197, label %198, label %204

198:                                              ; preds = %195
  %199 = load i8*, i8** %10, align 8
  %200 = load i32, i32* %11, align 4
  %201 = add i32 %200, 1
  store i32 %201, i32* %11, align 4
  %202 = zext i32 %200 to i64
  %203 = getelementptr inbounds i8, i8* %199, i64 %202
  store i8 45, i8* %203, align 1
  br label %226

204:                                              ; preds = %195
  %205 = load i32, i32* %16, align 4
  %206 = and i32 %205, 4
  %207 = icmp ne i32 %206, 0
  br i1 %207, label %208, label %214

208:                                              ; preds = %204
  %209 = load i8*, i8** %10, align 8
  %210 = load i32, i32* %11, align 4
  %211 = add i32 %210, 1
  store i32 %211, i32* %11, align 4
  %212 = zext i32 %210 to i64
  %213 = getelementptr inbounds i8, i8* %209, i64 %212
  store i8 43, i8* %213, align 1
  br label %225

214:                                              ; preds = %204
  %215 = load i32, i32* %16, align 4
  %216 = and i32 %215, 8
  %217 = icmp ne i32 %216, 0
  br i1 %217, label %218, label %224

218:                                              ; preds = %214
  %219 = load i8*, i8** %10, align 8
  %220 = load i32, i32* %11, align 4
  %221 = add i32 %220, 1
  store i32 %221, i32* %11, align 4
  %222 = zext i32 %220 to i64
  %223 = getelementptr inbounds i8, i8* %219, i64 %222
  store i8 32, i8* %223, align 1
  br label %224

224:                                              ; preds = %218, %214
  br label %225

225:                                              ; preds = %224, %208
  br label %226

226:                                              ; preds = %225, %198
  br label %227

227:                                              ; preds = %226, %192
  %228 = load %struct.output_gadget_t*, %struct.output_gadget_t** %9, align 8
  %229 = load i8*, i8** %10, align 8
  %230 = load i32, i32* %11, align 4
  %231 = load i32, i32* %15, align 4
  %232 = load i32, i32* %16, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %228, i8* noundef %229, i32 noundef %230, i32 noundef %231, i32 noundef %232)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_exponential_number(%struct.output_gadget_t* noundef %0, double noundef %1, i32 noundef %2, i32 noundef %3, i32 noundef %4, i8* noundef %5, i32 noundef %6) #0 {
  %8 = alloca %struct.output_gadget_t*, align 8
  %9 = alloca double, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i8*, align 8
  %14 = alloca i32, align 4
  %15 = alloca i8, align 1
  %16 = alloca double, align 8
  %17 = alloca i32, align 4
  %18 = alloca i8, align 1
  %19 = alloca %struct.scaling_factor, align 8
  %20 = alloca double, align 8
  %21 = alloca double, align 8
  %22 = alloca i8, align 1
  %23 = alloca i32, align 4
  %24 = alloca i32, align 4
  %25 = alloca i8, align 1
  %26 = alloca %struct.double_components, align 8
  %27 = alloca i32, align 4
  %28 = alloca i32, align 4
  %29 = alloca i32, align 4
  %30 = alloca %struct.double_components, align 8
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %8, align 8
  store double %1, double* %9, align 8
  store i32 %2, i32* %10, align 4
  store i32 %3, i32* %11, align 4
  store i32 %4, i32* %12, align 4
  store i8* %5, i8** %13, align 8
  store i32 %6, i32* %14, align 4
  %31 = load double, double* %9, align 8
  %32 = call i32 @get_sign_bit(double noundef %31)
  %33 = icmp ne i32 %32, 0
  %34 = zext i1 %33 to i8
  store i8 %34, i8* %15, align 1
  %35 = load i8, i8* %15, align 1
  %36 = trunc i8 %35 to i1
  br i1 %36, label %37, label %40

37:                                               ; preds = %7
  %38 = load double, double* %9, align 8
  %39 = fneg double %38
  br label %42

40:                                               ; preds = %7
  %41 = load double, double* %9, align 8
  br label %42

42:                                               ; preds = %40, %37
  %43 = phi double [ %39, %37 ], [ %41, %40 ]
  store double %43, double* %16, align 8
  %44 = load double, double* %16, align 8
  %45 = fcmp oeq double %44, 0.000000e+00
  br i1 %45, label %46, label %47

46:                                               ; preds = %42
  store i32 0, i32* %17, align 4
  br label %94

47:                                               ; preds = %42
  %48 = load double, double* %16, align 8
  %49 = call double @log10_of_positive(double noundef %48)
  store double %49, double* %20, align 8
  %50 = load double, double* %20, align 8
  %51 = call i32 @bastardized_floor(double noundef %50)
  store i32 %51, i32* %17, align 4
  %52 = load i32, i32* %17, align 4
  %53 = call double @pow10_of_int(i32 noundef %52)
  store double %53, double* %21, align 8
  %54 = load double, double* %16, align 8
  %55 = load double, double* %21, align 8
  %56 = fcmp olt double %54, %55
  br i1 %56, label %57, label %62

57:                                               ; preds = %47
  %58 = load i32, i32* %17, align 4
  %59 = add nsw i32 %58, -1
  store i32 %59, i32* %17, align 4
  %60 = load double, double* %21, align 8
  %61 = fdiv double %60, 1.000000e+01
  store double %61, double* %21, align 8
  br label %62

62:                                               ; preds = %57, %47
  %63 = load i32, i32* %17, align 4
  %64 = icmp sgt i32 %63, 0
  br i1 %64, label %65, label %67

65:                                               ; preds = %62
  %66 = load i32, i32* %17, align 4
  br label %70

67:                                               ; preds = %62
  %68 = load i32, i32* %17, align 4
  %69 = sub nsw i32 0, %68
  br label %70

70:                                               ; preds = %67, %65
  %71 = phi i32 [ %66, %65 ], [ %69, %67 ]
  %72 = icmp slt i32 %71, 18
  %73 = zext i1 %72 to i8
  store i8 %73, i8* %18, align 1
  %74 = load i8, i8* %18, align 1
  %75 = trunc i8 %74 to i1
  br i1 %75, label %76, label %89

76:                                               ; preds = %70
  %77 = load i32, i32* %17, align 4
  %78 = icmp sgt i32 %77, 0
  br i1 %78, label %79, label %81

79:                                               ; preds = %76
  %80 = load i32, i32* %17, align 4
  br label %84

81:                                               ; preds = %76
  %82 = load i32, i32* %17, align 4
  %83 = sub nsw i32 0, %82
  br label %84

84:                                               ; preds = %81, %79
  %85 = phi i32 [ %80, %79 ], [ %83, %81 ]
  %86 = sext i32 %85 to i64
  %87 = getelementptr inbounds [18 x double], [18 x double]* @powers_of_10, i64 0, i64 %86
  %88 = load double, double* %87, align 8
  br label %91

89:                                               ; preds = %70
  %90 = load double, double* %21, align 8
  br label %91

91:                                               ; preds = %89, %84
  %92 = phi double [ %88, %84 ], [ %90, %89 ]
  %93 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %19, i32 0, i32 0
  store double %92, double* %93, align 8
  br label %94

94:                                               ; preds = %91, %46
  store i8 0, i8* %22, align 1
  %95 = load i32, i32* %12, align 4
  %96 = and i32 %95, 4096
  %97 = icmp ne i32 %96, 0
  br i1 %97, label %98, label %136

98:                                               ; preds = %94
  %99 = load i32, i32* %10, align 4
  %100 = icmp eq i32 %99, 0
  br i1 %100, label %101, label %102

101:                                              ; preds = %98
  br label %104

102:                                              ; preds = %98
  %103 = load i32, i32* %10, align 4
  br label %104

104:                                              ; preds = %102, %101
  %105 = phi i32 [ 1, %101 ], [ %103, %102 ]
  store i32 %105, i32* %23, align 4
  %106 = load i32, i32* %17, align 4
  %107 = icmp sge i32 %106, -4
  br i1 %107, label %108, label %112

108:                                              ; preds = %104
  %109 = load i32, i32* %17, align 4
  %110 = load i32, i32* %23, align 4
  %111 = icmp slt i32 %109, %110
  br label %112

112:                                              ; preds = %108, %104
  %113 = phi i1 [ false, %104 ], [ %111, %108 ]
  %114 = zext i1 %113 to i8
  store i8 %114, i8* %22, align 1
  %115 = load i8, i8* %22, align 1
  %116 = trunc i8 %115 to i1
  br i1 %116, label %117, label %122

117:                                              ; preds = %112
  %118 = load i32, i32* %10, align 4
  %119 = sub nsw i32 %118, 1
  %120 = load i32, i32* %17, align 4
  %121 = sub nsw i32 %119, %120
  br label %125

122:                                              ; preds = %112
  %123 = load i32, i32* %10, align 4
  %124 = sub nsw i32 %123, 1
  br label %125

125:                                              ; preds = %122, %117
  %126 = phi i32 [ %121, %117 ], [ %124, %122 ]
  store i32 %126, i32* %24, align 4
  %127 = load i32, i32* %24, align 4
  %128 = icmp sgt i32 %127, 0
  br i1 %128, label %129, label %131

129:                                              ; preds = %125
  %130 = load i32, i32* %24, align 4
  br label %132

131:                                              ; preds = %125
  br label %132

132:                                              ; preds = %131, %129
  %133 = phi i32 [ %130, %129 ], [ 0, %131 ]
  store i32 %133, i32* %10, align 4
  %134 = load i32, i32* %12, align 4
  %135 = or i32 %134, 2048
  store i32 %135, i32* %12, align 4
  br label %136

136:                                              ; preds = %132, %94
  %137 = load i32, i32* %17, align 4
  %138 = icmp slt i32 %137, 0
  br i1 %138, label %139, label %142

139:                                              ; preds = %136
  %140 = load i8, i8* %18, align 1
  %141 = trunc i8 %140 to i1
  br label %142

142:                                              ; preds = %139, %136
  %143 = phi i1 [ false, %136 ], [ %141, %139 ]
  %144 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %19, i32 0, i32 1
  %145 = zext i1 %143 to i8
  store i8 %145, i8* %144, align 8
  %146 = load i8, i8* %22, align 1
  %147 = trunc i8 %146 to i1
  br i1 %147, label %151, label %148

148:                                              ; preds = %142
  %149 = load i32, i32* %17, align 4
  %150 = icmp eq i32 %149, 0
  br label %151

151:                                              ; preds = %148, %142
  %152 = phi i1 [ true, %142 ], [ %150, %148 ]
  %153 = zext i1 %152 to i8
  store i8 %153, i8* %25, align 1
  %154 = load i8, i8* %25, align 1
  %155 = trunc i8 %154 to i1
  br i1 %155, label %156, label %167

156:                                              ; preds = %151
  %157 = load i8, i8* %15, align 1
  %158 = trunc i8 %157 to i1
  br i1 %158, label %159, label %162

159:                                              ; preds = %156
  %160 = load double, double* %16, align 8
  %161 = fneg double %160
  br label %164

162:                                              ; preds = %156
  %163 = load double, double* %16, align 8
  br label %164

164:                                              ; preds = %162, %159
  %165 = phi double [ %161, %159 ], [ %163, %162 ]
  %166 = load i32, i32* %10, align 4
  call void @get_components(%struct.double_components* sret(%struct.double_components) align 8 %26, double noundef %165, i32 noundef %166)
  br label %175

167:                                              ; preds = %151
  %168 = load i8, i8* %15, align 1
  %169 = trunc i8 %168 to i1
  %170 = load i32, i32* %10, align 4
  %171 = load double, double* %16, align 8
  %172 = load i32, i32* %17, align 4
  %173 = bitcast %struct.scaling_factor* %19 to [2 x i64]*
  %174 = load [2 x i64], [2 x i64]* %173, align 8
  call void @get_normalized_components(%struct.double_components* sret(%struct.double_components) align 8 %26, i1 noundef zeroext %169, i32 noundef %170, double noundef %171, [2 x i64] %174, i32 noundef %172)
  br label %175

175:                                              ; preds = %167, %164
  %176 = load i8, i8* %22, align 1
  %177 = trunc i8 %176 to i1
  br i1 %177, label %178, label %201

178:                                              ; preds = %175
  %179 = load i32, i32* %12, align 4
  %180 = and i32 %179, 4096
  %181 = icmp ne i32 %180, 0
  br i1 %181, label %182, label %200

182:                                              ; preds = %178
  %183 = load i32, i32* %17, align 4
  %184 = icmp sge i32 %183, -1
  br i1 %184, label %185, label %200

185:                                              ; preds = %182
  %186 = getelementptr inbounds %struct.double_components, %struct.double_components* %26, i32 0, i32 0
  %187 = load i64, i64* %186, align 8
  %188 = sitofp i64 %187 to double
  %189 = load i32, i32* %17, align 4
  %190 = add nsw i32 %189, 1
  %191 = sext i32 %190 to i64
  %192 = getelementptr inbounds [18 x double], [18 x double]* @powers_of_10, i64 0, i64 %191
  %193 = load double, double* %192, align 8
  %194 = fcmp oeq double %188, %193
  br i1 %194, label %195, label %200

195:                                              ; preds = %185
  %196 = load i32, i32* %17, align 4
  %197 = add nsw i32 %196, 1
  store i32 %197, i32* %17, align 4
  %198 = load i32, i32* %10, align 4
  %199 = add i32 %198, -1
  store i32 %199, i32* %10, align 4
  br label %200

200:                                              ; preds = %195, %185, %182, %178
  br label %211

201:                                              ; preds = %175
  %202 = getelementptr inbounds %struct.double_components, %struct.double_components* %26, i32 0, i32 0
  %203 = load i64, i64* %202, align 8
  %204 = icmp sge i64 %203, 10
  br i1 %204, label %205, label %210

205:                                              ; preds = %201
  %206 = load i32, i32* %17, align 4
  %207 = add nsw i32 %206, 1
  store i32 %207, i32* %17, align 4
  %208 = getelementptr inbounds %struct.double_components, %struct.double_components* %26, i32 0, i32 0
  store i64 1, i64* %208, align 8
  %209 = getelementptr inbounds %struct.double_components, %struct.double_components* %26, i32 0, i32 1
  store i64 0, i64* %209, align 8
  br label %210

210:                                              ; preds = %205, %201
  br label %211

211:                                              ; preds = %210, %200
  %212 = load i8, i8* %22, align 1
  %213 = trunc i8 %212 to i1
  br i1 %213, label %214, label %215

214:                                              ; preds = %211
  br label %228

215:                                              ; preds = %211
  %216 = load i32, i32* %17, align 4
  %217 = icmp sgt i32 %216, 0
  br i1 %217, label %218, label %220

218:                                              ; preds = %215
  %219 = load i32, i32* %17, align 4
  br label %223

220:                                              ; preds = %215
  %221 = load i32, i32* %17, align 4
  %222 = sub nsw i32 0, %221
  br label %223

223:                                              ; preds = %220, %218
  %224 = phi i32 [ %219, %218 ], [ %222, %220 ]
  %225 = icmp slt i32 %224, 100
  %226 = zext i1 %225 to i64
  %227 = select i1 %225, i32 4, i32 5
  br label %228

228:                                              ; preds = %223, %214
  %229 = phi i32 [ 0, %214 ], [ %227, %223 ]
  store i32 %229, i32* %27, align 4
  %230 = load i32, i32* %12, align 4
  %231 = and i32 %230, 2
  %232 = icmp ne i32 %231, 0
  br i1 %232, label %233, label %237

233:                                              ; preds = %228
  %234 = load i32, i32* %27, align 4
  %235 = icmp ne i32 %234, 0
  br i1 %235, label %236, label %237

236:                                              ; preds = %233
  br label %248

237:                                              ; preds = %233, %228
  %238 = load i32, i32* %11, align 4
  %239 = load i32, i32* %27, align 4
  %240 = icmp ugt i32 %238, %239
  br i1 %240, label %241, label %245

241:                                              ; preds = %237
  %242 = load i32, i32* %11, align 4
  %243 = load i32, i32* %27, align 4
  %244 = sub i32 %242, %243
  br label %246

245:                                              ; preds = %237
  br label %246

246:                                              ; preds = %245, %241
  %247 = phi i32 [ %244, %241 ], [ 0, %245 ]
  br label %248

248:                                              ; preds = %246, %236
  %249 = phi i32 [ 0, %236 ], [ %247, %246 ]
  store i32 %249, i32* %28, align 4
  %250 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %251 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %250, i32 0, i32 3
  %252 = load i32, i32* %251, align 8
  store i32 %252, i32* %29, align 4
  %253 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %254 = load i32, i32* %10, align 4
  %255 = load i32, i32* %28, align 4
  %256 = load i32, i32* %12, align 4
  %257 = load i8*, i8** %13, align 8
  %258 = load i32, i32* %14, align 4
  %259 = bitcast %struct.double_components* %30 to i8*
  %260 = bitcast %struct.double_components* %26 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %259, i8* align 8 %260, i64 24, i1 false)
  call void @print_broken_up_decimal(%struct.double_components* noundef %30, %struct.output_gadget_t* noundef %253, i32 noundef %254, i32 noundef %255, i32 noundef %256, i8* noundef %257, i32 noundef %258)
  %261 = load i8, i8* %22, align 1
  %262 = trunc i8 %261 to i1
  br i1 %262, label %303, label %263

263:                                              ; preds = %248
  %264 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %265 = load i32, i32* %12, align 4
  %266 = and i32 %265, 32
  %267 = icmp ne i32 %266, 0
  %268 = zext i1 %267 to i64
  %269 = select i1 %267, i32 69, i32 101
  %270 = trunc i32 %269 to i8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %264, i8 noundef signext %270)
  %271 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %272 = load i32, i32* %17, align 4
  %273 = icmp sgt i32 %272, 0
  br i1 %273, label %274, label %277

274:                                              ; preds = %263
  %275 = load i32, i32* %17, align 4
  %276 = sext i32 %275 to i64
  br label %281

277:                                              ; preds = %263
  %278 = load i32, i32* %17, align 4
  %279 = sext i32 %278 to i64
  %280 = sub nsw i64 0, %279
  br label %281

281:                                              ; preds = %277, %274
  %282 = phi i64 [ %276, %274 ], [ %280, %277 ]
  %283 = load i32, i32* %17, align 4
  %284 = icmp slt i32 %283, 0
  %285 = load i32, i32* %27, align 4
  %286 = sub i32 %285, 1
  call void @print_integer(%struct.output_gadget_t* noundef %271, i64 noundef %282, i1 noundef zeroext %284, i8 noundef zeroext 10, i32 noundef 0, i32 noundef %286, i32 noundef 5)
  %287 = load i32, i32* %12, align 4
  %288 = and i32 %287, 2
  %289 = icmp ne i32 %288, 0
  br i1 %289, label %290, label %302

290:                                              ; preds = %281
  br label %291

291:                                              ; preds = %299, %290
  %292 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %293 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %292, i32 0, i32 3
  %294 = load i32, i32* %293, align 8
  %295 = load i32, i32* %29, align 4
  %296 = sub i32 %294, %295
  %297 = load i32, i32* %11, align 4
  %298 = icmp ult i32 %296, %297
  br i1 %298, label %299, label %301

299:                                              ; preds = %291
  %300 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  call void @putchar_via_gadget(%struct.output_gadget_t* noundef %300, i8 noundef signext 32)
  br label %291, !llvm.loop !25

301:                                              ; preds = %291
  br label %302

302:                                              ; preds = %301, %281
  br label %303

303:                                              ; preds = %302, %248
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_decimal_number(%struct.output_gadget_t* noundef %0, double noundef %1, i32 noundef %2, i32 noundef %3, i32 noundef %4, i8* noundef %5, i32 noundef %6) #0 {
  %8 = alloca %struct.output_gadget_t*, align 8
  %9 = alloca double, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i8*, align 8
  %14 = alloca i32, align 4
  %15 = alloca %struct.double_components, align 8
  %16 = alloca %struct.double_components, align 8
  store %struct.output_gadget_t* %0, %struct.output_gadget_t** %8, align 8
  store double %1, double* %9, align 8
  store i32 %2, i32* %10, align 4
  store i32 %3, i32* %11, align 4
  store i32 %4, i32* %12, align 4
  store i8* %5, i8** %13, align 8
  store i32 %6, i32* %14, align 4
  %17 = load double, double* %9, align 8
  %18 = load i32, i32* %10, align 4
  call void @get_components(%struct.double_components* sret(%struct.double_components) align 8 %15, double noundef %17, i32 noundef %18)
  %19 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %20 = load i32, i32* %10, align 4
  %21 = load i32, i32* %11, align 4
  %22 = load i32, i32* %12, align 4
  %23 = load i8*, i8** %13, align 8
  %24 = load i32, i32* %14, align 4
  %25 = bitcast %struct.double_components* %16 to i8*
  %26 = bitcast %struct.double_components* %15 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %25, i8* align 8 %26, i64 24, i1 false)
  call void @print_broken_up_decimal(%struct.double_components* noundef %16, %struct.output_gadget_t* noundef %19, i32 noundef %20, i32 noundef %21, i32 noundef %22, i8* noundef %23, i32 noundef %24)
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @get_sign_bit(double noundef %0) #0 {
  %2 = alloca double, align 8
  %3 = alloca %union.double_with_bit_access, align 8
  store double %0, double* %2, align 8
  %4 = load double, double* %2, align 8
  %5 = call i64 @get_bit_access(double noundef %4)
  %6 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %3, i32 0, i32 0
  store i64 %5, i64* %6, align 8
  %7 = bitcast %union.double_with_bit_access* %3 to i64*
  %8 = load i64, i64* %7, align 8
  %9 = lshr i64 %8, 63
  %10 = trunc i64 %9 to i32
  ret i32 %10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal double @log10_of_positive(double noundef %0) #0 {
  %2 = alloca double, align 8
  %3 = alloca %union.double_with_bit_access, align 8
  %4 = alloca i32, align 4
  %5 = alloca double, align 8
  store double %0, double* %2, align 8
  %6 = load double, double* %2, align 8
  %7 = call i64 @get_bit_access(double noundef %6)
  %8 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %3, i32 0, i32 0
  store i64 %7, i64* %8, align 8
  %9 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %3, i32 0, i32 0
  %10 = load i64, i64* %9, align 8
  %11 = call i32 @get_exp2(i64 %10)
  store i32 %11, i32* %4, align 4
  %12 = bitcast %union.double_with_bit_access* %3 to i64*
  %13 = load i64, i64* %12, align 8
  %14 = and i64 %13, 4503599627370495
  %15 = or i64 %14, 4607182418800017408
  %16 = bitcast %union.double_with_bit_access* %3 to i64*
  store i64 %15, i64* %16, align 8
  %17 = bitcast %union.double_with_bit_access* %3 to double*
  %18 = load double, double* %17, align 8
  %19 = fsub double %18, 1.500000e+00
  store double %19, double* %5, align 8
  %20 = load double, double* %5, align 8
  %21 = call double @llvm.fmuladd.f64(double %20, double 0x3FD287A7636F435F, double 0x3FC68A288B60B7FC)
  %22 = load double, double* %5, align 8
  %23 = load double, double* %5, align 8
  %24 = fmul double %22, %23
  %25 = fneg double %24
  %26 = call double @llvm.fmuladd.f64(double %25, double 0x3FB8B4DF2F3F047E, double %21)
  %27 = load double, double* %5, align 8
  %28 = load double, double* %5, align 8
  %29 = fmul double %27, %28
  %30 = load double, double* %5, align 8
  %31 = fmul double %29, %30
  %32 = call double @llvm.fmuladd.f64(double %31, double 0x3FA5F61BB83803FF, double %26)
  %33 = load i32, i32* %4, align 4
  %34 = sitofp i32 %33 to double
  %35 = call double @llvm.fmuladd.f64(double %34, double 0x3FD34413509F79FF, double %32)
  ret double %35
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @bastardized_floor(double noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca double, align 8
  %4 = alloca i32, align 4
  store double %0, double* %3, align 8
  %5 = load double, double* %3, align 8
  %6 = fcmp oge double %5, 0.000000e+00
  br i1 %6, label %7, label %10

7:                                                ; preds = %1
  %8 = load double, double* %3, align 8
  %9 = fptosi double %8 to i32
  store i32 %9, i32* %2, align 4
  br label %24

10:                                               ; preds = %1
  %11 = load double, double* %3, align 8
  %12 = fptosi double %11 to i32
  store i32 %12, i32* %4, align 4
  %13 = load i32, i32* %4, align 4
  %14 = sitofp i32 %13 to double
  %15 = load double, double* %3, align 8
  %16 = fcmp oeq double %14, %15
  br i1 %16, label %17, label %19

17:                                               ; preds = %10
  %18 = load i32, i32* %4, align 4
  br label %22

19:                                               ; preds = %10
  %20 = load i32, i32* %4, align 4
  %21 = sub nsw i32 %20, 1
  br label %22

22:                                               ; preds = %19, %17
  %23 = phi i32 [ %18, %17 ], [ %21, %19 ]
  store i32 %23, i32* %2, align 4
  br label %24

24:                                               ; preds = %22, %7
  %25 = load i32, i32* %2, align 4
  ret i32 %25
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal double @pow10_of_int(i32 noundef %0) #0 {
  %2 = alloca double, align 8
  %3 = alloca i32, align 4
  %4 = alloca %union.double_with_bit_access, align 8
  %5 = alloca i32, align 4
  %6 = alloca double, align 8
  %7 = alloca double, align 8
  store i32 %0, i32* %3, align 4
  %8 = load i32, i32* %3, align 4
  %9 = icmp eq i32 %8, -308
  br i1 %9, label %10, label %11

10:                                               ; preds = %1
  store double 0x730D67819E8D2, double* %2, align 8
  br label %51

11:                                               ; preds = %1
  %12 = load i32, i32* %3, align 4
  %13 = sitofp i32 %12 to double
  %14 = call double @llvm.fmuladd.f64(double %13, double 0x400A934F0979A371, double 5.000000e-01)
  %15 = call i32 @bastardized_floor(double noundef %14)
  store i32 %15, i32* %5, align 4
  %16 = load i32, i32* %3, align 4
  %17 = sitofp i32 %16 to double
  %18 = load i32, i32* %5, align 4
  %19 = sitofp i32 %18 to double
  %20 = fmul double %19, 0x3FE62E42FEFA39EF
  %21 = fneg double %20
  %22 = call double @llvm.fmuladd.f64(double %17, double 0x40026BB1BBB55516, double %21)
  store double %22, double* %6, align 8
  %23 = load double, double* %6, align 8
  %24 = load double, double* %6, align 8
  %25 = fmul double %23, %24
  store double %25, double* %7, align 8
  %26 = load i32, i32* %5, align 4
  %27 = sext i32 %26 to i64
  %28 = add i64 %27, 1023
  %29 = shl i64 %28, 52
  %30 = bitcast %union.double_with_bit_access* %4 to i64*
  store i64 %29, i64* %30, align 8
  %31 = load double, double* %6, align 8
  %32 = fmul double 2.000000e+00, %31
  %33 = load double, double* %6, align 8
  %34 = fsub double 2.000000e+00, %33
  %35 = load double, double* %7, align 8
  %36 = load double, double* %7, align 8
  %37 = load double, double* %7, align 8
  %38 = fdiv double %37, 1.400000e+01
  %39 = fadd double 1.000000e+01, %38
  %40 = fdiv double %36, %39
  %41 = fadd double 6.000000e+00, %40
  %42 = fdiv double %35, %41
  %43 = fadd double %34, %42
  %44 = fdiv double %32, %43
  %45 = fadd double 1.000000e+00, %44
  %46 = bitcast %union.double_with_bit_access* %4 to double*
  %47 = load double, double* %46, align 8
  %48 = fmul double %47, %45
  store double %48, double* %46, align 8
  %49 = bitcast %union.double_with_bit_access* %4 to double*
  %50 = load double, double* %49, align 8
  store double %50, double* %2, align 8
  br label %51

51:                                               ; preds = %11, %10
  %52 = load double, double* %2, align 8
  ret double %52
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @get_components(%struct.double_components* noalias sret(%struct.double_components) align 8 %0, double noundef %1, i32 noundef %2) #0 {
  %4 = alloca double, align 8
  %5 = alloca i32, align 4
  %6 = alloca double, align 8
  %7 = alloca double, align 8
  store double %1, double* %4, align 8
  store i32 %2, i32* %5, align 4
  %8 = load double, double* %4, align 8
  %9 = call i32 @get_sign_bit(double noundef %8)
  %10 = icmp ne i32 %9, 0
  %11 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 2
  %12 = zext i1 %10 to i8
  store i8 %12, i8* %11, align 8
  %13 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 2
  %14 = load i8, i8* %13, align 8
  %15 = trunc i8 %14 to i1
  br i1 %15, label %16, label %19

16:                                               ; preds = %3
  %17 = load double, double* %4, align 8
  %18 = fneg double %17
  br label %21

19:                                               ; preds = %3
  %20 = load double, double* %4, align 8
  br label %21

21:                                               ; preds = %19, %16
  %22 = phi double [ %18, %16 ], [ %20, %19 ]
  store double %22, double* %6, align 8
  %23 = load double, double* %6, align 8
  %24 = fptosi double %23 to i64
  %25 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  store i64 %24, i64* %25, align 8
  %26 = load double, double* %6, align 8
  %27 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %28 = load i64, i64* %27, align 8
  %29 = sitofp i64 %28 to double
  %30 = fsub double %26, %29
  %31 = load i32, i32* %5, align 4
  %32 = zext i32 %31 to i64
  %33 = getelementptr inbounds [18 x double], [18 x double]* @powers_of_10, i64 0, i64 %32
  %34 = load double, double* %33, align 8
  %35 = fmul double %30, %34
  store double %35, double* %7, align 8
  %36 = load double, double* %7, align 8
  %37 = fptosi double %36 to i64
  %38 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  store i64 %37, i64* %38, align 8
  %39 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %40 = load i64, i64* %39, align 8
  %41 = sitofp i64 %40 to double
  %42 = load double, double* %7, align 8
  %43 = fsub double %42, %41
  store double %43, double* %7, align 8
  %44 = load double, double* %7, align 8
  %45 = fcmp ogt double %44, 5.000000e-01
  br i1 %45, label %46, label %64

46:                                               ; preds = %21
  %47 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %48 = load i64, i64* %47, align 8
  %49 = add nsw i64 %48, 1
  store i64 %49, i64* %47, align 8
  %50 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %51 = load i64, i64* %50, align 8
  %52 = sitofp i64 %51 to double
  %53 = load i32, i32* %5, align 4
  %54 = zext i32 %53 to i64
  %55 = getelementptr inbounds [18 x double], [18 x double]* @powers_of_10, i64 0, i64 %54
  %56 = load double, double* %55, align 8
  %57 = fcmp oge double %52, %56
  br i1 %57, label %58, label %63

58:                                               ; preds = %46
  %59 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  store i64 0, i64* %59, align 8
  %60 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %61 = load i64, i64* %60, align 8
  %62 = add nsw i64 %61, 1
  store i64 %62, i64* %60, align 8
  br label %63

63:                                               ; preds = %58, %46
  br label %81

64:                                               ; preds = %21
  %65 = load double, double* %7, align 8
  %66 = fcmp oeq double %65, 5.000000e-01
  br i1 %66, label %67, label %80

67:                                               ; preds = %64
  %68 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %69 = load i64, i64* %68, align 8
  %70 = icmp eq i64 %69, 0
  br i1 %70, label %76, label %71

71:                                               ; preds = %67
  %72 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %73 = load i64, i64* %72, align 8
  %74 = and i64 %73, 1
  %75 = icmp ne i64 %74, 0
  br i1 %75, label %76, label %80

76:                                               ; preds = %71, %67
  %77 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %78 = load i64, i64* %77, align 8
  %79 = add nsw i64 %78, 1
  store i64 %79, i64* %77, align 8
  br label %80

80:                                               ; preds = %76, %71, %64
  br label %81

81:                                               ; preds = %80, %63
  %82 = load i32, i32* %5, align 4
  %83 = icmp eq i32 %82, 0
  br i1 %83, label %84, label %105

84:                                               ; preds = %81
  %85 = load double, double* %6, align 8
  %86 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %87 = load i64, i64* %86, align 8
  %88 = sitofp i64 %87 to double
  %89 = fsub double %85, %88
  store double %89, double* %7, align 8
  %90 = load double, double* %7, align 8
  %91 = fcmp olt double %90, 5.000000e-01
  br i1 %91, label %92, label %95

92:                                               ; preds = %84
  %93 = load double, double* %7, align 8
  %94 = fcmp ogt double %93, 5.000000e-01
  br i1 %94, label %95, label %104

95:                                               ; preds = %92, %84
  %96 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %97 = load i64, i64* %96, align 8
  %98 = and i64 %97, 1
  %99 = icmp ne i64 %98, 0
  br i1 %99, label %100, label %104

100:                                              ; preds = %95
  %101 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %102 = load i64, i64* %101, align 8
  %103 = add nsw i64 %102, 1
  store i64 %103, i64* %101, align 8
  br label %104

104:                                              ; preds = %100, %95, %92
  br label %105

105:                                              ; preds = %104, %81
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @get_normalized_components(%struct.double_components* noalias sret(%struct.double_components) align 8 %0, i1 noundef zeroext %1, i32 noundef %2, double noundef %3, [2 x i64] %4, i32 noundef %5) #0 {
  %7 = alloca %struct.scaling_factor, align 8
  %8 = alloca i8, align 1
  %9 = alloca i32, align 4
  %10 = alloca double, align 8
  %11 = alloca i32, align 4
  %12 = alloca %struct.double_components, align 8
  %13 = alloca double, align 8
  %14 = alloca i8, align 1
  %15 = alloca double, align 8
  %16 = alloca double, align 8
  %17 = alloca %struct.scaling_factor, align 8
  %18 = alloca double, align 8
  %19 = alloca double, align 8
  %20 = bitcast %struct.scaling_factor* %7 to [2 x i64]*
  store [2 x i64] %4, [2 x i64]* %20, align 8
  %21 = zext i1 %1 to i8
  store i8 %21, i8* %8, align 1
  store i32 %2, i32* %9, align 4
  store double %3, double* %10, align 8
  store i32 %5, i32* %11, align 4
  %22 = load i8, i8* %8, align 1
  %23 = trunc i8 %22 to i1
  %24 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 2
  %25 = zext i1 %23 to i8
  store i8 %25, i8* %24, align 8
  %26 = load double, double* %10, align 8
  %27 = bitcast %struct.scaling_factor* %7 to [2 x i64]*
  %28 = load [2 x i64], [2 x i64]* %27, align 8
  %29 = call double @apply_scaling(double noundef %26, [2 x i64] %28)
  store double %29, double* %13, align 8
  %30 = load i32, i32* %11, align 4
  %31 = sub nsw i32 0, %30
  %32 = load i32, i32* %9, align 4
  %33 = add nsw i32 %31, %32
  %34 = icmp sge i32 %33, 307
  %35 = zext i1 %34 to i8
  store i8 %35, i8* %14, align 1
  %36 = load i8, i8* %14, align 1
  %37 = trunc i8 %36 to i1
  br i1 %37, label %38, label %49

38:                                               ; preds = %6
  %39 = load i8, i8* %8, align 1
  %40 = trunc i8 %39 to i1
  br i1 %40, label %41, label %44

41:                                               ; preds = %38
  %42 = load double, double* %13, align 8
  %43 = fneg double %42
  br label %46

44:                                               ; preds = %38
  %45 = load double, double* %13, align 8
  br label %46

46:                                               ; preds = %44, %41
  %47 = phi double [ %43, %41 ], [ %45, %44 ]
  %48 = load i32, i32* %9, align 4
  call void @get_components(%struct.double_components* sret(%struct.double_components) align 8 %0, double noundef %47, i32 noundef %48)
  br label %111

49:                                               ; preds = %6
  %50 = load double, double* %13, align 8
  %51 = fptosi double %50 to i64
  %52 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 0
  store i64 %51, i64* %52, align 8
  %53 = load double, double* %10, align 8
  %54 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 0
  %55 = load i64, i64* %54, align 8
  %56 = sitofp i64 %55 to double
  %57 = bitcast %struct.scaling_factor* %7 to [2 x i64]*
  %58 = load [2 x i64], [2 x i64]* %57, align 8
  %59 = call double @unapply_scaling(double noundef %56, [2 x i64] %58)
  %60 = fsub double %53, %59
  store double %60, double* %15, align 8
  %61 = load i32, i32* %9, align 4
  %62 = zext i32 %61 to i64
  %63 = getelementptr inbounds [18 x double], [18 x double]* @powers_of_10, i64 0, i64 %62
  %64 = load double, double* %63, align 8
  store double %64, double* %16, align 8
  %65 = load double, double* %16, align 8
  %66 = bitcast %struct.scaling_factor* %7 to [2 x i64]*
  %67 = load [2 x i64], [2 x i64]* %66, align 8
  %68 = call [2 x i64] @update_normalization([2 x i64] %67, double noundef %65)
  %69 = bitcast %struct.scaling_factor* %17 to [2 x i64]*
  store [2 x i64] %68, [2 x i64]* %69, align 8
  %70 = load double, double* %15, align 8
  %71 = bitcast %struct.scaling_factor* %17 to [2 x i64]*
  %72 = load [2 x i64], [2 x i64]* %71, align 8
  %73 = call double @apply_scaling(double noundef %70, [2 x i64] %72)
  store double %73, double* %18, align 8
  store double 5.000000e-01, double* %19, align 8
  %74 = load double, double* %18, align 8
  %75 = fptosi double %74 to i64
  %76 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  store i64 %75, i64* %76, align 8
  %77 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  %78 = load i64, i64* %77, align 8
  %79 = sitofp i64 %78 to double
  %80 = load double, double* %18, align 8
  %81 = fsub double %80, %79
  store double %81, double* %18, align 8
  %82 = load double, double* %18, align 8
  %83 = load double, double* %19, align 8
  %84 = fcmp oge double %82, %83
  %85 = zext i1 %84 to i32
  %86 = sext i32 %85 to i64
  %87 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  %88 = load i64, i64* %87, align 8
  %89 = add nsw i64 %88, %86
  store i64 %89, i64* %87, align 8
  %90 = load double, double* %18, align 8
  %91 = load double, double* %19, align 8
  %92 = fcmp oeq double %90, %91
  br i1 %92, label %93, label %97

93:                                               ; preds = %49
  %94 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  %95 = load i64, i64* %94, align 8
  %96 = and i64 %95, -2
  store i64 %96, i64* %94, align 8
  br label %97

97:                                               ; preds = %93, %49
  %98 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  %99 = load i64, i64* %98, align 8
  %100 = sitofp i64 %99 to double
  %101 = load double, double* %16, align 8
  %102 = fcmp oge double %100, %101
  br i1 %102, label %103, label %108

103:                                              ; preds = %97
  %104 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 1
  store i64 0, i64* %104, align 8
  %105 = getelementptr inbounds %struct.double_components, %struct.double_components* %12, i32 0, i32 0
  %106 = load i64, i64* %105, align 8
  %107 = add nsw i64 %106, 1
  store i64 %107, i64* %105, align 8
  br label %108

108:                                              ; preds = %103, %97
  %109 = bitcast %struct.double_components* %0 to i8*
  %110 = bitcast %struct.double_components* %12 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %109, i8* align 8 %110, i64 24, i1 false)
  br label %111

111:                                              ; preds = %108, %46
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @print_broken_up_decimal(%struct.double_components* noundef %0, %struct.output_gadget_t* noundef %1, i32 noundef %2, i32 noundef %3, i32 noundef %4, i8* noundef %5, i32 noundef %6) #0 {
  %8 = alloca %struct.output_gadget_t*, align 8
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i8*, align 8
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i64, align 8
  store %struct.output_gadget_t* %1, %struct.output_gadget_t** %8, align 8
  store i32 %2, i32* %9, align 4
  store i32 %3, i32* %10, align 4
  store i32 %4, i32* %11, align 4
  store i8* %5, i8** %12, align 8
  store i32 %6, i32* %13, align 4
  %16 = load i32, i32* %9, align 4
  %17 = icmp ne i32 %16, 0
  br i1 %17, label %18, label %109

18:                                               ; preds = %7
  %19 = load i32, i32* %9, align 4
  store i32 %19, i32* %14, align 4
  %20 = load i32, i32* %11, align 4
  %21 = and i32 %20, 4096
  %22 = icmp ne i32 %21, 0
  br i1 %22, label %23, label %46

23:                                               ; preds = %18
  %24 = load i32, i32* %11, align 4
  %25 = and i32 %24, 16
  %26 = icmp ne i32 %25, 0
  br i1 %26, label %46, label %27

27:                                               ; preds = %23
  %28 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %29 = load i64, i64* %28, align 8
  %30 = icmp sgt i64 %29, 0
  br i1 %30, label %31, label %46

31:                                               ; preds = %27
  br label %32

32:                                               ; preds = %31, %39
  %33 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %34 = load i64, i64* %33, align 8
  %35 = srem i64 %34, 10
  store i64 %35, i64* %15, align 8
  %36 = load i64, i64* %15, align 8
  %37 = icmp ne i64 %36, 0
  br i1 %37, label %38, label %39

38:                                               ; preds = %32
  br label %45

39:                                               ; preds = %32
  %40 = load i32, i32* %14, align 4
  %41 = add i32 %40, -1
  store i32 %41, i32* %14, align 4
  %42 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %43 = load i64, i64* %42, align 8
  %44 = sdiv i64 %43, 10
  store i64 %44, i64* %42, align 8
  br label %32

45:                                               ; preds = %38
  br label %46

46:                                               ; preds = %45, %27, %23, %18
  %47 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %48 = load i64, i64* %47, align 8
  %49 = icmp sgt i64 %48, 0
  br i1 %49, label %58, label %50

50:                                               ; preds = %46
  %51 = load i32, i32* %11, align 4
  %52 = and i32 %51, 4096
  %53 = icmp ne i32 %52, 0
  br i1 %53, label %54, label %58

54:                                               ; preds = %50
  %55 = load i32, i32* %11, align 4
  %56 = and i32 %55, 16
  %57 = icmp ne i32 %56, 0
  br i1 %57, label %58, label %108

58:                                               ; preds = %54, %50, %46
  br label %59

59:                                               ; preds = %80, %58
  %60 = load i32, i32* %13, align 4
  %61 = icmp ult i32 %60, 32
  br i1 %61, label %62, label %81

62:                                               ; preds = %59
  %63 = load i32, i32* %14, align 4
  %64 = add i32 %63, -1
  store i32 %64, i32* %14, align 4
  %65 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %66 = load i64, i64* %65, align 8
  %67 = srem i64 %66, 10
  %68 = add nsw i64 48, %67
  %69 = trunc i64 %68 to i8
  %70 = load i8*, i8** %12, align 8
  %71 = load i32, i32* %13, align 4
  %72 = add i32 %71, 1
  store i32 %72, i32* %13, align 4
  %73 = zext i32 %71 to i64
  %74 = getelementptr inbounds i8, i8* %70, i64 %73
  store i8 %69, i8* %74, align 1
  %75 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 1
  %76 = load i64, i64* %75, align 8
  %77 = sdiv i64 %76, 10
  store i64 %77, i64* %75, align 8
  %78 = icmp ne i64 %77, 0
  br i1 %78, label %80, label %79

79:                                               ; preds = %62
  br label %81

80:                                               ; preds = %62
  br label %59, !llvm.loop !26

81:                                               ; preds = %79, %59
  br label %82

82:                                               ; preds = %90, %81
  %83 = load i32, i32* %13, align 4
  %84 = icmp ult i32 %83, 32
  br i1 %84, label %85, label %88

85:                                               ; preds = %82
  %86 = load i32, i32* %14, align 4
  %87 = icmp ugt i32 %86, 0
  br label %88

88:                                               ; preds = %85, %82
  %89 = phi i1 [ false, %82 ], [ %87, %85 ]
  br i1 %89, label %90, label %98

90:                                               ; preds = %88
  %91 = load i8*, i8** %12, align 8
  %92 = load i32, i32* %13, align 4
  %93 = add i32 %92, 1
  store i32 %93, i32* %13, align 4
  %94 = zext i32 %92 to i64
  %95 = getelementptr inbounds i8, i8* %91, i64 %94
  store i8 48, i8* %95, align 1
  %96 = load i32, i32* %14, align 4
  %97 = add i32 %96, -1
  store i32 %97, i32* %14, align 4
  br label %82, !llvm.loop !27

98:                                               ; preds = %88
  %99 = load i32, i32* %13, align 4
  %100 = icmp ult i32 %99, 32
  br i1 %100, label %101, label %107

101:                                              ; preds = %98
  %102 = load i8*, i8** %12, align 8
  %103 = load i32, i32* %13, align 4
  %104 = add i32 %103, 1
  store i32 %104, i32* %13, align 4
  %105 = zext i32 %103 to i64
  %106 = getelementptr inbounds i8, i8* %102, i64 %105
  store i8 46, i8* %106, align 1
  br label %107

107:                                              ; preds = %101, %98
  br label %108

108:                                              ; preds = %107, %54
  br label %123

109:                                              ; preds = %7
  %110 = load i32, i32* %11, align 4
  %111 = and i32 %110, 16
  %112 = icmp ne i32 %111, 0
  br i1 %112, label %113, label %122

113:                                              ; preds = %109
  %114 = load i32, i32* %13, align 4
  %115 = icmp ult i32 %114, 32
  br i1 %115, label %116, label %122

116:                                              ; preds = %113
  %117 = load i8*, i8** %12, align 8
  %118 = load i32, i32* %13, align 4
  %119 = add i32 %118, 1
  store i32 %119, i32* %13, align 4
  %120 = zext i32 %118 to i64
  %121 = getelementptr inbounds i8, i8* %117, i64 %120
  store i8 46, i8* %121, align 1
  br label %122

122:                                              ; preds = %116, %113, %109
  br label %123

123:                                              ; preds = %122, %108
  br label %124

124:                                              ; preds = %143, %123
  %125 = load i32, i32* %13, align 4
  %126 = icmp ult i32 %125, 32
  br i1 %126, label %127, label %144

127:                                              ; preds = %124
  %128 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %129 = load i64, i64* %128, align 8
  %130 = srem i64 %129, 10
  %131 = add nsw i64 48, %130
  %132 = trunc i64 %131 to i8
  %133 = load i8*, i8** %12, align 8
  %134 = load i32, i32* %13, align 4
  %135 = add i32 %134, 1
  store i32 %135, i32* %13, align 4
  %136 = zext i32 %134 to i64
  %137 = getelementptr inbounds i8, i8* %133, i64 %136
  store i8 %132, i8* %137, align 1
  %138 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 0
  %139 = load i64, i64* %138, align 8
  %140 = sdiv i64 %139, 10
  store i64 %140, i64* %138, align 8
  %141 = icmp ne i64 %140, 0
  br i1 %141, label %143, label %142

142:                                              ; preds = %127
  br label %144

143:                                              ; preds = %127
  br label %124, !llvm.loop !28

144:                                              ; preds = %142, %124
  %145 = load i32, i32* %11, align 4
  %146 = and i32 %145, 2
  %147 = icmp ne i32 %146, 0
  br i1 %147, label %183, label %148

148:                                              ; preds = %144
  %149 = load i32, i32* %11, align 4
  %150 = and i32 %149, 1
  %151 = icmp ne i32 %150, 0
  br i1 %151, label %152, label %183

152:                                              ; preds = %148
  %153 = load i32, i32* %10, align 4
  %154 = icmp ne i32 %153, 0
  br i1 %154, label %155, label %166

155:                                              ; preds = %152
  %156 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 2
  %157 = load i8, i8* %156, align 8
  %158 = trunc i8 %157 to i1
  br i1 %158, label %163, label %159

159:                                              ; preds = %155
  %160 = load i32, i32* %11, align 4
  %161 = and i32 %160, 12
  %162 = icmp ne i32 %161, 0
  br i1 %162, label %163, label %166

163:                                              ; preds = %159, %155
  %164 = load i32, i32* %10, align 4
  %165 = add i32 %164, -1
  store i32 %165, i32* %10, align 4
  br label %166

166:                                              ; preds = %163, %159, %152
  br label %167

167:                                              ; preds = %176, %166
  %168 = load i32, i32* %13, align 4
  %169 = load i32, i32* %10, align 4
  %170 = icmp ult i32 %168, %169
  br i1 %170, label %171, label %174

171:                                              ; preds = %167
  %172 = load i32, i32* %13, align 4
  %173 = icmp ult i32 %172, 32
  br label %174

174:                                              ; preds = %171, %167
  %175 = phi i1 [ false, %167 ], [ %173, %171 ]
  br i1 %175, label %176, label %182

176:                                              ; preds = %174
  %177 = load i8*, i8** %12, align 8
  %178 = load i32, i32* %13, align 4
  %179 = add i32 %178, 1
  store i32 %179, i32* %13, align 4
  %180 = zext i32 %178 to i64
  %181 = getelementptr inbounds i8, i8* %177, i64 %180
  store i8 48, i8* %181, align 1
  br label %167, !llvm.loop !29

182:                                              ; preds = %174
  br label %183

183:                                              ; preds = %182, %148, %144
  %184 = load i32, i32* %13, align 4
  %185 = icmp ult i32 %184, 32
  br i1 %185, label %186, label %219

186:                                              ; preds = %183
  %187 = getelementptr inbounds %struct.double_components, %struct.double_components* %0, i32 0, i32 2
  %188 = load i8, i8* %187, align 8
  %189 = trunc i8 %188 to i1
  br i1 %189, label %190, label %196

190:                                              ; preds = %186
  %191 = load i8*, i8** %12, align 8
  %192 = load i32, i32* %13, align 4
  %193 = add i32 %192, 1
  store i32 %193, i32* %13, align 4
  %194 = zext i32 %192 to i64
  %195 = getelementptr inbounds i8, i8* %191, i64 %194
  store i8 45, i8* %195, align 1
  br label %218

196:                                              ; preds = %186
  %197 = load i32, i32* %11, align 4
  %198 = and i32 %197, 4
  %199 = icmp ne i32 %198, 0
  br i1 %199, label %200, label %206

200:                                              ; preds = %196
  %201 = load i8*, i8** %12, align 8
  %202 = load i32, i32* %13, align 4
  %203 = add i32 %202, 1
  store i32 %203, i32* %13, align 4
  %204 = zext i32 %202 to i64
  %205 = getelementptr inbounds i8, i8* %201, i64 %204
  store i8 43, i8* %205, align 1
  br label %217

206:                                              ; preds = %196
  %207 = load i32, i32* %11, align 4
  %208 = and i32 %207, 8
  %209 = icmp ne i32 %208, 0
  br i1 %209, label %210, label %216

210:                                              ; preds = %206
  %211 = load i8*, i8** %12, align 8
  %212 = load i32, i32* %13, align 4
  %213 = add i32 %212, 1
  store i32 %213, i32* %13, align 4
  %214 = zext i32 %212 to i64
  %215 = getelementptr inbounds i8, i8* %211, i64 %214
  store i8 32, i8* %215, align 1
  br label %216

216:                                              ; preds = %210, %206
  br label %217

217:                                              ; preds = %216, %200
  br label %218

218:                                              ; preds = %217, %190
  br label %219

219:                                              ; preds = %218, %183
  %220 = load %struct.output_gadget_t*, %struct.output_gadget_t** %8, align 8
  %221 = load i8*, i8** %12, align 8
  %222 = load i32, i32* %13, align 4
  %223 = load i32, i32* %10, align 4
  %224 = load i32, i32* %11, align 4
  call void @out_rev_(%struct.output_gadget_t* noundef %220, i8* noundef %221, i32 noundef %222, i32 noundef %223, i32 noundef %224)
  ret void
}

; Function Attrs: argmemonly nofree nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #3

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @get_bit_access(double noundef %0) #0 {
  %2 = alloca %union.double_with_bit_access, align 8
  %3 = alloca double, align 8
  store double %0, double* %3, align 8
  %4 = load double, double* %3, align 8
  %5 = bitcast %union.double_with_bit_access* %2 to double*
  store double %4, double* %5, align 8
  %6 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %2, i32 0, i32 0
  %7 = load i64, i64* %6, align 8
  ret i64 %7
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @get_exp2(i64 %0) #0 {
  %2 = alloca %union.double_with_bit_access, align 8
  %3 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %2, i32 0, i32 0
  store i64 %0, i64* %3, align 8
  %4 = bitcast %union.double_with_bit_access* %2 to i64*
  %5 = load i64, i64* %4, align 8
  %6 = lshr i64 %5, 52
  %7 = and i64 %6, 2047
  %8 = trunc i64 %7 to i32
  %9 = sub nsw i32 %8, 1023
  ret i32 %9
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare double @llvm.fmuladd.f64(double, double, double) #4

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal double @apply_scaling(double noundef %0, [2 x i64] %1) #0 {
  %3 = alloca %struct.scaling_factor, align 8
  %4 = alloca double, align 8
  %5 = bitcast %struct.scaling_factor* %3 to [2 x i64]*
  store [2 x i64] %1, [2 x i64]* %5, align 8
  store double %0, double* %4, align 8
  %6 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 1
  %7 = load i8, i8* %6, align 8
  %8 = trunc i8 %7 to i1
  br i1 %8, label %9, label %14

9:                                                ; preds = %2
  %10 = load double, double* %4, align 8
  %11 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  %12 = load double, double* %11, align 8
  %13 = fmul double %10, %12
  br label %19

14:                                               ; preds = %2
  %15 = load double, double* %4, align 8
  %16 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  %17 = load double, double* %16, align 8
  %18 = fdiv double %15, %17
  br label %19

19:                                               ; preds = %14, %9
  %20 = phi double [ %13, %9 ], [ %18, %14 ]
  ret double %20
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal double @unapply_scaling(double noundef %0, [2 x i64] %1) #0 {
  %3 = alloca %struct.scaling_factor, align 8
  %4 = alloca double, align 8
  %5 = bitcast %struct.scaling_factor* %3 to [2 x i64]*
  store [2 x i64] %1, [2 x i64]* %5, align 8
  store double %0, double* %4, align 8
  %6 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 1
  %7 = load i8, i8* %6, align 8
  %8 = trunc i8 %7 to i1
  br i1 %8, label %9, label %14

9:                                                ; preds = %2
  %10 = load double, double* %4, align 8
  %11 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  %12 = load double, double* %11, align 8
  %13 = fdiv double %10, %12
  br label %19

14:                                               ; preds = %2
  %15 = load double, double* %4, align 8
  %16 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  %17 = load double, double* %16, align 8
  %18 = fmul double %15, %17
  br label %19

19:                                               ; preds = %14, %9
  %20 = phi double [ %13, %9 ], [ %18, %14 ]
  ret double %20
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal [2 x i64] @update_normalization([2 x i64] %0, double noundef %1) #0 {
  %3 = alloca %struct.scaling_factor, align 8
  %4 = alloca %struct.scaling_factor, align 8
  %5 = alloca double, align 8
  %6 = alloca i32, align 4
  %7 = alloca %union.double_with_bit_access, align 8
  %8 = alloca i32, align 4
  %9 = alloca %union.double_with_bit_access, align 8
  %10 = bitcast %struct.scaling_factor* %4 to [2 x i64]*
  store [2 x i64] %0, [2 x i64]* %10, align 8
  store double %1, double* %5, align 8
  %11 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %4, i32 0, i32 1
  %12 = load i8, i8* %11, align 8
  %13 = trunc i8 %12 to i1
  br i1 %13, label %14, label %21

14:                                               ; preds = %2
  %15 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 1
  store i8 1, i8* %15, align 8
  %16 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %4, i32 0, i32 0
  %17 = load double, double* %16, align 8
  %18 = load double, double* %5, align 8
  %19 = fmul double %17, %18
  %20 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  store double %19, double* %20, align 8
  br label %69

21:                                               ; preds = %2
  %22 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %4, i32 0, i32 0
  %23 = load double, double* %22, align 8
  %24 = call i64 @get_bit_access(double noundef %23)
  %25 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %7, i32 0, i32 0
  store i64 %24, i64* %25, align 8
  %26 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %7, i32 0, i32 0
  %27 = load i64, i64* %26, align 8
  %28 = call i32 @get_exp2(i64 %27)
  store i32 %28, i32* %6, align 4
  %29 = load double, double* %5, align 8
  %30 = call i64 @get_bit_access(double noundef %29)
  %31 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %9, i32 0, i32 0
  store i64 %30, i64* %31, align 8
  %32 = getelementptr inbounds %union.double_with_bit_access, %union.double_with_bit_access* %9, i32 0, i32 0
  %33 = load i64, i64* %32, align 8
  %34 = call i32 @get_exp2(i64 %33)
  store i32 %34, i32* %8, align 4
  %35 = load i32, i32* %6, align 4
  %36 = icmp sgt i32 %35, 0
  br i1 %36, label %37, label %39

37:                                               ; preds = %21
  %38 = load i32, i32* %6, align 4
  br label %42

39:                                               ; preds = %21
  %40 = load i32, i32* %6, align 4
  %41 = sub nsw i32 0, %40
  br label %42

42:                                               ; preds = %39, %37
  %43 = phi i32 [ %38, %37 ], [ %41, %39 ]
  %44 = load i32, i32* %8, align 4
  %45 = icmp sgt i32 %44, 0
  br i1 %45, label %46, label %48

46:                                               ; preds = %42
  %47 = load i32, i32* %8, align 4
  br label %51

48:                                               ; preds = %42
  %49 = load i32, i32* %8, align 4
  %50 = sub nsw i32 0, %49
  br label %51

51:                                               ; preds = %48, %46
  %52 = phi i32 [ %47, %46 ], [ %50, %48 ]
  %53 = icmp sgt i32 %43, %52
  br i1 %53, label %54, label %61

54:                                               ; preds = %51
  %55 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 1
  store i8 0, i8* %55, align 8
  %56 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %4, i32 0, i32 0
  %57 = load double, double* %56, align 8
  %58 = load double, double* %5, align 8
  %59 = fdiv double %57, %58
  %60 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  store double %59, double* %60, align 8
  br label %68

61:                                               ; preds = %51
  %62 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 1
  store i8 1, i8* %62, align 8
  %63 = load double, double* %5, align 8
  %64 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %4, i32 0, i32 0
  %65 = load double, double* %64, align 8
  %66 = fdiv double %63, %65
  %67 = getelementptr inbounds %struct.scaling_factor, %struct.scaling_factor* %3, i32 0, i32 0
  store double %66, double* %67, align 8
  br label %68

68:                                               ; preds = %61, %54
  br label %69

69:                                               ; preds = %68, %14
  %70 = bitcast %struct.scaling_factor* %3 to [2 x i64]*
  %71 = load [2 x i64], [2 x i64]* %70, align 8
  ret [2 x i64] %71
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @discarding_gadget(%struct.output_gadget_t* noalias sret(%struct.output_gadget_t) align 8 %0) #0 {
  %2 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 0
  store void (i8, i8*)* null, void (i8, i8*)** %2, align 8
  %3 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 1
  store i8* null, i8** %3, align 8
  %4 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 2
  store i8* null, i8** %4, align 8
  %5 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 3
  store i32 0, i32* %5, align 8
  %6 = getelementptr inbounds %struct.output_gadget_t, %struct.output_gadget_t* %0, i32 0, i32 4
  store i32 0, i32* %6, align 4
  ret void
}

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
attributes #1 = { nofree nosync nounwind willreturn }
attributes #2 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
attributes #3 = { argmemonly nofree nounwind willreturn }
attributes #4 = { nofree nosync nounwind readnone speculatable willreturn }

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
