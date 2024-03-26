; ModuleID = 'blah.bc'
source_filename = "llvm-link"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

@seed = global i64 0, align 8
@var_0 = global i64 974408894297567841, align 8
@var_1 = global i8 66, align 1
@var_2 = global i8 0, align 1
@var_3 = global i64 5641188591160976061, align 8
@var_4 = global i8 0, align 1
@var_5 = global i8 -93, align 1
@var_6 = global i64 6811601507656744425, align 8
@var_7 = global i64 9067224066152263289, align 8
@var_8 = global i64 -2749471690871548383, align 8
@var_9 = global i64 -7896345560573941889, align 8
@var_10 = global i8 49, align 1
@var_11 = global i8 -114, align 1
@var_12 = global i8 0, align 1
@var_13 = global i64 -8199257619336957460, align 8
@var_14 = global i32 1330335270, align 4
@var_15 = global i32 -1711082008, align 4
@var_16 = global i64 -5539199402212913883, align 8
@var_17 = global i8 0, align 1
@var_19 = global i8 127, align 1
@zero = global i32 0, align 4
@arr_0 = common global [10 x [10 x i64]] zeroinitializer, align 16
@arr_1 = common global [10 x i8] zeroinitializer, align 1
@arr_2 = common global [10 x i8] zeroinitializer, align 1
@arr_3 = common global [10 x [10 x i8]] zeroinitializer, align 16
@arr_6 = common global [20 x i8] zeroinitializer, align 16
@arr_12 = common global [22 x i32] zeroinitializer, align 16
@arr_13 = common global [22 x [22 x i64]] zeroinitializer, align 16
@arr_15 = common global [22 x i8] zeroinitializer, align 16
@.str = private unnamed_addr constant [6 x i8] c"%llu\0A\00", align 1
@var_20 = global i8 -35, align 1
@var_21 = global i8 0, align 1
@var_22 = global i64 4860369896945684251, align 8
@var_23 = global i64 -2187617610345478494, align 8
@var_24 = global i8 0, align 1
@var_25 = global i64 -2718420653173790527, align 8
@var_26 = global i8 -90, align 1
@arr_5 = common global [10 x [10 x i8]] zeroinitializer, align 16
@var_27 = global i64 574410703128043639, align 8
@var_28 = global i8 29, align 1
@var_29 = global i64 -4589844211089081597, align 8
@var_30 = global i8 -79, align 1
@var_31 = global i8 -61, align 1
@var_32 = global i8 0, align 1
@var_33 = global i8 109, align 1
@var_34 = global i8 -61, align 1
@var_35 = global i8 34, align 1
@var_36 = global i64 -4227284126736062811, align 8
@var_37 = global i64 -2929283376140271842, align 8
@var_38 = global i64 -6960528739343822845, align 8
@var_39 = global i8 1, align 1
@arr_18 = common global [22 x [22 x [22 x i8]]] zeroinitializer, align 16
@var_40 = global i8 6, align 1
@var_41 = global i64 3083595004254887777, align 8

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @hash(ptr %0, i64 %1) #0 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %4, align 8
  %6 = add i64 %5, 2654435769
  %7 = load ptr, ptr %3, align 8
  %8 = load i64, ptr %7, align 8
  %9 = shl i64 %8, 6
  %10 = add i64 %6, %9
  %11 = load ptr, ptr %3, align 8
  %12 = load i64, ptr %11, align 8
  %13 = lshr i64 %12, 2
  %14 = add i64 %10, %13
  %15 = load ptr, ptr %3, align 8
  %16 = load i64, ptr %15, align 8
  %17 = xor i64 %16, %14
  store i64 %17, ptr %15, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @init() #0 {
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i64, align 8
  %10 = alloca i64, align 8
  %11 = alloca i64, align 8
  %12 = alloca i64, align 8
  %13 = alloca i64, align 8
  %14 = alloca i64, align 8
  %15 = alloca i64, align 8
  %16 = alloca i64, align 8
  store i64 0, ptr %1, align 8
  br label %17

17:                                               ; preds = %33, %0
  %18 = load i64, ptr %1, align 8
  %19 = icmp ult i64 %18, 10
  br i1 %19, label %20, label %36

20:                                               ; preds = %17
  store i64 0, ptr %2, align 8
  br label %21

21:                                               ; preds = %29, %20
  %22 = load i64, ptr %2, align 8
  %23 = icmp ult i64 %22, 10
  br i1 %23, label %24, label %32

24:                                               ; preds = %21
  %25 = load i64, ptr %1, align 8
  %26 = getelementptr inbounds [10 x [10 x i64]], ptr @arr_0, i64 0, i64 %25
  %27 = load i64, ptr %2, align 8
  %28 = getelementptr inbounds [10 x i64], ptr %26, i64 0, i64 %27
  store i64 3187310603059834283, ptr %28, align 8
  br label %29

29:                                               ; preds = %24
  %30 = load i64, ptr %2, align 8
  %31 = add i64 %30, 1
  store i64 %31, ptr %2, align 8
  br label %21, !llvm.loop !4

32:                                               ; preds = %21
  br label %33

33:                                               ; preds = %32
  %34 = load i64, ptr %1, align 8
  %35 = add i64 %34, 1
  store i64 %35, ptr %1, align 8
  br label %17, !llvm.loop !6

36:                                               ; preds = %17
  store i64 0, ptr %3, align 8
  br label %37

37:                                               ; preds = %43, %36
  %38 = load i64, ptr %3, align 8
  %39 = icmp ult i64 %38, 10
  br i1 %39, label %40, label %46

40:                                               ; preds = %37
  %41 = load i64, ptr %3, align 8
  %42 = getelementptr inbounds [10 x i8], ptr @arr_1, i64 0, i64 %41
  store i8 1, ptr %42, align 1
  br label %43

43:                                               ; preds = %40
  %44 = load i64, ptr %3, align 8
  %45 = add i64 %44, 1
  store i64 %45, ptr %3, align 8
  br label %37, !llvm.loop !7

46:                                               ; preds = %37
  store i64 0, ptr %4, align 8
  br label %47

47:                                               ; preds = %53, %46
  %48 = load i64, ptr %4, align 8
  %49 = icmp ult i64 %48, 10
  br i1 %49, label %50, label %56

50:                                               ; preds = %47
  %51 = load i64, ptr %4, align 8
  %52 = getelementptr inbounds [10 x i8], ptr @arr_2, i64 0, i64 %51
  store i8 1, ptr %52, align 1
  br label %53

53:                                               ; preds = %50
  %54 = load i64, ptr %4, align 8
  %55 = add i64 %54, 1
  store i64 %55, ptr %4, align 8
  br label %47, !llvm.loop !8

56:                                               ; preds = %47
  store i64 0, ptr %5, align 8
  br label %57

57:                                               ; preds = %73, %56
  %58 = load i64, ptr %5, align 8
  %59 = icmp ult i64 %58, 10
  br i1 %59, label %60, label %76

60:                                               ; preds = %57
  store i64 0, ptr %6, align 8
  br label %61

61:                                               ; preds = %69, %60
  %62 = load i64, ptr %6, align 8
  %63 = icmp ult i64 %62, 10
  br i1 %63, label %64, label %72

64:                                               ; preds = %61
  %65 = load i64, ptr %5, align 8
  %66 = getelementptr inbounds [10 x [10 x i8]], ptr @arr_3, i64 0, i64 %65
  %67 = load i64, ptr %6, align 8
  %68 = getelementptr inbounds [10 x i8], ptr %66, i64 0, i64 %67
  store i8 24, ptr %68, align 1
  br label %69

69:                                               ; preds = %64
  %70 = load i64, ptr %6, align 8
  %71 = add i64 %70, 1
  store i64 %71, ptr %6, align 8
  br label %61, !llvm.loop !9

72:                                               ; preds = %61
  br label %73

73:                                               ; preds = %72
  %74 = load i64, ptr %5, align 8
  %75 = add i64 %74, 1
  store i64 %75, ptr %5, align 8
  br label %57, !llvm.loop !10

76:                                               ; preds = %57
  store i64 0, ptr %7, align 8
  br label %77

77:                                               ; preds = %83, %76
  %78 = load i64, ptr %7, align 8
  %79 = icmp ult i64 %78, 20
  br i1 %79, label %80, label %86

80:                                               ; preds = %77
  %81 = load i64, ptr %7, align 8
  %82 = getelementptr inbounds [20 x i8], ptr @arr_6, i64 0, i64 %81
  store i8 -21, ptr %82, align 1
  br label %83

83:                                               ; preds = %80
  %84 = load i64, ptr %7, align 8
  %85 = add i64 %84, 1
  store i64 %85, ptr %7, align 8
  br label %77, !llvm.loop !11

86:                                               ; preds = %77
  store i64 0, ptr %8, align 8
  br label %87

87:                                               ; preds = %93, %86
  %88 = load i64, ptr %8, align 8
  %89 = icmp ult i64 %88, 22
  br i1 %89, label %90, label %96

90:                                               ; preds = %87
  %91 = load i64, ptr %8, align 8
  %92 = getelementptr inbounds [22 x i32], ptr @arr_12, i64 0, i64 %91
  store i32 -1419371658, ptr %92, align 4
  br label %93

93:                                               ; preds = %90
  %94 = load i64, ptr %8, align 8
  %95 = add i64 %94, 1
  store i64 %95, ptr %8, align 8
  br label %87, !llvm.loop !12

96:                                               ; preds = %87
  store i64 0, ptr %9, align 8
  br label %97

97:                                               ; preds = %113, %96
  %98 = load i64, ptr %9, align 8
  %99 = icmp ult i64 %98, 22
  br i1 %99, label %100, label %116

100:                                              ; preds = %97
  store i64 0, ptr %10, align 8
  br label %101

101:                                              ; preds = %109, %100
  %102 = load i64, ptr %10, align 8
  %103 = icmp ult i64 %102, 22
  br i1 %103, label %104, label %112

104:                                              ; preds = %101
  %105 = load i64, ptr %9, align 8
  %106 = getelementptr inbounds [22 x [22 x i64]], ptr @arr_13, i64 0, i64 %105
  %107 = load i64, ptr %10, align 8
  %108 = getelementptr inbounds [22 x i64], ptr %106, i64 0, i64 %107
  store i64 -7290541985839421487, ptr %108, align 8
  br label %109

109:                                              ; preds = %104
  %110 = load i64, ptr %10, align 8
  %111 = add i64 %110, 1
  store i64 %111, ptr %10, align 8
  br label %101, !llvm.loop !13

112:                                              ; preds = %101
  br label %113

113:                                              ; preds = %112
  %114 = load i64, ptr %9, align 8
  %115 = add i64 %114, 1
  store i64 %115, ptr %9, align 8
  br label %97, !llvm.loop !14

116:                                              ; preds = %97
  store i64 0, ptr %11, align 8
  br label %117

117:                                              ; preds = %129, %116
  %118 = load i64, ptr %11, align 8
  %119 = icmp ult i64 %118, 22
  br i1 %119, label %120, label %132

120:                                              ; preds = %117
  %121 = load i64, ptr %11, align 8
  %122 = urem i64 %121, 2
  %123 = icmp eq i64 %122, 0
  %124 = zext i1 %123 to i64
  %125 = select i1 %123, i32 97, i32 121
  %126 = trunc i32 %125 to i8
  %127 = load i64, ptr %11, align 8
  %128 = getelementptr inbounds [22 x i8], ptr @arr_15, i64 0, i64 %127
  store i8 %126, ptr %128, align 1
  br label %129

129:                                              ; preds = %120
  %130 = load i64, ptr %11, align 8
  %131 = add i64 %130, 1
  store i64 %131, ptr %11, align 8
  br label %117, !llvm.loop !15

132:                                              ; preds = %117
  store i64 0, ptr %12, align 8
  br label %133

133:                                              ; preds = %156, %132
  %134 = load i64, ptr %12, align 8
  %135 = icmp ult i64 %134, 10
  br i1 %135, label %136, label %159

136:                                              ; preds = %133
  store i64 0, ptr %13, align 8
  br label %137

137:                                              ; preds = %152, %136
  %138 = load i64, ptr %13, align 8
  %139 = icmp ult i64 %138, 10
  br i1 %139, label %140, label %155

140:                                              ; preds = %137
  %141 = load i64, ptr %12, align 8
  %142 = urem i64 %141, 2
  %143 = icmp eq i64 %142, 0
  %144 = zext i1 %143 to i64
  %145 = select i1 %143, i32 0, i32 1
  %146 = icmp ne i32 %145, 0
  %147 = load i64, ptr %12, align 8
  %148 = getelementptr inbounds [10 x [10 x i8]], ptr @arr_5, i64 0, i64 %147
  %149 = load i64, ptr %13, align 8
  %150 = getelementptr inbounds [10 x i8], ptr %148, i64 0, i64 %149
  %151 = zext i1 %146 to i8
  store i8 %151, ptr %150, align 1
  br label %152

152:                                              ; preds = %140
  %153 = load i64, ptr %13, align 8
  %154 = add i64 %153, 1
  store i64 %154, ptr %13, align 8
  br label %137, !llvm.loop !16

155:                                              ; preds = %137
  br label %156

156:                                              ; preds = %155
  %157 = load i64, ptr %12, align 8
  %158 = add i64 %157, 1
  store i64 %158, ptr %12, align 8
  br label %133, !llvm.loop !17

159:                                              ; preds = %133
  store i64 0, ptr %14, align 8
  br label %160

160:                                              ; preds = %192, %159
  %161 = load i64, ptr %14, align 8
  %162 = icmp ult i64 %161, 22
  br i1 %162, label %163, label %195

163:                                              ; preds = %160
  store i64 0, ptr %15, align 8
  br label %164

164:                                              ; preds = %188, %163
  %165 = load i64, ptr %15, align 8
  %166 = icmp ult i64 %165, 22
  br i1 %166, label %167, label %191

167:                                              ; preds = %164
  store i64 0, ptr %16, align 8
  br label %168

168:                                              ; preds = %184, %167
  %169 = load i64, ptr %16, align 8
  %170 = icmp ult i64 %169, 22
  br i1 %170, label %171, label %187

171:                                              ; preds = %168
  %172 = load i64, ptr %15, align 8
  %173 = urem i64 %172, 2
  %174 = icmp eq i64 %173, 0
  %175 = zext i1 %174 to i64
  %176 = select i1 %174, i32 24, i32 103
  %177 = trunc i32 %176 to i8
  %178 = load i64, ptr %14, align 8
  %179 = getelementptr inbounds [22 x [22 x [22 x i8]]], ptr @arr_18, i64 0, i64 %178
  %180 = load i64, ptr %15, align 8
  %181 = getelementptr inbounds [22 x [22 x i8]], ptr %179, i64 0, i64 %180
  %182 = load i64, ptr %16, align 8
  %183 = getelementptr inbounds [22 x i8], ptr %181, i64 0, i64 %182
  store i8 %177, ptr %183, align 1
  br label %184

184:                                              ; preds = %171
  %185 = load i64, ptr %16, align 8
  %186 = add i64 %185, 1
  store i64 %186, ptr %16, align 8
  br label %168, !llvm.loop !18

187:                                              ; preds = %168
  br label %188

188:                                              ; preds = %187
  %189 = load i64, ptr %15, align 8
  %190 = add i64 %189, 1
  store i64 %190, ptr %15, align 8
  br label %164, !llvm.loop !19

191:                                              ; preds = %164
  br label %192

192:                                              ; preds = %191
  %193 = load i64, ptr %14, align 8
  %194 = add i64 %193, 1
  store i64 %194, ptr %14, align 8
  br label %160, !llvm.loop !20

195:                                              ; preds = %160
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @checksum() #0 {
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = load i8, ptr @var_20, align 1
  %7 = zext i8 %6 to i64
  call void @hash(ptr @seed, i64 %7)
  %8 = load i8, ptr @var_21, align 1
  %9 = trunc i8 %8 to i1
  %10 = zext i1 %9 to i64
  call void @hash(ptr @seed, i64 %10)
  %11 = load i64, ptr @var_22, align 8
  call void @hash(ptr @seed, i64 %11)
  %12 = load i64, ptr @var_23, align 8
  call void @hash(ptr @seed, i64 %12)
  %13 = load i8, ptr @var_24, align 1
  %14 = trunc i8 %13 to i1
  %15 = zext i1 %14 to i64
  call void @hash(ptr @seed, i64 %15)
  %16 = load i64, ptr @var_25, align 8
  call void @hash(ptr @seed, i64 %16)
  %17 = load i8, ptr @var_26, align 1
  %18 = zext i8 %17 to i64
  call void @hash(ptr @seed, i64 %18)
  %19 = load i64, ptr @var_27, align 8
  call void @hash(ptr @seed, i64 %19)
  %20 = load i8, ptr @var_28, align 1
  %21 = zext i8 %20 to i64
  call void @hash(ptr @seed, i64 %21)
  %22 = load i64, ptr @var_29, align 8
  call void @hash(ptr @seed, i64 %22)
  %23 = load i8, ptr @var_30, align 1
  %24 = sext i8 %23 to i64
  call void @hash(ptr @seed, i64 %24)
  %25 = load i8, ptr @var_31, align 1
  %26 = sext i8 %25 to i64
  call void @hash(ptr @seed, i64 %26)
  %27 = load i8, ptr @var_32, align 1
  %28 = trunc i8 %27 to i1
  %29 = zext i1 %28 to i64
  call void @hash(ptr @seed, i64 %29)
  %30 = load i8, ptr @var_33, align 1
  %31 = sext i8 %30 to i64
  call void @hash(ptr @seed, i64 %31)
  %32 = load i8, ptr @var_34, align 1
  %33 = zext i8 %32 to i64
  call void @hash(ptr @seed, i64 %33)
  %34 = load i8, ptr @var_35, align 1
  %35 = sext i8 %34 to i64
  call void @hash(ptr @seed, i64 %35)
  %36 = load i64, ptr @var_36, align 8
  call void @hash(ptr @seed, i64 %36)
  %37 = load i64, ptr @var_37, align 8
  call void @hash(ptr @seed, i64 %37)
  %38 = load i64, ptr @var_38, align 8
  call void @hash(ptr @seed, i64 %38)
  %39 = load i8, ptr @var_39, align 1
  %40 = trunc i8 %39 to i1
  %41 = zext i1 %40 to i64
  call void @hash(ptr @seed, i64 %41)
  %42 = load i8, ptr @var_40, align 1
  %43 = sext i8 %42 to i64
  call void @hash(ptr @seed, i64 %43)
  %44 = load i64, ptr @var_41, align 8
  call void @hash(ptr @seed, i64 %44)
  store i64 0, ptr %1, align 8
  br label %45

45:                                               ; preds = %64, %0
  %46 = load i64, ptr %1, align 8
  %47 = icmp ult i64 %46, 10
  br i1 %47, label %48, label %67

48:                                               ; preds = %45
  store i64 0, ptr %2, align 8
  br label %49

49:                                               ; preds = %60, %48
  %50 = load i64, ptr %2, align 8
  %51 = icmp ult i64 %50, 10
  br i1 %51, label %52, label %63

52:                                               ; preds = %49
  %53 = load i64, ptr %1, align 8
  %54 = getelementptr inbounds [10 x [10 x i8]], ptr @arr_5, i64 0, i64 %53
  %55 = load i64, ptr %2, align 8
  %56 = getelementptr inbounds [10 x i8], ptr %54, i64 0, i64 %55
  %57 = load i8, ptr %56, align 1
  %58 = trunc i8 %57 to i1
  %59 = zext i1 %58 to i64
  call void @hash(ptr @seed, i64 %59)
  br label %60

60:                                               ; preds = %52
  %61 = load i64, ptr %2, align 8
  %62 = add i64 %61, 1
  store i64 %62, ptr %2, align 8
  br label %49, !llvm.loop !21

63:                                               ; preds = %49
  br label %64

64:                                               ; preds = %63
  %65 = load i64, ptr %1, align 8
  %66 = add i64 %65, 1
  store i64 %66, ptr %1, align 8
  br label %45, !llvm.loop !22

67:                                               ; preds = %45
  store i64 0, ptr %3, align 8
  br label %68

68:                                               ; preds = %96, %67
  %69 = load i64, ptr %3, align 8
  %70 = icmp ult i64 %69, 22
  br i1 %70, label %71, label %99

71:                                               ; preds = %68
  store i64 0, ptr %4, align 8
  br label %72

72:                                               ; preds = %92, %71
  %73 = load i64, ptr %4, align 8
  %74 = icmp ult i64 %73, 22
  br i1 %74, label %75, label %95

75:                                               ; preds = %72
  store i64 0, ptr %5, align 8
  br label %76

76:                                               ; preds = %88, %75
  %77 = load i64, ptr %5, align 8
  %78 = icmp ult i64 %77, 22
  br i1 %78, label %79, label %91

79:                                               ; preds = %76
  %80 = load i64, ptr %3, align 8
  %81 = getelementptr inbounds [22 x [22 x [22 x i8]]], ptr @arr_18, i64 0, i64 %80
  %82 = load i64, ptr %4, align 8
  %83 = getelementptr inbounds [22 x [22 x i8]], ptr %81, i64 0, i64 %82
  %84 = load i64, ptr %5, align 8
  %85 = getelementptr inbounds [22 x i8], ptr %83, i64 0, i64 %84
  %86 = load i8, ptr %85, align 1
  %87 = sext i8 %86 to i64
  call void @hash(ptr @seed, i64 %87)
  br label %88

88:                                               ; preds = %79
  %89 = load i64, ptr %5, align 8
  %90 = add i64 %89, 1
  store i64 %90, ptr %5, align 8
  br label %76, !llvm.loop !23

91:                                               ; preds = %76
  br label %92

92:                                               ; preds = %91
  %93 = load i64, ptr %4, align 8
  %94 = add i64 %93, 1
  store i64 %94, ptr %4, align 8
  br label %72, !llvm.loop !24

95:                                               ; preds = %72
  br label %96

96:                                               ; preds = %95
  %97 = load i64, ptr %3, align 8
  %98 = add i64 %97, 1
  store i64 %98, ptr %3, align 8
  br label %68, !llvm.loop !25

99:                                               ; preds = %68
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 {
  call void @init()
  %1 = load i64, ptr @var_0, align 8
  %2 = load i8, ptr @var_1, align 1
  %3 = load i8, ptr @var_2, align 1
  %4 = trunc i8 %3 to i1
  %5 = load i64, ptr @var_3, align 8
  %6 = load i8, ptr @var_4, align 1
  %7 = trunc i8 %6 to i1
  %8 = load i8, ptr @var_5, align 1
  %9 = load i64, ptr @var_6, align 8
  %10 = load i64, ptr @var_7, align 8
  %11 = load i64, ptr @var_8, align 8
  %12 = load i64, ptr @var_9, align 8
  %13 = load i8, ptr @var_10, align 1
  %14 = load i8, ptr @var_11, align 1
  %15 = load i8, ptr @var_12, align 1
  %16 = trunc i8 %15 to i1
  %17 = load i64, ptr @var_13, align 8
  %18 = load i32, ptr @var_14, align 4
  %19 = load i32, ptr @var_15, align 4
  %20 = load i64, ptr @var_16, align 8
  %21 = load i8, ptr @var_17, align 1
  %22 = trunc i8 %21 to i1
  %23 = load i8, ptr @var_19, align 1
  %24 = load i32, ptr @zero, align 4
  call void @test(i64 %1, i8 signext %2, i1 zeroext %4, i64 %5, i1 zeroext %7, i8 zeroext %8, i64 %9, i64 %10, i64 %11, i64 %12, i8 signext %13, i8 signext %14, i1 zeroext %16, i64 %17, i32 %18, i32 %19, i64 %20, i1 zeroext %22, i8 zeroext %23, i32 %24, ptr @arr_0, ptr @arr_1, ptr @arr_2, ptr @arr_3, ptr @arr_6, ptr @arr_12, ptr @arr_13, ptr @arr_15)
  call void @checksum()
  %25 = load i64, ptr @seed, align 8
  %26 = call i32 (ptr, ...) @printf(ptr @.str, i64 %25)
  ret i32 0
}

declare i32 @printf(ptr, ...) #1

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @test(i64 %0, i8 signext %1, i1 zeroext %2, i64 %3, i1 zeroext %4, i8 zeroext %5, i64 %6, i64 %7, i64 %8, i64 %9, i8 signext %10, i8 signext %11, i1 zeroext %12, i64 %13, i32 %14, i32 %15, i64 %16, i1 zeroext %17, i8 zeroext %18, i32 %19, ptr %20, ptr %21, ptr %22, ptr %23, ptr %24, ptr %25, ptr %26, ptr %27) #0 {
  %29 = alloca i64, align 8
  %30 = alloca i8, align 1
  %31 = alloca i8, align 1
  %32 = alloca i64, align 8
  %33 = alloca i8, align 1
  %34 = alloca i8, align 1
  %35 = alloca i64, align 8
  %36 = alloca i64, align 8
  %37 = alloca i64, align 8
  %38 = alloca i64, align 8
  %39 = alloca i8, align 1
  %40 = alloca i8, align 1
  %41 = alloca i8, align 1
  %42 = alloca i64, align 8
  %43 = alloca i32, align 4
  %44 = alloca i32, align 4
  %45 = alloca i64, align 8
  %46 = alloca i8, align 1
  %47 = alloca i8, align 1
  %48 = alloca i32, align 4
  %49 = alloca ptr, align 8
  %50 = alloca ptr, align 8
  %51 = alloca ptr, align 8
  %52 = alloca ptr, align 8
  %53 = alloca ptr, align 8
  %54 = alloca ptr, align 8
  %55 = alloca ptr, align 8
  %56 = alloca ptr, align 8
  %57 = alloca i32, align 4
  %58 = alloca i32, align 4
  %59 = alloca i32, align 4
  %60 = alloca i8, align 1
  %61 = alloca i64, align 8
  %62 = alloca i64, align 8
  %63 = alloca i64, align 8
  %64 = alloca i8, align 1
  %65 = alloca i64, align 8
  %66 = alloca i64, align 8
  %67 = alloca i64, align 8
  %68 = alloca i64, align 8
  %69 = alloca i64, align 8
  %70 = alloca i8, align 1
  %71 = alloca i8, align 1
  %72 = alloca i32, align 4
  %73 = alloca i64, align 8
  %74 = alloca i64, align 8
  %75 = alloca i8, align 1
  %76 = alloca i32, align 4
  %77 = alloca i32, align 4
  %78 = alloca i32, align 4
  %79 = alloca i64, align 8
  %80 = alloca i64, align 8
  %81 = alloca i64, align 8
  %82 = alloca i64, align 8
  %83 = alloca i64, align 8
  %84 = alloca i64, align 8
  %85 = alloca i64, align 8
  %86 = alloca i64, align 8
  %87 = alloca i64, align 8
  %88 = alloca i64, align 8
  %89 = alloca i64, align 8
  %90 = alloca i64, align 8
  %91 = alloca i64, align 8
  %92 = alloca i8, align 1
  %93 = alloca i8, align 1
  %94 = alloca i32, align 4
  %95 = alloca i32, align 4
  %96 = alloca i32, align 4
  %97 = alloca i8, align 1
  %98 = alloca i32, align 4
  %99 = alloca i32, align 4
  %100 = alloca i32, align 4
  %101 = alloca i8, align 1
  %102 = alloca i8, align 1
  %103 = alloca i32, align 4
  %104 = alloca i32, align 4
  %105 = alloca i32, align 4
  %106 = alloca i64, align 8
  %107 = alloca i64, align 8
  %108 = alloca i64, align 8
  %109 = alloca i64, align 8
  %110 = alloca i64, align 8
  %111 = alloca i64, align 8
  %112 = alloca i64, align 8
  %113 = alloca i64, align 8
  %114 = alloca i64, align 8
  store i64 %0, ptr %29, align 8
  store i8 %1, ptr %30, align 1
  %115 = zext i1 %2 to i8
  store i8 %115, ptr %31, align 1
  store i64 %3, ptr %32, align 8
  %116 = zext i1 %4 to i8
  store i8 %116, ptr %33, align 1
  store i8 %5, ptr %34, align 1
  store i64 %6, ptr %35, align 8
  store i64 %7, ptr %36, align 8
  store i64 %8, ptr %37, align 8
  store i64 %9, ptr %38, align 8
  store i8 %10, ptr %39, align 1
  store i8 %11, ptr %40, align 1
  %117 = zext i1 %12 to i8
  store i8 %117, ptr %41, align 1
  store i64 %13, ptr %42, align 8
  store i32 %14, ptr %43, align 4
  store i32 %15, ptr %44, align 4
  store i64 %16, ptr %45, align 8
  %118 = zext i1 %17 to i8
  store i8 %118, ptr %46, align 1
  store i8 %18, ptr %47, align 1
  store i32 %19, ptr %48, align 4
  store ptr %20, ptr %49, align 8
  store ptr %21, ptr %50, align 8
  store ptr %22, ptr %51, align 8
  store ptr %23, ptr %52, align 8
  store ptr %24, ptr %53, align 8
  store ptr %25, ptr %54, align 8
  store ptr %26, ptr %55, align 8
  store ptr %27, ptr %56, align 8
  store i32 -34, ptr %57, align 4
  store i32 0, ptr %58, align 4
  %119 = load i32, ptr %57, align 4
  %120 = load i32, ptr %58, align 4
  %121 = icmp slt i32 %119, %120
  br i1 %121, label %122, label %124

122:                                              ; preds = %28
  %123 = load i32, ptr %57, align 4
  br label %126

124:                                              ; preds = %28
  %125 = load i32, ptr %58, align 4
  br label %126

126:                                              ; preds = %124, %122
  %127 = phi i32 [ %123, %122 ], [ %125, %124 ]
  store i32 %127, ptr %59, align 4
  %128 = load i32, ptr %59, align 4
  %129 = icmp ne i32 %128, 0
  br i1 %129, label %130, label %141

130:                                              ; preds = %126
  %131 = load i8, ptr %30, align 1
  %132 = sext i8 %131 to i32
  %133 = sext i32 %132 to i64
  %134 = load i64, ptr %37, align 8
  %135 = sdiv i64 %133, %134
  %136 = load i8, ptr %31, align 1
  %137 = trunc i8 %136 to i1
  %138 = zext i1 %137 to i32
  %139 = sext i32 %138 to i64
  %140 = add nsw i64 %135, %139
  br label %143

141:                                              ; preds = %126
  %142 = load i64, ptr %37, align 8
  br label %143

143:                                              ; preds = %141, %130
  %144 = phi i64 [ %140, %130 ], [ %142, %141 ]
  %145 = icmp ne i64 %144, 0
  br i1 %145, label %146, label %406

146:                                              ; preds = %143
  %147 = load i64, ptr %35, align 8
  %148 = icmp ne i64 %147, 0
  br i1 %148, label %149, label %161

149:                                              ; preds = %146
  %150 = load i32, ptr %44, align 4
  %151 = sdiv i32 127, %150
  %152 = icmp ne i32 %151, 0
  br i1 %152, label %153, label %158

153:                                              ; preds = %149
  %154 = load i8, ptr %33, align 1
  %155 = trunc i8 %154 to i1
  %156 = zext i1 %155 to i32
  %157 = sext i32 %156 to i64
  br label %159

158:                                              ; preds = %149
  br label %159

159:                                              ; preds = %158, %153
  %160 = phi i64 [ %157, %153 ], [ 1, %158 ]
  br label %163

161:                                              ; preds = %146
  %162 = load i64, ptr %36, align 8
  br label %163

163:                                              ; preds = %161, %159
  %164 = phi i64 [ %160, %159 ], [ %162, %161 ]
  %165 = icmp ne i64 %164, 0
  %166 = zext i1 %165 to i32
  %167 = sub nsw i32 %166, 1
  %168 = icmp ne i32 %167, 0
  %169 = zext i1 %168 to i8
  store i8 %169, ptr %60, align 1
  br label %170

170:                                              ; preds = %234, %163
  %171 = load i8, ptr %60, align 1
  %172 = trunc i8 %171 to i1
  %173 = zext i1 %172 to i32
  %174 = load i8, ptr %40, align 1
  %175 = icmp ne i8 %174, 0
  %176 = zext i1 %175 to i32
  %177 = icmp slt i32 %173, %176
  br i1 %177, label %178, label %241

178:                                              ; preds = %170
  %179 = load i64, ptr %36, align 8
  %180 = trunc i64 %179 to i8
  %181 = zext i8 %180 to i32
  %182 = load i8, ptr @var_20, align 1
  %183 = zext i8 %182 to i32
  %184 = add nsw i32 %183, %181
  %185 = trunc i32 %184 to i8
  store i8 %185, ptr @var_20, align 1
  %186 = load i8, ptr %41, align 1
  %187 = trunc i8 %186 to i1
  %188 = zext i1 %187 to i64
  %189 = select i1 %187, i32 103, i32 127
  %190 = icmp ne i32 %189, 0
  br i1 %190, label %191, label %192

191:                                              ; preds = %178
  br label %197

192:                                              ; preds = %178
  %193 = load i8, ptr %46, align 1
  %194 = trunc i8 %193 to i1
  %195 = zext i1 %194 to i32
  %196 = sext i32 %195 to i64
  br label %197

197:                                              ; preds = %192, %191
  %198 = phi i64 [ -8743832625451505084, %191 ], [ %196, %192 ]
  %199 = mul nsw i64 -1, %198
  %200 = icmp ne i64 %199, 0
  %201 = zext i1 %200 to i8
  store i8 %201, ptr @var_21, align 1
  %202 = load i64, ptr @var_22, align 8
  store i64 %202, ptr %61, align 8
  %203 = load ptr, ptr %50, align 8
  %204 = load i8, ptr %60, align 1
  %205 = trunc i8 %204 to i1
  %206 = zext i1 %205 to i64
  %207 = getelementptr inbounds i8, ptr %203, i64 %206
  %208 = load i8, ptr %207, align 1
  %209 = trunc i8 %208 to i1
  %210 = zext i1 %209 to i32
  %211 = xor i32 %210, -1
  %212 = trunc i32 %211 to i8
  %213 = zext i8 %212 to i64
  store i64 %213, ptr %62, align 8
  %214 = load i64, ptr %61, align 8
  %215 = load i64, ptr %62, align 8
  %216 = icmp sgt i64 %214, %215
  br i1 %216, label %217, label %219

217:                                              ; preds = %197
  %218 = load i64, ptr %61, align 8
  br label %221

219:                                              ; preds = %197
  %220 = load i64, ptr %62, align 8
  br label %221

221:                                              ; preds = %219, %217
  %222 = phi i64 [ %218, %217 ], [ %220, %219 ]
  store i64 %222, ptr %63, align 8
  %223 = load i64, ptr %63, align 8
  store i64 %223, ptr @var_22, align 8
  %224 = load ptr, ptr %50, align 8
  %225 = load i8, ptr %60, align 1
  %226 = trunc i8 %225 to i1
  %227 = zext i1 %226 to i64
  %228 = getelementptr inbounds i8, ptr %224, i64 %227
  %229 = load i8, ptr %228, align 1
  %230 = trunc i8 %229 to i1
  %231 = xor i1 %230, true
  %232 = zext i1 %231 to i32
  %233 = sext i32 %232 to i64
  store i64 %233, ptr @var_23, align 8
  br label %234

234:                                              ; preds = %221
  %235 = load i8, ptr %60, align 1
  %236 = trunc i8 %235 to i1
  %237 = zext i1 %236 to i32
  %238 = add nsw i32 %237, 1
  %239 = icmp ne i32 %238, 0
  %240 = zext i1 %239 to i8
  store i8 %240, ptr %60, align 1
  br label %170, !llvm.loop !26

241:                                              ; preds = %170
  %242 = load i64, ptr %35, align 8
  %243 = icmp ne i64 %242, 0
  br i1 %243, label %244, label %256

244:                                              ; preds = %241
  %245 = load i32, ptr %44, align 4
  %246 = sdiv i32 127, %245
  %247 = icmp ne i32 %246, 0
  br i1 %247, label %248, label %253

248:                                              ; preds = %244
  %249 = load i8, ptr %33, align 1
  %250 = trunc i8 %249 to i1
  %251 = zext i1 %250 to i32
  %252 = sext i32 %251 to i64
  br label %254

253:                                              ; preds = %244
  br label %254

254:                                              ; preds = %253, %248
  %255 = phi i64 [ %252, %248 ], [ 1, %253 ]
  br label %258

256:                                              ; preds = %241
  %257 = load i64, ptr %36, align 8
  br label %258

258:                                              ; preds = %256, %254
  %259 = phi i64 [ %255, %254 ], [ %257, %256 ]
  %260 = icmp ne i64 %259, 0
  %261 = zext i1 %260 to i32
  %262 = sub nsw i32 %261, 1
  %263 = icmp ne i32 %262, 0
  %264 = zext i1 %263 to i8
  store i8 %264, ptr %64, align 1
  br label %265

265:                                              ; preds = %384, %258
  %266 = load i8, ptr %64, align 1
  %267 = trunc i8 %266 to i1
  %268 = zext i1 %267 to i32
  %269 = load i8, ptr %40, align 1
  %270 = icmp ne i8 %269, 0
  %271 = zext i1 %270 to i32
  %272 = icmp slt i32 %268, %271
  br i1 %272, label %273, label %391

273:                                              ; preds = %265
  %274 = load ptr, ptr %49, align 8
  %275 = getelementptr inbounds [10 x i64], ptr %274, i64 3
  %276 = getelementptr inbounds [10 x i64], ptr %275, i64 0, i64 1
  %277 = load i64, ptr %276, align 8
  %278 = icmp ne i64 %277, 0
  br i1 %278, label %279, label %289

279:                                              ; preds = %273
  %280 = load ptr, ptr %50, align 8
  %281 = load i8, ptr %64, align 1
  %282 = trunc i8 %281 to i1
  %283 = zext i1 %282 to i64
  %284 = getelementptr inbounds i8, ptr %280, i64 %283
  %285 = load i8, ptr %284, align 1
  %286 = trunc i8 %285 to i1
  %287 = zext i1 %286 to i32
  %288 = sext i32 %287 to i64
  br label %291

289:                                              ; preds = %273
  %290 = load i64, ptr %38, align 8
  br label %291

291:                                              ; preds = %289, %279
  %292 = phi i64 [ %288, %279 ], [ %290, %289 ]
  %293 = icmp ne i64 %292, 0
  %294 = zext i1 %293 to i8
  store i8 %294, ptr @var_24, align 1
  %295 = load ptr, ptr %51, align 8
  %296 = load i8, ptr %64, align 1
  %297 = trunc i8 %296 to i1
  %298 = zext i1 %297 to i64
  %299 = getelementptr inbounds i8, ptr %295, i64 %298
  %300 = load i8, ptr %299, align 1
  %301 = trunc i8 %300 to i1
  br i1 %301, label %302, label %383

302:                                              ; preds = %291
  %303 = load i64, ptr @var_25, align 8
  store i64 %303, ptr %65, align 8
  %304 = load ptr, ptr %52, align 8
  %305 = load i8, ptr %64, align 1
  %306 = trunc i8 %305 to i1
  %307 = zext i1 %306 to i64
  %308 = getelementptr inbounds [10 x i8], ptr %304, i64 %307
  %309 = load i8, ptr %64, align 1
  %310 = trunc i8 %309 to i1
  %311 = zext i1 %310 to i64
  %312 = getelementptr inbounds [10 x i8], ptr %308, i64 0, i64 %311
  %313 = load i8, ptr %312, align 1
  %314 = icmp ne i8 %313, 0
  br i1 %314, label %315, label %327

315:                                              ; preds = %302
  %316 = load ptr, ptr %52, align 8
  %317 = load i8, ptr %64, align 1
  %318 = trunc i8 %317 to i1
  %319 = zext i1 %318 to i64
  %320 = getelementptr inbounds [10 x i8], ptr %316, i64 %319
  %321 = load i8, ptr %64, align 1
  %322 = trunc i8 %321 to i1
  %323 = zext i1 %322 to i64
  %324 = getelementptr inbounds [10 x i8], ptr %320, i64 0, i64 %323
  %325 = load i8, ptr %324, align 1
  %326 = sext i8 %325 to i32
  br label %328

327:                                              ; preds = %302
  br label %328

328:                                              ; preds = %327, %315
  %329 = phi i32 [ %326, %315 ], [ 0, %327 ]
  %330 = sext i32 %329 to i64
  store i64 %330, ptr %66, align 8
  %331 = load i64, ptr %65, align 8
  %332 = load i64, ptr %66, align 8
  %333 = icmp ult i64 %331, %332
  br i1 %333, label %334, label %336

334:                                              ; preds = %328
  %335 = load i64, ptr %65, align 8
  br label %338

336:                                              ; preds = %328
  %337 = load i64, ptr %66, align 8
  br label %338

338:                                              ; preds = %336, %334
  %339 = phi i64 [ %335, %334 ], [ %337, %336 ]
  store i64 %339, ptr %67, align 8
  %340 = load i64, ptr %67, align 8
  store i64 %340, ptr @var_25, align 8
  %341 = load ptr, ptr %49, align 8
  %342 = load i8, ptr %64, align 1
  %343 = trunc i8 %342 to i1
  %344 = zext i1 %343 to i64
  %345 = getelementptr inbounds [10 x i64], ptr %341, i64 %344
  %346 = load i8, ptr %64, align 1
  %347 = trunc i8 %346 to i1
  %348 = zext i1 %347 to i64
  %349 = getelementptr inbounds [10 x i64], ptr %345, i64 0, i64 %348
  %350 = load i64, ptr %349, align 8
  %351 = icmp ne i64 %350, 0
  br i1 %351, label %352, label %363

352:                                              ; preds = %338
  %353 = load ptr, ptr %49, align 8
  %354 = load i8, ptr %64, align 1
  %355 = trunc i8 %354 to i1
  %356 = zext i1 %355 to i64
  %357 = getelementptr inbounds [10 x i64], ptr %353, i64 %356
  %358 = load i8, ptr %64, align 1
  %359 = trunc i8 %358 to i1
  %360 = zext i1 %359 to i64
  %361 = getelementptr inbounds [10 x i64], ptr %357, i64 0, i64 %360
  %362 = load i64, ptr %361, align 8
  br label %367

363:                                              ; preds = %338
  %364 = load i8, ptr %40, align 1
  %365 = sext i8 %364 to i32
  %366 = sext i32 %365 to i64
  br label %367

367:                                              ; preds = %363, %352
  %368 = phi i64 [ %362, %352 ], [ %366, %363 ]
  %369 = trunc i64 %368 to i8
  %370 = zext i8 %369 to i32
  %371 = load i8, ptr @var_26, align 1
  %372 = zext i8 %371 to i32
  %373 = xor i32 %372, %370
  %374 = trunc i32 %373 to i8
  store i8 %374, ptr @var_26, align 1
  %375 = load i8, ptr %64, align 1
  %376 = trunc i8 %375 to i1
  %377 = zext i1 %376 to i64
  %378 = getelementptr inbounds [10 x [10 x i8]], ptr @arr_5, i64 0, i64 %377
  %379 = load i8, ptr %64, align 1
  %380 = trunc i8 %379 to i1
  %381 = zext i1 %380 to i64
  %382 = getelementptr inbounds [10 x i8], ptr %378, i64 0, i64 %381
  store i8 1, ptr %382, align 1
  br label %383

383:                                              ; preds = %367, %291
  br label %384

384:                                              ; preds = %383
  %385 = load i8, ptr %64, align 1
  %386 = trunc i8 %385 to i1
  %387 = zext i1 %386 to i32
  %388 = add nsw i32 %387, 1
  %389 = icmp ne i32 %388, 0
  %390 = zext i1 %389 to i8
  store i8 %390, ptr %64, align 1
  br label %265, !llvm.loop !27

391:                                              ; preds = %265
  %392 = load i8, ptr %34, align 1
  %393 = icmp ne i8 %392, 0
  br i1 %393, label %394, label %397

394:                                              ; preds = %391
  %395 = load i8, ptr %30, align 1
  %396 = sext i8 %395 to i32
  br label %400

397:                                              ; preds = %391
  %398 = load i8, ptr %30, align 1
  %399 = sext i8 %398 to i32
  br label %400

400:                                              ; preds = %397, %394
  %401 = phi i32 [ %396, %394 ], [ %399, %397 ]
  %402 = sext i32 %401 to i64
  %403 = xor i64 1399754803113188818, %402
  %404 = trunc i64 %403 to i8
  %405 = sext i8 %404 to i64
  store i64 %405, ptr @var_27, align 8
  br label %406

406:                                              ; preds = %400, %143
  %407 = load i64, ptr %37, align 8
  %408 = xor i64 %407, -1
  %409 = xor i64 %408, -1
  %410 = icmp ne i64 %409, 0
  br i1 %410, label %412, label %411

411:                                              ; preds = %406
  br i1 true, label %412, label %429

412:                                              ; preds = %411, %406
  %413 = load i64, ptr %38, align 8
  %414 = trunc i64 %413 to i8
  %415 = zext i8 %414 to i32
  %416 = load i8, ptr @var_28, align 1
  %417 = zext i8 %416 to i32
  %418 = add nsw i32 %417, %415
  %419 = trunc i32 %418 to i8
  store i8 %419, ptr @var_28, align 1
  %420 = load i32, ptr %44, align 4
  %421 = sext i32 %420 to i64
  %422 = load i64, ptr @var_29, align 8
  %423 = and i64 %422, %421
  store i64 %423, ptr @var_29, align 8
  %424 = load i64, ptr %38, align 8
  %425 = trunc i64 %424 to i8
  store i8 %425, ptr @var_30, align 1
  %426 = load i8, ptr %30, align 1
  %427 = sext i8 %426 to i64
  %428 = trunc i64 %427 to i8
  store i8 %428, ptr @var_31, align 1
  br label %553

429:                                              ; preds = %411
  %430 = load i64, ptr %45, align 8
  %431 = icmp ne i64 %430, 0
  %432 = zext i1 %431 to i32
  %433 = load i8, ptr @var_32, align 1
  %434 = trunc i8 %433 to i1
  %435 = zext i1 %434 to i32
  %436 = and i32 %435, %432
  %437 = icmp ne i32 %436, 0
  %438 = zext i1 %437 to i8
  store i8 %438, ptr @var_32, align 1
  store i8 -4, ptr @var_33, align 1
  %439 = load i8, ptr %39, align 1
  %440 = sext i8 %439 to i32
  %441 = sext i32 %440 to i64
  %442 = load i32, ptr %43, align 4
  %443 = sext i32 %442 to i64
  %444 = icmp uge i64 %441, %443
  %445 = zext i1 %444 to i32
  %446 = trunc i32 %445 to i8
  store i8 %446, ptr @var_34, align 1
  %447 = load i64, ptr %29, align 8
  %448 = icmp ne i64 %447, 0
  br i1 %448, label %449, label %478

449:                                              ; preds = %429
  store i8 0, ptr %70, align 1
  store i8 113, ptr %71, align 1
  %450 = load i8, ptr %70, align 1
  %451 = sext i8 %450 to i32
  %452 = load i8, ptr %71, align 1
  %453 = sext i8 %452 to i32
  %454 = icmp sgt i32 %451, %453
  br i1 %454, label %455, label %458

455:                                              ; preds = %449
  %456 = load i8, ptr %70, align 1
  %457 = sext i8 %456 to i32
  br label %461

458:                                              ; preds = %449
  %459 = load i8, ptr %71, align 1
  %460 = sext i8 %459 to i32
  br label %461

461:                                              ; preds = %458, %455
  %462 = phi i32 [ %457, %455 ], [ %460, %458 ]
  store i32 %462, ptr %72, align 4
  %463 = load i32, ptr %72, align 4
  %464 = sext i32 %463 to i64
  store i64 %464, ptr %69, align 8
  %465 = load i8, ptr %34, align 1
  %466 = zext i8 %465 to i32
  %467 = sext i32 %466 to i64
  store i64 %467, ptr %73, align 8
  %468 = load i64, ptr %69, align 8
  %469 = load i64, ptr %73, align 8
  %470 = icmp slt i64 %468, %469
  br i1 %470, label %471, label %473

471:                                              ; preds = %461
  %472 = load i64, ptr %69, align 8
  br label %475

473:                                              ; preds = %461
  %474 = load i64, ptr %73, align 8
  br label %475

475:                                              ; preds = %473, %471
  %476 = phi i64 [ %472, %471 ], [ %474, %473 ]
  store i64 %476, ptr %74, align 8
  %477 = load i64, ptr %74, align 8
  br label %481

478:                                              ; preds = %429
  %479 = load i32, ptr %44, align 4
  %480 = sext i32 %479 to i64
  br label %481

481:                                              ; preds = %478, %475
  %482 = phi i64 [ %477, %475 ], [ %480, %478 ]
  %483 = sub i64 %482, 111
  store i64 %483, ptr %68, align 8
  br label %484

484:                                              ; preds = %549, %481
  %485 = load i64, ptr %68, align 8
  %486 = load i64, ptr %35, align 8
  %487 = sub i64 %486, 6811601507656744406
  %488 = icmp ult i64 %485, %487
  br i1 %488, label %489, label %552

489:                                              ; preds = %484
  %490 = load i64, ptr %32, align 8
  %491 = icmp ne i64 %490, 0
  %492 = zext i1 %491 to i32
  %493 = sub nsw i32 %492, 1
  %494 = icmp ne i32 %493, 0
  %495 = zext i1 %494 to i8
  store i8 %495, ptr %75, align 1
  br label %496

496:                                              ; preds = %541, %489
  %497 = load i8, ptr %75, align 1
  %498 = trunc i8 %497 to i1
  %499 = zext i1 %498 to i32
  %500 = icmp slt i32 %499, 1
  br i1 %500, label %501, label %548

501:                                              ; preds = %496
  store i8 -84, ptr @var_35, align 1
  %502 = load ptr, ptr %53, align 8
  %503 = load i64, ptr %68, align 8
  %504 = sub i64 %503, 1
  %505 = getelementptr inbounds i8, ptr %502, i64 %504
  %506 = load i8, ptr %505, align 1
  %507 = sext i8 %506 to i32
  store i32 %507, ptr %76, align 4
  %508 = load ptr, ptr %53, align 8
  %509 = load i64, ptr %68, align 8
  %510 = add i64 %509, 1
  %511 = getelementptr inbounds i8, ptr %508, i64 %510
  %512 = load i8, ptr %511, align 1
  %513 = icmp ne i8 %512, 0
  br i1 %513, label %514, label %521

514:                                              ; preds = %501
  %515 = load ptr, ptr %53, align 8
  %516 = load i64, ptr %68, align 8
  %517 = sub i64 %516, 2
  %518 = getelementptr inbounds i8, ptr %515, i64 %517
  %519 = load i8, ptr %518, align 1
  %520 = sext i8 %519 to i32
  br label %528

521:                                              ; preds = %501
  %522 = load ptr, ptr %53, align 8
  %523 = load i64, ptr %68, align 8
  %524 = add i64 %523, 1
  %525 = getelementptr inbounds i8, ptr %522, i64 %524
  %526 = load i8, ptr %525, align 1
  %527 = sext i8 %526 to i32
  br label %528

528:                                              ; preds = %521, %514
  %529 = phi i32 [ %520, %514 ], [ %527, %521 ]
  store i32 %529, ptr %77, align 4
  %530 = load i32, ptr %76, align 4
  %531 = load i32, ptr %77, align 4
  %532 = icmp sgt i32 %530, %531
  br i1 %532, label %533, label %535

533:                                              ; preds = %528
  %534 = load i32, ptr %76, align 4
  br label %537

535:                                              ; preds = %528
  %536 = load i32, ptr %77, align 4
  br label %537

537:                                              ; preds = %535, %533
  %538 = phi i32 [ %534, %533 ], [ %536, %535 ]
  store i32 %538, ptr %78, align 4
  %539 = load i32, ptr %78, align 4
  %540 = sext i32 %539 to i64
  store i64 %540, ptr @var_36, align 8
  br label %541

541:                                              ; preds = %537
  %542 = load i8, ptr %75, align 1
  %543 = trunc i8 %542 to i1
  %544 = zext i1 %543 to i32
  %545 = add nsw i32 %544, 1
  %546 = icmp ne i32 %545, 0
  %547 = zext i1 %546 to i8
  store i8 %547, ptr %75, align 1
  br label %496, !llvm.loop !28

548:                                              ; preds = %496
  br label %549

549:                                              ; preds = %548
  %550 = load i64, ptr %68, align 8
  %551 = add i64 %550, 1
  store i64 %551, ptr %68, align 8
  br label %484, !llvm.loop !29

552:                                              ; preds = %484
  br label %553

553:                                              ; preds = %552, %412
  %554 = load i64, ptr %35, align 8
  store i64 %554, ptr %79, align 8
  %555 = load i8, ptr %40, align 1
  %556 = sext i8 %555 to i64
  store i64 %556, ptr %81, align 8
  store i64 -8909293706326293161, ptr %83, align 8
  store i64 -8747918391861174041, ptr %84, align 8
  %557 = load i64, ptr %83, align 8
  %558 = load i64, ptr %84, align 8
  %559 = icmp ugt i64 %557, %558
  br i1 %559, label %560, label %562

560:                                              ; preds = %553
  %561 = load i64, ptr %83, align 8
  br label %564

562:                                              ; preds = %553
  %563 = load i64, ptr %84, align 8
  br label %564

564:                                              ; preds = %562, %560
  %565 = phi i64 [ %561, %560 ], [ %563, %562 ]
  store i64 %565, ptr %85, align 8
  %566 = load i64, ptr %85, align 8
  store i64 %566, ptr %82, align 8
  %567 = load i64, ptr %81, align 8
  %568 = load i64, ptr %82, align 8
  %569 = icmp ult i64 %567, %568
  br i1 %569, label %570, label %572

570:                                              ; preds = %564
  %571 = load i64, ptr %81, align 8
  br label %574

572:                                              ; preds = %564
  %573 = load i64, ptr %82, align 8
  br label %574

574:                                              ; preds = %572, %570
  %575 = phi i64 [ %571, %570 ], [ %573, %572 ]
  store i64 %575, ptr %86, align 8
  %576 = load i64, ptr %86, align 8
  store i64 %576, ptr %80, align 8
  %577 = load i64, ptr %79, align 8
  %578 = load i64, ptr %80, align 8
  %579 = icmp ugt i64 %577, %578
  br i1 %579, label %580, label %582

580:                                              ; preds = %574
  %581 = load i64, ptr %79, align 8
  br label %584

582:                                              ; preds = %574
  %583 = load i64, ptr %80, align 8
  br label %584

584:                                              ; preds = %582, %580
  %585 = phi i64 [ %581, %580 ], [ %583, %582 ]
  store i64 %585, ptr %87, align 8
  %586 = load i64, ptr %87, align 8
  store i64 %586, ptr @var_37, align 8
  store i64 -74, ptr %89, align 8
  store i64 -8832833163218785510, ptr %90, align 8
  %587 = load i64, ptr %89, align 8
  %588 = load i64, ptr %90, align 8
  %589 = icmp slt i64 %587, %588
  br i1 %589, label %590, label %592

590:                                              ; preds = %584
  %591 = load i64, ptr %89, align 8
  br label %594

592:                                              ; preds = %584
  %593 = load i64, ptr %90, align 8
  br label %594

594:                                              ; preds = %592, %590
  %595 = phi i64 [ %591, %590 ], [ %593, %592 ]
  store i64 %595, ptr %91, align 8
  %596 = load i64, ptr %91, align 8
  %597 = sub i64 %596, -8832833163218785510
  store i64 %597, ptr %88, align 8
  br label %598

598:                                              ; preds = %815, %594
  %599 = load i64, ptr %88, align 8
  %600 = icmp ult i64 %599, 22
  br i1 %600, label %601, label %820

601:                                              ; preds = %598
  %602 = load ptr, ptr %54, align 8
  %603 = load i64, ptr %88, align 8
  %604 = getelementptr inbounds i32, ptr %602, i64 %603
  %605 = load i32, ptr %604, align 4
  %606 = icmp ne i32 %605, 0
  %607 = zext i1 %606 to i32
  %608 = sub nsw i32 %607, 1
  %609 = icmp ne i32 %608, 0
  %610 = zext i1 %609 to i8
  store i8 %610, ptr %92, align 1
  br label %611

611:                                              ; preds = %800, %601
  %612 = load i8, ptr %92, align 1
  %613 = trunc i8 %612 to i1
  %614 = zext i1 %613 to i32
  %615 = load i8, ptr %30, align 1
  %616 = icmp ne i8 %615, 0
  %617 = zext i1 %616 to i32
  %618 = icmp slt i32 %614, %617
  br i1 %618, label %619, label %814

619:                                              ; preds = %611
  store i8 0, ptr %93, align 1
  br label %620

620:                                              ; preds = %778, %619
  %621 = load i8, ptr %93, align 1
  %622 = trunc i8 %621 to i1
  %623 = zext i1 %622 to i32
  %624 = icmp slt i32 %623, 1
  br i1 %624, label %625, label %785

625:                                              ; preds = %620
  %626 = load ptr, ptr %54, align 8
  %627 = load i8, ptr %92, align 1
  %628 = trunc i8 %627 to i1
  %629 = zext i1 %628 to i64
  %630 = getelementptr inbounds i32, ptr %626, i64 %629
  %631 = load i32, ptr %630, align 4
  %632 = icmp ne i32 %631, 0
  br i1 %632, label %633, label %634

633:                                              ; preds = %625
  br label %650

634:                                              ; preds = %625
  %635 = load i32, ptr %44, align 4
  store i32 %635, ptr %94, align 4
  %636 = load i8, ptr %41, align 1
  %637 = trunc i8 %636 to i1
  %638 = zext i1 %637 to i32
  store i32 %638, ptr %95, align 4
  %639 = load i32, ptr %94, align 4
  %640 = load i32, ptr %95, align 4
  %641 = icmp slt i32 %639, %640
  br i1 %641, label %642, label %644

642:                                              ; preds = %634
  %643 = load i32, ptr %94, align 4
  br label %646

644:                                              ; preds = %634
  %645 = load i32, ptr %95, align 4
  br label %646

646:                                              ; preds = %644, %642
  %647 = phi i32 [ %643, %642 ], [ %645, %644 ]
  store i32 %647, ptr %96, align 4
  %648 = load i32, ptr %96, align 4
  %649 = sext i32 %648 to i64
  br label %650

650:                                              ; preds = %646, %633
  %651 = phi i64 [ 0, %633 ], [ %649, %646 ]
  %652 = load i64, ptr @var_38, align 8
  %653 = and i64 %652, %651
  store i64 %653, ptr @var_38, align 8
  %654 = load i8, ptr @var_39, align 1
  %655 = trunc i8 %654 to i1
  %656 = zext i1 %655 to i8
  store i8 %656, ptr %97, align 1
  %657 = load i64, ptr %42, align 8
  %658 = icmp sgt i64 -1, %657
  %659 = xor i1 %658, true
  %660 = zext i1 %659 to i32
  store i32 %660, ptr %98, align 4
  %661 = load i8, ptr %97, align 1
  %662 = trunc i8 %661 to i1
  %663 = zext i1 %662 to i32
  %664 = load i32, ptr %98, align 4
  %665 = icmp slt i32 %663, %664
  br i1 %665, label %666, label %670

666:                                              ; preds = %650
  %667 = load i8, ptr %97, align 1
  %668 = trunc i8 %667 to i1
  %669 = zext i1 %668 to i32
  br label %672

670:                                              ; preds = %650
  %671 = load i32, ptr %98, align 4
  br label %672

672:                                              ; preds = %670, %666
  %673 = phi i32 [ %669, %666 ], [ %671, %670 ]
  store i32 %673, ptr %99, align 4
  %674 = load i32, ptr %99, align 4
  %675 = icmp ne i32 %674, 0
  %676 = zext i1 %675 to i8
  store i8 %676, ptr @var_39, align 1
  %677 = load ptr, ptr %55, align 8
  %678 = load i64, ptr %88, align 8
  %679 = getelementptr inbounds [22 x i64], ptr %677, i64 %678
  %680 = load i8, ptr %92, align 1
  %681 = trunc i8 %680 to i1
  %682 = zext i1 %681 to i64
  %683 = getelementptr inbounds [22 x i64], ptr %679, i64 0, i64 %682
  %684 = load i64, ptr %683, align 8
  %685 = icmp ne i64 %684, 0
  br i1 %685, label %686, label %695

686:                                              ; preds = %672
  %687 = load ptr, ptr %54, align 8
  %688 = load i64, ptr %88, align 8
  %689 = getelementptr inbounds i32, ptr %687, i64 %688
  %690 = load i32, ptr %689, align 4
  %691 = load i8, ptr %34, align 1
  %692 = zext i8 %691 to i32
  %693 = icmp slt i32 %690, %692
  %694 = zext i1 %693 to i32
  br label %699

695:                                              ; preds = %672
  %696 = load i64, ptr %37, align 8
  %697 = trunc i64 %696 to i8
  %698 = zext i8 %697 to i32
  br label %699

699:                                              ; preds = %695, %686
  %700 = phi i32 [ %694, %686 ], [ %698, %695 ]
  %701 = icmp ne i32 %700, 0
  br i1 %701, label %702, label %737

702:                                              ; preds = %699
  %703 = load i8, ptr %46, align 1
  %704 = trunc i8 %703 to i1
  %705 = zext i1 %704 to i8
  store i8 %705, ptr %101, align 1
  %706 = load ptr, ptr %56, align 8
  %707 = load i64, ptr %88, align 8
  %708 = getelementptr inbounds i8, ptr %706, i64 %707
  %709 = load i8, ptr %708, align 1
  store i8 %709, ptr %102, align 1
  %710 = load i8, ptr %101, align 1
  %711 = sext i8 %710 to i32
  %712 = load i8, ptr %102, align 1
  %713 = sext i8 %712 to i32
  %714 = icmp sgt i32 %711, %713
  br i1 %714, label %715, label %718

715:                                              ; preds = %702
  %716 = load i8, ptr %101, align 1
  %717 = sext i8 %716 to i32
  br label %721

718:                                              ; preds = %702
  %719 = load i8, ptr %102, align 1
  %720 = sext i8 %719 to i32
  br label %721

721:                                              ; preds = %718, %715
  %722 = phi i32 [ %717, %715 ], [ %720, %718 ]
  store i32 %722, ptr %103, align 4
  %723 = load i32, ptr %103, align 4
  store i32 %723, ptr %100, align 4
  %724 = load i64, ptr %37, align 8
  %725 = trunc i64 %724 to i32
  store i32 %725, ptr %104, align 4
  %726 = load i32, ptr %100, align 4
  %727 = load i32, ptr %104, align 4
  %728 = icmp sgt i32 %726, %727
  br i1 %728, label %729, label %731

729:                                              ; preds = %721
  %730 = load i32, ptr %100, align 4
  br label %733

731:                                              ; preds = %721
  %732 = load i32, ptr %104, align 4
  br label %733

733:                                              ; preds = %731, %729
  %734 = phi i32 [ %730, %729 ], [ %732, %731 ]
  store i32 %734, ptr %105, align 4
  %735 = load i32, ptr %105, align 4
  %736 = sext i32 %735 to i64
  br label %749

737:                                              ; preds = %699
  store i64 550899815553814903, ptr %106, align 8
  store i64 6063631626888121186, ptr %107, align 8
  %738 = load i64, ptr %106, align 8
  %739 = load i64, ptr %107, align 8
  %740 = icmp ugt i64 %738, %739
  br i1 %740, label %741, label %743

741:                                              ; preds = %737
  %742 = load i64, ptr %106, align 8
  br label %745

743:                                              ; preds = %737
  %744 = load i64, ptr %107, align 8
  br label %745

745:                                              ; preds = %743, %741
  %746 = phi i64 [ %742, %741 ], [ %744, %743 ]
  store i64 %746, ptr %108, align 8
  %747 = load i64, ptr %108, align 8
  %748 = xor i64 %747, -1
  br label %749

749:                                              ; preds = %745, %733
  %750 = phi i64 [ %736, %733 ], [ %748, %745 ]
  %751 = trunc i64 %750 to i8
  %752 = load i8, ptr %93, align 1
  %753 = trunc i8 %752 to i1
  %754 = zext i1 %753 to i64
  %755 = getelementptr inbounds [22 x [22 x [22 x i8]]], ptr @arr_18, i64 0, i64 %754
  %756 = load i64, ptr %88, align 8
  %757 = getelementptr inbounds [22 x [22 x i8]], ptr %755, i64 0, i64 %756
  %758 = load i8, ptr %93, align 1
  %759 = trunc i8 %758 to i1
  %760 = zext i1 %759 to i64
  %761 = getelementptr inbounds [22 x i8], ptr %757, i64 0, i64 %760
  store i8 %751, ptr %761, align 1
  %762 = load i64, ptr %36, align 8
  %763 = icmp ne i64 %762, 0
  br i1 %763, label %764, label %765

764:                                              ; preds = %749
  br label %770

765:                                              ; preds = %749
  %766 = load i8, ptr %31, align 1
  %767 = trunc i8 %766 to i1
  %768 = zext i1 %767 to i32
  %769 = sext i32 %768 to i64
  br label %770

770:                                              ; preds = %765, %764
  %771 = phi i64 [ -121, %764 ], [ %769, %765 ]
  %772 = trunc i64 %771 to i8
  %773 = sext i8 %772 to i32
  %774 = load i8, ptr @var_40, align 1
  %775 = sext i8 %774 to i32
  %776 = add nsw i32 %775, %773
  %777 = trunc i32 %776 to i8
  store i8 %777, ptr @var_40, align 1
  br label %778

778:                                              ; preds = %770
  %779 = load i8, ptr %93, align 1
  %780 = trunc i8 %779 to i1
  %781 = zext i1 %780 to i32
  %782 = add nsw i32 %781, 1
  %783 = icmp ne i32 %782, 0
  %784 = zext i1 %783 to i8
  store i8 %784, ptr %93, align 1
  br label %620, !llvm.loop !30

785:                                              ; preds = %620
  br label %786

786:                                              ; preds = %785
  %787 = load ptr, ptr %54, align 8
  %788 = load i64, ptr %88, align 8
  %789 = getelementptr inbounds i32, ptr %787, i64 %788
  %790 = load i32, ptr %789, align 4
  %791 = sext i32 %790 to i64
  store i64 %791, ptr %109, align 8
  %792 = load i64, ptr %32, align 8
  store i64 %792, ptr %110, align 8
  %793 = load i64, ptr %109, align 8
  %794 = load i64, ptr %110, align 8
  %795 = icmp ult i64 %793, %794
  br i1 %795, label %796, label %798

796:                                              ; preds = %786
  %797 = load i64, ptr %109, align 8
  br label %800

798:                                              ; preds = %786
  %799 = load i64, ptr %110, align 8
  br label %800

800:                                              ; preds = %798, %796
  %801 = phi i64 [ %797, %796 ], [ %799, %798 ]
  store i64 %801, ptr %111, align 8
  %802 = load i64, ptr %111, align 8
  %803 = sub i64 0, %802
  %804 = urem i64 0, %803
  %805 = icmp ne i64 %804, 0
  %806 = zext i1 %805 to i32
  %807 = add nsw i32 %806, 1
  %808 = load i8, ptr %92, align 1
  %809 = trunc i8 %808 to i1
  %810 = zext i1 %809 to i32
  %811 = add nsw i32 %810, %807
  %812 = icmp ne i32 %811, 0
  %813 = zext i1 %812 to i8
  store i8 %813, ptr %92, align 1
  br label %611, !llvm.loop !31

814:                                              ; preds = %611
  br label %815

815:                                              ; preds = %814
  %816 = load i64, ptr %36, align 8
  %817 = sub i64 %816, 9067224066152263288
  %818 = load i64, ptr %88, align 8
  %819 = add i64 %818, %817
  store i64 %819, ptr %88, align 8
  br label %598, !llvm.loop !32

820:                                              ; preds = %598
  %821 = load i8, ptr %31, align 1
  %822 = trunc i8 %821 to i1
  %823 = xor i1 %822, true
  %824 = zext i1 %823 to i32
  %825 = sub nsw i32 0, %824
  %826 = sext i32 %825 to i64
  store i64 %826, ptr %112, align 8
  %827 = load i8, ptr %47, align 1
  %828 = icmp ne i8 %827, 0
  br i1 %828, label %831, label %829

829:                                              ; preds = %820
  %830 = load i64, ptr %35, align 8
  br label %835

831:                                              ; preds = %820
  %832 = load i8, ptr %47, align 1
  %833 = zext i8 %832 to i32
  %834 = sext i32 %833 to i64
  br label %835

835:                                              ; preds = %831, %829
  %836 = phi i64 [ %830, %829 ], [ %834, %831 ]
  store i64 %836, ptr %113, align 8
  %837 = load i64, ptr %112, align 8
  %838 = load i64, ptr %113, align 8
  %839 = icmp ugt i64 %837, %838
  br i1 %839, label %840, label %842

840:                                              ; preds = %835
  %841 = load i64, ptr %112, align 8
  br label %844

842:                                              ; preds = %835
  %843 = load i64, ptr %113, align 8
  br label %844

844:                                              ; preds = %842, %840
  %845 = phi i64 [ %841, %840 ], [ %843, %842 ]
  store i64 %845, ptr %114, align 8
  %846 = load i64, ptr %114, align 8
  store i64 %846, ptr @var_41, align 8
  ret void
}

attributes #0 = { noinline nounwind optnone ssp uwtable "darwin-stkchk-strong-link" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "darwin-stkchk-strong-link" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0, !0}
!llvm.module.flags = !{!1, !2, !3}

!0 = !{!"Apple clang version 13.0.0 (clang-1300.0.29.30)"}
!1 = !{i32 2, !"SDK Version", [2 x i32] [i32 12, i32 1]}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{i32 8, !"PIC Level", i32 2}
!4 = distinct !{!4, !5}
!5 = !{!"llvm.loop.mustprogress"}
!6 = distinct !{!6, !5}
!7 = distinct !{!7, !5}
!8 = distinct !{!8, !5}
!9 = distinct !{!9, !5}
!10 = distinct !{!10, !5}
!11 = distinct !{!11, !5}
!12 = distinct !{!12, !5}
!13 = distinct !{!13, !5}
!14 = distinct !{!14, !5}
!15 = distinct !{!15, !5}
!16 = distinct !{!16, !5}
!17 = distinct !{!17, !5}
!18 = distinct !{!18, !5}
!19 = distinct !{!19, !5}
!20 = distinct !{!20, !5}
!21 = distinct !{!21, !5}
!22 = distinct !{!22, !5}
!23 = distinct !{!23, !5}
!24 = distinct !{!24, !5}
!25 = distinct !{!25, !5}
!26 = distinct !{!26, !5}
!27 = distinct !{!27, !5}
!28 = distinct !{!28, !5}
!29 = distinct !{!29, !5}
!30 = distinct !{!30, !5}
!31 = distinct !{!31, !5}
!32 = distinct !{!32, !5}
