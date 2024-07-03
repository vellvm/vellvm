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

121:                                              ; preds = %116
  %122 = load i32, i32* %11, align 4
  %123 = or i32 %122, 2
  store i32 %123, i32* %11, align 4
  %124 = load i32, i32* %16, align 4
  %125 = sub nsw i32 0, %124
  store i32 %125, i32* %12, align 4
  br label %128

126:                                              ; preds = %116
  %127 = load i32, i32* %16, align 4
  store i32 %127, i32* %12, align 4
  br label %128

128:                                              ; preds = %126, %121
  %129 = load i8*, i8** %9, align 8
  %130 = getelementptr inbounds i8, i8* %129, i32 1
  store i8* %130, i8** %9, align 8
  br label %131

131:                                              ; preds = %128, %111
  br label %132

132:                                              ; preds = %131, %109
  store i32 0, i32* %13, align 4
  %133 = load i8*, i8** %9, align 8
  %134 = load i8, i8* %133, align 1
  %135 = sext i8 %134 to i32
  %136 = icmp eq i32 %135, 46
  br i1 %136, label %137, label %166

137:                                              ; preds = %132
  %138 = load i32, i32* %11, align 4
  %139 = or i32 %138, 1024
  store i32 %139, i32* %11, align 4
  %140 = load i8*, i8** %9, align 8
  %141 = getelementptr inbounds i8, i8* %140, i32 1
  store i8* %141, i8** %9, align 8
  %142 = load i8*, i8** %9, align 8
  %143 = load i8, i8* %142, align 1
  %144 = call zeroext i1 @_is_digit(i8 noundef signext %143)
  br i1 %144, label %145, label %147

145:                                              ; preds = %137
  %146 = call i32 @_atoi(i8** noundef %9)
  store i32 %146, i32* %13, align 4
  br label %165

147:                                              ; preds = %137
  %148 = load i8*, i8** %9, align 8
  %149 = load i8, i8* %148, align 1
  %150 = sext i8 %149 to i32
  %151 = icmp eq i32 %150, 42
  br i1 %151, label %152, label %164

152:                                              ; preds = %147
  %153 = va_arg i8** %10, i32
  store i32 %153, i32* %19, align 4
  %154 = load i32, i32* %19, align 4
  store i32 %154, i32* %18, align 4
  %155 = load i32, i32* %18, align 4
  %156 = icmp sgt i32 %155, 0
  br i1 %156, label %157, label %159

157:                                              ; preds = %152
  %158 = load i32, i32* %18, align 4
  br label %160

159:                                              ; preds = %152
  br label %160

160:                                              ; preds = %159, %157
  %161 = phi i32 [ %158, %157 ], [ 0, %159 ]
  store i32 %161, i32* %13, align 4
  %162 = load i8*, i8** %9, align 8
  %163 = getelementptr inbounds i8, i8* %162, i32 1
  store i8* %163, i8** %9, align 8
  br label %164

164:                                              ; preds = %160, %147
  br label %165

165:                                              ; preds = %164, %145
  br label %166

166:                                              ; preds = %165, %132
  %167 = load i8*, i8** %9, align 8
  %168 = load i8, i8* %167, align 1
  %169 = sext i8 %168 to i32
  switch i32 %169, label %215 [
    i32 108, label %170
    i32 104, label %185
    i32 116, label %200
    i32 106, label %205
    i32 122, label %210
  ]

170:                                              ; preds = %166
  %171 = load i32, i32* %11, align 4
  %172 = or i32 %171, 256
  store i32 %172, i32* %11, align 4
  %173 = load i8*, i8** %9, align 8
  %174 = getelementptr inbounds i8, i8* %173, i32 1
  store i8* %174, i8** %9, align 8
  %175 = load i8*, i8** %9, align 8
  %176 = load i8, i8* %175, align 1
  %177 = sext i8 %176 to i32
  %178 = icmp eq i32 %177, 108
  br i1 %178, label %179, label %184

179:                                              ; preds = %170
  %180 = load i32, i32* %11, align 4
  %181 = or i32 %180, 512
  store i32 %181, i32* %11, align 4
  %182 = load i8*, i8** %9, align 8
  %183 = getelementptr inbounds i8, i8* %182, i32 1
  store i8* %183, i8** %9, align 8
  br label %184

184:                                              ; preds = %179, %170
  br label %216

185:                                              ; preds = %166
  %186 = load i32, i32* %11, align 4
  %187 = or i32 %186, 128
  store i32 %187, i32* %11, align 4
  %188 = load i8*, i8** %9, align 8
  %189 = getelementptr inbounds i8, i8* %188, i32 1
  store i8* %189, i8** %9, align 8
  %190 = load i8*, i8** %9, align 8
  %191 = load i8, i8* %190, align 1
  %192 = sext i8 %191 to i32
  %193 = icmp eq i32 %192, 104
  br i1 %193, label %194, label %199

194:                                              ; preds = %185
  %195 = load i32, i32* %11, align 4
  %196 = or i32 %195, 64
  store i32 %196, i32* %11, align 4
  %197 = load i8*, i8** %9, align 8
  %198 = getelementptr inbounds i8, i8* %197, i32 1
  store i8* %198, i8** %9, align 8
  br label %199

199:                                              ; preds = %194, %185
  br label %216

200:                                              ; preds = %166
  %201 = load i32, i32* %11, align 4
  %202 = or i32 %201, 256
  store i32 %202, i32* %11, align 4
  %203 = load i8*, i8** %9, align 8
  %204 = getelementptr inbounds i8, i8* %203, i32 1
  store i8* %204, i8** %9, align 8
  br label %216

205:                                              ; preds = %166
  %206 = load i32, i32* %11, align 4
  %207 = or i32 %206, 256
  store i32 %207, i32* %11, align 4
  %208 = load i8*, i8** %9, align 8
  %209 = getelementptr inbounds i8, i8* %208, i32 1
  store i8* %209, i8** %9, align 8
  br label %216

210:                                              ; preds = %166
  %211 = load i32, i32* %11, align 4
  %212 = or i32 %211, 256
  store i32 %212, i32* %11, align 4
  %213 = load i8*, i8** %9, align 8
  %214 = getelementptr inbounds i8, i8* %213, i32 1
  store i8* %214, i8** %9, align 8
  br label %216

215:                                              ; preds = %166
  br label %216

216:                                              ; preds = %215, %210, %205, %200, %199, %184
  %217 = load i8*, i8** %9, align 8
  %218 = load i8, i8* %217, align 1
  %219 = sext i8 %218 to i32
  switch i32 %219, label %686 [
    i32 100, label %220
    i32 105, label %220
    i32 117, label %220
    i32 120, label %220
    i32 88, label %220
    i32 111, label %220
    i32 98, label %220
    i32 102, label %467
    i32 70, label %467
    i32 101, label %488
    i32 69, label %488
    i32 103, label %488
    i32 71, label %488
    i32 99, label %527
    i32 115, label %572
    i32 112, label %662
    i32 37, label %678
  ]

220:                                              ; preds = %216, %216, %216, %216, %216, %216, %216
  %221 = load i8*, i8** %9, align 8
  %222 = load i8, i8* %221, align 1
  %223 = sext i8 %222 to i32
  %224 = icmp eq i32 %223, 120
  br i1 %224, label %230, label %225

225:                                              ; preds = %220
  %226 = load i8*, i8** %9, align 8
  %227 = load i8, i8* %226, align 1
  %228 = sext i8 %227 to i32
  %229 = icmp eq i32 %228, 88
  br i1 %229, label %230, label %231

230:                                              ; preds = %225, %220
  store i32 16, i32* %20, align 4
  br label %248

231:                                              ; preds = %225
  %232 = load i8*, i8** %9, align 8
  %233 = load i8, i8* %232, align 1
  %234 = sext i8 %233 to i32
  %235 = icmp eq i32 %234, 111
  br i1 %235, label %236, label %237

236:                                              ; preds = %231
  store i32 8, i32* %20, align 4
  br label %247

237:                                              ; preds = %231
  %238 = load i8*, i8** %9, align 8
  %239 = load i8, i8* %238, align 1
  %240 = sext i8 %239 to i32
  %241 = icmp eq i32 %240, 98
  br i1 %241, label %242, label %243

242:                                              ; preds = %237
  store i32 2, i32* %20, align 4
  br label %246

243:                                              ; preds = %237
  store i32 10, i32* %20, align 4
  %244 = load i32, i32* %11, align 4
  %245 = and i32 %244, -17
  store i32 %245, i32* %11, align 4
  br label %246

246:                                              ; preds = %243, %242
  br label %247

247:                                              ; preds = %246, %236
  br label %248

248:                                              ; preds = %247, %230
  %249 = load i8*, i8** %9, align 8
  %250 = load i8, i8* %249, align 1
  %251 = sext i8 %250 to i32
  %252 = icmp eq i32 %251, 88
  br i1 %252, label %253, label %256

253:                                              ; preds = %248
  %254 = load i32, i32* %11, align 4
  %255 = or i32 %254, 32
  store i32 %255, i32* %11, align 4
  br label %256

256:                                              ; preds = %253, %248
  %257 = load i8*, i8** %9, align 8
  %258 = load i8, i8* %257, align 1
  %259 = sext i8 %258 to i32
  %260 = icmp ne i32 %259, 105
  br i1 %260, label %261, label %269

261:                                              ; preds = %256
  %262 = load i8*, i8** %9, align 8
  %263 = load i8, i8* %262, align 1
  %264 = sext i8 %263 to i32
  %265 = icmp ne i32 %264, 100
  br i1 %265, label %266, label %269

266:                                              ; preds = %261
  %267 = load i32, i32* %11, align 4
  %268 = and i32 %267, -13
  store i32 %268, i32* %11, align 4
  br label %269

269:                                              ; preds = %266, %261, %256
  %270 = load i32, i32* %11, align 4
  %271 = and i32 %270, 1024
  %272 = icmp ne i32 %271, 0
  br i1 %272, label %273, label %276

273:                                              ; preds = %269
  %274 = load i32, i32* %11, align 4
  %275 = and i32 %274, -2
  store i32 %275, i32* %11, align 4
  br label %276

276:                                              ; preds = %273, %269
  %277 = load i8*, i8** %9, align 8
  %278 = load i8, i8* %277, align 1
  %279 = sext i8 %278 to i32
  %280 = icmp eq i32 %279, 105
  br i1 %280, label %286, label %281

281:                                              ; preds = %276
  %282 = load i8*, i8** %9, align 8
  %283 = load i8, i8* %282, align 1
  %284 = sext i8 %283 to i32
  %285 = icmp eq i32 %284, 100
  br i1 %285, label %286, label %391

286:                                              ; preds = %281, %276
  %287 = load i32, i32* %11, align 4
  %288 = and i32 %287, 512
  %289 = icmp ne i32 %288, 0
  br i1 %289, label %290, label %314

290:                                              ; preds = %286
  %291 = va_arg i8** %10, i64
  store i64 %291, i64* %22, align 8
  %292 = load i64, i64* %22, align 8
  store i64 %292, i64* %21, align 8
  %293 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %294 = load i8*, i8** %7, align 8
  %295 = load i64, i64* %15, align 8
  %296 = load i64, i64* %8, align 8
  %297 = load i64, i64* %21, align 8
  %298 = icmp sgt i64 %297, 0
  br i1 %298, label %299, label %301

299:                                              ; preds = %290
  %300 = load i64, i64* %21, align 8
  br label %304

301:                                              ; preds = %290
  %302 = load i64, i64* %21, align 8
  %303 = sub nsw i64 0, %302
  br label %304

304:                                              ; preds = %301, %299
  %305 = phi i64 [ %300, %299 ], [ %303, %301 ]
  %306 = load i64, i64* %21, align 8
  %307 = icmp slt i64 %306, 0
  %308 = load i32, i32* %20, align 4
  %309 = zext i32 %308 to i64
  %310 = load i32, i32* %13, align 4
  %311 = load i32, i32* %12, align 4
  %312 = load i32, i32* %11, align 4
  %313 = call i64 @_ntoa_long_long(void (i8, i8*, i64, i64)* noundef %293, i8* noundef %294, i64 noundef %295, i64 noundef %296, i64 noundef %305, i1 noundef zeroext %307, i64 noundef %309, i32 noundef %310, i32 noundef %311, i32 noundef %312)
  store i64 %313, i64* %15, align 8
  br label %390

314:                                              ; preds = %286
  %315 = load i32, i32* %11, align 4
  %316 = and i32 %315, 256
  %317 = icmp ne i32 %316, 0
  br i1 %317, label %318, label %342

318:                                              ; preds = %314
  %319 = va_arg i8** %10, i64
  store i64 %319, i64* %24, align 8
  %320 = load i64, i64* %24, align 8
  store i64 %320, i64* %23, align 8
  %321 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %322 = load i8*, i8** %7, align 8
  %323 = load i64, i64* %15, align 8
  %324 = load i64, i64* %8, align 8
  %325 = load i64, i64* %23, align 8
  %326 = icmp sgt i64 %325, 0
  br i1 %326, label %327, label %329

327:                                              ; preds = %318
  %328 = load i64, i64* %23, align 8
  br label %332

329:                                              ; preds = %318
  %330 = load i64, i64* %23, align 8
  %331 = sub nsw i64 0, %330
  br label %332

332:                                              ; preds = %329, %327
  %333 = phi i64 [ %328, %327 ], [ %331, %329 ]
  %334 = load i64, i64* %23, align 8
  %335 = icmp slt i64 %334, 0
  %336 = load i32, i32* %20, align 4
  %337 = zext i32 %336 to i64
  %338 = load i32, i32* %13, align 4
  %339 = load i32, i32* %12, align 4
  %340 = load i32, i32* %11, align 4
  %341 = call i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %321, i8* noundef %322, i64 noundef %323, i64 noundef %324, i64 noundef %333, i1 noundef zeroext %335, i64 noundef %337, i32 noundef %338, i32 noundef %339, i32 noundef %340)
  store i64 %341, i64* %15, align 8
  br label %389

342:                                              ; preds = %314
  %343 = load i32, i32* %11, align 4
  %344 = and i32 %343, 64
  %345 = icmp ne i32 %344, 0
  br i1 %345, label %346, label %351

346:                                              ; preds = %342
  %347 = va_arg i8** %10, i32
  store i32 %347, i32* %26, align 4
  %348 = load i32, i32* %26, align 4
  %349 = trunc i32 %348 to i8
  %350 = sext i8 %349 to i32
  br label %365

351:                                              ; preds = %342
  %352 = load i32, i32* %11, align 4
  %353 = and i32 %352, 128
  %354 = icmp ne i32 %353, 0
  br i1 %354, label %355, label %360

355:                                              ; preds = %351
  %356 = va_arg i8** %10, i32
  store i32 %356, i32* %27, align 4
  %357 = load i32, i32* %27, align 4
  %358 = trunc i32 %357 to i16
  %359 = sext i16 %358 to i32
  br label %363

360:                                              ; preds = %351
  %361 = va_arg i8** %10, i32
  store i32 %361, i32* %28, align 4
  %362 = load i32, i32* %28, align 4
  br label %363

363:                                              ; preds = %360, %355
  %364 = phi i32 [ %359, %355 ], [ %362, %360 ]
  br label %365

365:                                              ; preds = %363, %346
  %366 = phi i32 [ %350, %346 ], [ %364, %363 ]
  store i32 %366, i32* %25, align 4
  %367 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %368 = load i8*, i8** %7, align 8
  %369 = load i64, i64* %15, align 8
  %370 = load i64, i64* %8, align 8
  %371 = load i32, i32* %25, align 4
  %372 = icmp sgt i32 %371, 0
  br i1 %372, label %373, label %375

373:                                              ; preds = %365
  %374 = load i32, i32* %25, align 4
  br label %378

375:                                              ; preds = %365
  %376 = load i32, i32* %25, align 4
  %377 = sub nsw i32 0, %376
  br label %378

378:                                              ; preds = %375, %373
  %379 = phi i32 [ %374, %373 ], [ %377, %375 ]
  %380 = zext i32 %379 to i64
  %381 = load i32, i32* %25, align 4
  %382 = icmp slt i32 %381, 0
  %383 = load i32, i32* %20, align 4
  %384 = zext i32 %383 to i64
  %385 = load i32, i32* %13, align 4
  %386 = load i32, i32* %12, align 4
  %387 = load i32, i32* %11, align 4
  %388 = call i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %367, i8* noundef %368, i64 noundef %369, i64 noundef %370, i64 noundef %380, i1 noundef zeroext %382, i64 noundef %384, i32 noundef %385, i32 noundef %386, i32 noundef %387)
  store i64 %388, i64* %15, align 8
  br label %389

389:                                              ; preds = %378, %332
  br label %390

390:                                              ; preds = %389, %304
  br label %464

391:                                              ; preds = %281
  %392 = load i32, i32* %11, align 4
  %393 = and i32 %392, 512
  %394 = icmp ne i32 %393, 0
  br i1 %394, label %395, label %408

395:                                              ; preds = %391
  %396 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %397 = load i8*, i8** %7, align 8
  %398 = load i64, i64* %15, align 8
  %399 = load i64, i64* %8, align 8
  %400 = va_arg i8** %10, i64
  store i64 %400, i64* %29, align 8
  %401 = load i64, i64* %29, align 8
  %402 = load i32, i32* %20, align 4
  %403 = zext i32 %402 to i64
  %404 = load i32, i32* %13, align 4
  %405 = load i32, i32* %12, align 4
  %406 = load i32, i32* %11, align 4
  %407 = call i64 @_ntoa_long_long(void (i8, i8*, i64, i64)* noundef %396, i8* noundef %397, i64 noundef %398, i64 noundef %399, i64 noundef %401, i1 noundef zeroext false, i64 noundef %403, i32 noundef %404, i32 noundef %405, i32 noundef %406)
  store i64 %407, i64* %15, align 8
  br label %463

408:                                              ; preds = %391
  %409 = load i32, i32* %11, align 4
  %410 = and i32 %409, 256
  %411 = icmp ne i32 %410, 0
  br i1 %411, label %412, label %425

412:                                              ; preds = %408
  %413 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %414 = load i8*, i8** %7, align 8
  %415 = load i64, i64* %15, align 8
  %416 = load i64, i64* %8, align 8
  %417 = va_arg i8** %10, i64
  store i64 %417, i64* %30, align 8
  %418 = load i64, i64* %30, align 8
  %419 = load i32, i32* %20, align 4
  %420 = zext i32 %419 to i64
  %421 = load i32, i32* %13, align 4
  %422 = load i32, i32* %12, align 4
  %423 = load i32, i32* %11, align 4
  %424 = call i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %413, i8* noundef %414, i64 noundef %415, i64 noundef %416, i64 noundef %418, i1 noundef zeroext false, i64 noundef %420, i32 noundef %421, i32 noundef %422, i32 noundef %423)
  store i64 %424, i64* %15, align 8
  br label %462

425:                                              ; preds = %408
  %426 = load i32, i32* %11, align 4
  %427 = and i32 %426, 64
  %428 = icmp ne i32 %427, 0
  br i1 %428, label %429, label %434

429:                                              ; preds = %425
  %430 = va_arg i8** %10, i32
  store i32 %430, i32* %32, align 4
  %431 = load i32, i32* %32, align 4
  %432 = trunc i32 %431 to i8
  %433 = zext i8 %432 to i32
  br label %448

434:                                              ; preds = %425
  %435 = load i32, i32* %11, align 4
  %436 = and i32 %435, 128
  %437 = icmp ne i32 %436, 0
  br i1 %437, label %438, label %443

438:                                              ; preds = %434
  %439 = va_arg i8** %10, i32
  store i32 %439, i32* %33, align 4
  %440 = load i32, i32* %33, align 4
  %441 = trunc i32 %440 to i16
  %442 = zext i16 %441 to i32
  br label %446

443:                                              ; preds = %434
  %444 = va_arg i8** %10, i32
  store i32 %444, i32* %34, align 4
  %445 = load i32, i32* %34, align 4
  br label %446

446:                                              ; preds = %443, %438
  %447 = phi i32 [ %442, %438 ], [ %445, %443 ]
  br label %448

448:                                              ; preds = %446, %429
  %449 = phi i32 [ %433, %429 ], [ %447, %446 ]
  store i32 %449, i32* %31, align 4
  %450 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %451 = load i8*, i8** %7, align 8
  %452 = load i64, i64* %15, align 8
  %453 = load i64, i64* %8, align 8
  %454 = load i32, i32* %31, align 4
  %455 = zext i32 %454 to i64
  %456 = load i32, i32* %20, align 4
  %457 = zext i32 %456 to i64
  %458 = load i32, i32* %13, align 4
  %459 = load i32, i32* %12, align 4
  %460 = load i32, i32* %11, align 4
  %461 = call i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %450, i8* noundef %451, i64 noundef %452, i64 noundef %453, i64 noundef %455, i1 noundef zeroext false, i64 noundef %457, i32 noundef %458, i32 noundef %459, i32 noundef %460)
  store i64 %461, i64* %15, align 8
  br label %462

462:                                              ; preds = %448, %412
  br label %463

463:                                              ; preds = %462, %395
  br label %464

464:                                              ; preds = %463, %390
  %465 = load i8*, i8** %9, align 8
  %466 = getelementptr inbounds i8, i8* %465, i32 1
  store i8* %466, i8** %9, align 8
  br label %696

467:                                              ; preds = %216, %216
  %468 = load i8*, i8** %9, align 8
  %469 = load i8, i8* %468, align 1
  %470 = sext i8 %469 to i32
  %471 = icmp eq i32 %470, 70
  br i1 %471, label %472, label %475

472:                                              ; preds = %467
  %473 = load i32, i32* %11, align 4
  %474 = or i32 %473, 32
  store i32 %474, i32* %11, align 4
  br label %475

475:                                              ; preds = %472, %467
  %476 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %477 = load i8*, i8** %7, align 8
  %478 = load i64, i64* %15, align 8
  %479 = load i64, i64* %8, align 8
  %480 = va_arg i8** %10, double
  store double %480, double* %35, align 8
  %481 = load double, double* %35, align 8
  %482 = load i32, i32* %13, align 4
  %483 = load i32, i32* %12, align 4
  %484 = load i32, i32* %11, align 4
  %485 = call i64 @_ftoa(void (i8, i8*, i64, i64)* noundef %476, i8* noundef %477, i64 noundef %478, i64 noundef %479, double noundef %481, i32 noundef %482, i32 noundef %483, i32 noundef %484)
  store i64 %485, i64* %15, align 8
  %486 = load i8*, i8** %9, align 8
  %487 = getelementptr inbounds i8, i8* %486, i32 1
  store i8* %487, i8** %9, align 8
  br label %696

488:                                              ; preds = %216, %216, %216, %216
  %489 = load i8*, i8** %9, align 8
  %490 = load i8, i8* %489, align 1
  %491 = sext i8 %490 to i32
  %492 = icmp eq i32 %491, 103
  br i1 %492, label %498, label %493

493:                                              ; preds = %488
  %494 = load i8*, i8** %9, align 8
  %495 = load i8, i8* %494, align 1
  %496 = sext i8 %495 to i32
  %497 = icmp eq i32 %496, 71
  br i1 %497, label %498, label %501

498:                                              ; preds = %493, %488
  %499 = load i32, i32* %11, align 4
  %500 = or i32 %499, 2048
  store i32 %500, i32* %11, align 4
  br label %501

501:                                              ; preds = %498, %493
  %502 = load i8*, i8** %9, align 8
  %503 = load i8, i8* %502, align 1
  %504 = sext i8 %503 to i32
  %505 = icmp eq i32 %504, 69
  br i1 %505, label %511, label %506

506:                                              ; preds = %501
  %507 = load i8*, i8** %9, align 8
  %508 = load i8, i8* %507, align 1
  %509 = sext i8 %508 to i32
  %510 = icmp eq i32 %509, 71
  br i1 %510, label %511, label %514

511:                                              ; preds = %506, %501
  %512 = load i32, i32* %11, align 4
  %513 = or i32 %512, 32
  store i32 %513, i32* %11, align 4
  br label %514

514:                                              ; preds = %511, %506
  %515 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %516 = load i8*, i8** %7, align 8
  %517 = load i64, i64* %15, align 8
  %518 = load i64, i64* %8, align 8
  %519 = va_arg i8** %10, double
  store double %519, double* %36, align 8
  %520 = load double, double* %36, align 8
  %521 = load i32, i32* %13, align 4
  %522 = load i32, i32* %12, align 4
  %523 = load i32, i32* %11, align 4
  %524 = call i64 @_etoa(void (i8, i8*, i64, i64)* noundef %515, i8* noundef %516, i64 noundef %517, i64 noundef %518, double noundef %520, i32 noundef %521, i32 noundef %522, i32 noundef %523)
  store i64 %524, i64* %15, align 8
  %525 = load i8*, i8** %9, align 8
  %526 = getelementptr inbounds i8, i8* %525, i32 1
  store i8* %526, i8** %9, align 8
  br label %696

527:                                              ; preds = %216
  store i32 1, i32* %37, align 4
  %528 = load i32, i32* %11, align 4
  %529 = and i32 %528, 2
  %530 = icmp ne i32 %529, 0
  br i1 %530, label %544, label %531

531:                                              ; preds = %527
  br label %532

532:                                              ; preds = %537, %531
  %533 = load i32, i32* %37, align 4
  %534 = add i32 %533, 1
  store i32 %534, i32* %37, align 4
  %535 = load i32, i32* %12, align 4
  %536 = icmp ult i32 %533, %535
  br i1 %536, label %537, label %543

537:                                              ; preds = %532
  %538 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %539 = load i8*, i8** %7, align 8
  %540 = load i64, i64* %15, align 8
  %541 = add i64 %540, 1
  store i64 %541, i64* %15, align 8
  %542 = load i64, i64* %8, align 8
  call void %538(i8 noundef signext 32, i8* noundef %539, i64 noundef %540, i64 noundef %542)
  br label %532, !llvm.loop !12

543:                                              ; preds = %532
  br label %544

544:                                              ; preds = %543, %527
  %545 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %546 = va_arg i8** %10, i32
  store i32 %546, i32* %38, align 4
  %547 = load i32, i32* %38, align 4
  %548 = trunc i32 %547 to i8
  %549 = load i8*, i8** %7, align 8
  %550 = load i64, i64* %15, align 8
  %551 = add i64 %550, 1
  store i64 %551, i64* %15, align 8
  %552 = load i64, i64* %8, align 8
  call void %545(i8 noundef signext %548, i8* noundef %549, i64 noundef %550, i64 noundef %552)
  %553 = load i32, i32* %11, align 4
  %554 = and i32 %553, 2
  %555 = icmp ne i32 %554, 0
  br i1 %555, label %556, label %569

556:                                              ; preds = %544
  br label %557

557:                                              ; preds = %562, %556
  %558 = load i32, i32* %37, align 4
  %559 = add i32 %558, 1
  store i32 %559, i32* %37, align 4
  %560 = load i32, i32* %12, align 4
  %561 = icmp ult i32 %558, %560
  br i1 %561, label %562, label %568

562:                                              ; preds = %557
  %563 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %564 = load i8*, i8** %7, align 8
  %565 = load i64, i64* %15, align 8
  %566 = add i64 %565, 1
  store i64 %566, i64* %15, align 8
  %567 = load i64, i64* %8, align 8
  call void %563(i8 noundef signext 32, i8* noundef %564, i64 noundef %565, i64 noundef %567)
  br label %557, !llvm.loop !13

568:                                              ; preds = %557
  br label %569

569:                                              ; preds = %568, %544
  %570 = load i8*, i8** %9, align 8
  %571 = getelementptr inbounds i8, i8* %570, i32 1
  store i8* %571, i8** %9, align 8
  br label %696

572:                                              ; preds = %216
  %573 = va_arg i8** %10, i8*
  store i8* %573, i8** %40, align 8
  %574 = load i8*, i8** %40, align 8
  store i8* %574, i8** %39, align 8
  %575 = load i8*, i8** %39, align 8
  %576 = load i32, i32* %13, align 4
  %577 = icmp ne i32 %576, 0
  br i1 %577, label %578, label %581

578:                                              ; preds = %572
  %579 = load i32, i32* %13, align 4
  %580 = zext i32 %579 to i64
  br label %582

581:                                              ; preds = %572
  br label %582

582:                                              ; preds = %581, %578
  %583 = phi i64 [ %580, %578 ], [ -1, %581 ]
  %584 = call i32 @_strnlen_s(i8* noundef %575, i64 noundef %583)
  store i32 %584, i32* %41, align 4
  %585 = load i32, i32* %11, align 4
  %586 = and i32 %585, 1024
  %587 = icmp ne i32 %586, 0
  br i1 %587, label %588, label %598

588:                                              ; preds = %582
  %589 = load i32, i32* %41, align 4
  %590 = load i32, i32* %13, align 4
  %591 = icmp ult i32 %589, %590
  br i1 %591, label %592, label %594

592:                                              ; preds = %588
  %593 = load i32, i32* %41, align 4
  br label %596

594:                                              ; preds = %588
  %595 = load i32, i32* %13, align 4
  br label %596

596:                                              ; preds = %594, %592
  %597 = phi i32 [ %593, %592 ], [ %595, %594 ]
  store i32 %597, i32* %41, align 4
  br label %598

598:                                              ; preds = %596, %582
  %599 = load i32, i32* %11, align 4
  %600 = and i32 %599, 2
  %601 = icmp ne i32 %600, 0
  br i1 %601, label %615, label %602

602:                                              ; preds = %598
  br label %603

603:                                              ; preds = %608, %602
  %604 = load i32, i32* %41, align 4
  %605 = add i32 %604, 1
  store i32 %605, i32* %41, align 4
  %606 = load i32, i32* %12, align 4
  %607 = icmp ult i32 %604, %606
  br i1 %607, label %608, label %614

608:                                              ; preds = %603
  %609 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %610 = load i8*, i8** %7, align 8
  %611 = load i64, i64* %15, align 8
  %612 = add i64 %611, 1
  store i64 %612, i64* %15, align 8
  %613 = load i64, i64* %8, align 8
  call void %609(i8 noundef signext 32, i8* noundef %610, i64 noundef %611, i64 noundef %613)
  br label %603, !llvm.loop !14

614:                                              ; preds = %603
  br label %615

615:                                              ; preds = %614, %598
  br label %616

616:                                              ; preds = %633, %615
  %617 = load i8*, i8** %39, align 8
  %618 = load i8, i8* %617, align 1
  %619 = sext i8 %618 to i32
  %620 = icmp ne i32 %619, 0
  br i1 %620, label %621, label %631

621:                                              ; preds = %616
  %622 = load i32, i32* %11, align 4
  %623 = and i32 %622, 1024
  %624 = icmp ne i32 %623, 0
  br i1 %624, label %625, label %629

625:                                              ; preds = %621
  %626 = load i32, i32* %13, align 4
  %627 = add i32 %626, -1
  store i32 %627, i32* %13, align 4
  %628 = icmp ne i32 %626, 0
  br label %629

629:                                              ; preds = %625, %621
  %630 = phi i1 [ true, %621 ], [ %628, %625 ]
  br label %631

631:                                              ; preds = %629, %616
  %632 = phi i1 [ false, %616 ], [ %630, %629 ]
  br i1 %632, label %633, label %642

633:                                              ; preds = %631
  %634 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %635 = load i8*, i8** %39, align 8
  %636 = getelementptr inbounds i8, i8* %635, i32 1
  store i8* %636, i8** %39, align 8
  %637 = load i8, i8* %635, align 1
  %638 = load i8*, i8** %7, align 8
  %639 = load i64, i64* %15, align 8
  %640 = add i64 %639, 1
  store i64 %640, i64* %15, align 8
  %641 = load i64, i64* %8, align 8
  call void %634(i8 noundef signext %637, i8* noundef %638, i64 noundef %639, i64 noundef %641)
  br label %616, !llvm.loop !15

642:                                              ; preds = %631
  %643 = load i32, i32* %11, align 4
  %644 = and i32 %643, 2
  %645 = icmp ne i32 %644, 0
  br i1 %645, label %646, label %659

646:                                              ; preds = %642
  br label %647

647:                                              ; preds = %652, %646
  %648 = load i32, i32* %41, align 4
  %649 = add i32 %648, 1
  store i32 %649, i32* %41, align 4
  %650 = load i32, i32* %12, align 4
  %651 = icmp ult i32 %648, %650
  br i1 %651, label %652, label %658

652:                                              ; preds = %647
  %653 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %654 = load i8*, i8** %7, align 8
  %655 = load i64, i64* %15, align 8
  %656 = add i64 %655, 1
  store i64 %656, i64* %15, align 8
  %657 = load i64, i64* %8, align 8
  call void %653(i8 noundef signext 32, i8* noundef %654, i64 noundef %655, i64 noundef %657)
  br label %647, !llvm.loop !16

658:                                              ; preds = %647
  br label %659

659:                                              ; preds = %658, %642
  %660 = load i8*, i8** %9, align 8
  %661 = getelementptr inbounds i8, i8* %660, i32 1
  store i8* %661, i8** %9, align 8
  br label %696

662:                                              ; preds = %216
  store i32 16, i32* %12, align 4
  %663 = load i32, i32* %11, align 4
  %664 = or i32 %663, 33
  store i32 %664, i32* %11, align 4
  store i8 1, i8* %42, align 1
  %665 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %666 = load i8*, i8** %7, align 8
  %667 = load i64, i64* %15, align 8
  %668 = load i64, i64* %8, align 8
  %669 = va_arg i8** %10, i8*
  store i8* %669, i8** %43, align 8
  %670 = load i8*, i8** %43, align 8
  %671 = ptrtoint i8* %670 to i64
  %672 = load i32, i32* %13, align 4
  %673 = load i32, i32* %12, align 4
  %674 = load i32, i32* %11, align 4
  %675 = call i64 @_ntoa_long_long(void (i8, i8*, i64, i64)* noundef %665, i8* noundef %666, i64 noundef %667, i64 noundef %668, i64 noundef %671, i1 noundef zeroext false, i64 noundef 16, i32 noundef %672, i32 noundef %673, i32 noundef %674)
  store i64 %675, i64* %15, align 8
  %676 = load i8*, i8** %9, align 8
  %677 = getelementptr inbounds i8, i8* %676, i32 1
  store i8* %677, i8** %9, align 8
  br label %696

678:                                              ; preds = %216
  %679 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %680 = load i8*, i8** %7, align 8
  %681 = load i64, i64* %15, align 8
  %682 = add i64 %681, 1
  store i64 %682, i64* %15, align 8
  %683 = load i64, i64* %8, align 8
  call void %679(i8 noundef signext 37, i8* noundef %680, i64 noundef %681, i64 noundef %683)
  %684 = load i8*, i8** %9, align 8
  %685 = getelementptr inbounds i8, i8* %684, i32 1
  store i8* %685, i8** %9, align 8
  br label %696

686:                                              ; preds = %216
  %687 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %688 = load i8*, i8** %9, align 8
  %689 = load i8, i8* %688, align 1
  %690 = load i8*, i8** %7, align 8
  %691 = load i64, i64* %15, align 8
  %692 = add i64 %691, 1
  store i64 %692, i64* %15, align 8
  %693 = load i64, i64* %8, align 8
  call void %687(i8 noundef signext %689, i8* noundef %690, i64 noundef %691, i64 noundef %693)
  %694 = load i8*, i8** %9, align 8
  %695 = getelementptr inbounds i8, i8* %694, i32 1
  store i8* %695, i8** %9, align 8
  br label %696

696:                                              ; preds = %686, %678, %662, %659, %569, %514, %475, %464
  br label %48, !llvm.loop !9

697:                                              ; preds = %48
  %698 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %6, align 8
  %699 = load i8*, i8** %7, align 8
  %700 = load i64, i64* %15, align 8
  %701 = load i64, i64* %8, align 8
  %702 = icmp ult i64 %700, %701
  br i1 %702, label %703, label %705

703:                                              ; preds = %697
  %704 = load i64, i64* %15, align 8
  br label %708

705:                                              ; preds = %697
  %706 = load i64, i64* %8, align 8
  %707 = sub i64 %706, 1
  br label %708

708:                                              ; preds = %705, %703
  %709 = phi i64 [ %704, %703 ], [ %707, %705 ]
  %710 = load i64, i64* %8, align 8
  call void %698(i8 noundef signext 0, i8* noundef %699, i64 noundef %709, i64 noundef %710)
  %711 = load i64, i64* %15, align 8
  %712 = trunc i64 %711 to i32
  ret i32 %712
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @_out_char(i8 noundef signext %0, i8* noundef %1, i64 noundef %2, i64 noundef %3) #0 {
  %5 = alloca i8, align 1
  %6 = alloca i8*, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store i8 %0, i8* %5, align 1
  store i8* %1, i8** %6, align 8
  store i64 %2, i64* %7, align 8
  store i64 %3, i64* %8, align 8
  %9 = load i8*, i8** %6, align 8
  %10 = load i64, i64* %7, align 8
  %11 = load i64, i64* %8, align 8
  %12 = load i8, i8* %5, align 1
  %13 = icmp ne i8 %12, 0
  br i1 %13, label %14, label %16

14:                                               ; preds = %4
  %15 = load i8, i8* %5, align 1
  call void @_putchar(i8 noundef signext %15)
  br label %16

16:                                               ; preds = %14, %4
  ret void
}

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_end(i8*) #2

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
  %11 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_buffer, i8* noundef %8, i64 noundef -1, i8* noundef %9, i8* noundef %10)
  store i32 %11, i32* %6, align 4
  %12 = bitcast i8** %5 to i8*
  call void @llvm.va_end(i8* %12)
  %13 = load i32, i32* %6, align 4
  ret i32 %13
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @_out_buffer(i8 noundef signext %0, i8* noundef %1, i64 noundef %2, i64 noundef %3) #0 {
  %5 = alloca i8, align 1
  %6 = alloca i8*, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store i8 %0, i8* %5, align 1
  store i8* %1, i8** %6, align 8
  store i64 %2, i64* %7, align 8
  store i64 %3, i64* %8, align 8
  %9 = load i64, i64* %7, align 8
  %10 = load i64, i64* %8, align 8
  %11 = icmp ult i64 %9, %10
  br i1 %11, label %12, label %17

12:                                               ; preds = %4
  %13 = load i8, i8* %5, align 1
  %14 = load i8*, i8** %6, align 8
  %15 = load i64, i64* %7, align 8
  %16 = getelementptr inbounds i8, i8* %14, i64 %15
  store i8 %13, i8* %16, align 1
  br label %17

17:                                               ; preds = %12, %4
  ret void
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
  %14 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_buffer, i8* noundef %10, i64 noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vprintf_(i8* noundef %0, i8* noundef %1) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i8*, align 8
  %5 = alloca [1 x i8], align 1
  store i8* %0, i8** %3, align 8
  store i8* %1, i8** %4, align 8
  %6 = getelementptr inbounds [1 x i8], [1 x i8]* %5, i64 0, i64 0
  %7 = load i8*, i8** %3, align 8
  %8 = load i8*, i8** %4, align 8
  %9 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_char, i8* noundef %6, i64 noundef -1, i8* noundef %7, i8* noundef %8)
  ret i32 %9
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @vsnprintf_(i8* noundef %0, i64 noundef %1, i8* noundef %2, i8* noundef %3) #0 {
  %5 = alloca i8*, align 8
  %6 = alloca i64, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i8*, align 8
  store i8* %0, i8** %5, align 8
  store i64 %1, i64* %6, align 8
  store i8* %2, i8** %7, align 8
  store i8* %3, i8** %8, align 8
  %9 = load i8*, i8** %5, align 8
  %10 = load i64, i64* %6, align 8
  %11 = load i8*, i8** %7, align 8
  %12 = load i8*, i8** %8, align 8
  %13 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_buffer, i8* noundef %9, i64 noundef %10, i8* noundef %11, i8* noundef %12)
  ret i32 %13
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @fctprintf(void (i8, i8*)* noundef %0, i8* noundef %1, i8* noundef %2, ...) #0 {
  %4 = alloca void (i8, i8*)*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca %struct.out_fct_wrap_type, align 8
  %9 = alloca i32, align 4
  store void (i8, i8*)* %0, void (i8, i8*)** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  %10 = bitcast i8** %7 to i8*
  call void @llvm.va_start(i8* %10)
  %11 = getelementptr inbounds %struct.out_fct_wrap_type, %struct.out_fct_wrap_type* %8, i32 0, i32 0
  %12 = load void (i8, i8*)*, void (i8, i8*)** %4, align 8
  store void (i8, i8*)* %12, void (i8, i8*)** %11, align 8
  %13 = getelementptr inbounds %struct.out_fct_wrap_type, %struct.out_fct_wrap_type* %8, i32 0, i32 1
  %14 = load i8*, i8** %5, align 8
  store i8* %14, i8** %13, align 8
  %15 = ptrtoint %struct.out_fct_wrap_type* %8 to i64
  %16 = inttoptr i64 %15 to i8*
  %17 = load i8*, i8** %6, align 8
  %18 = load i8*, i8** %7, align 8
  %19 = call i32 @_vsnprintf(void (i8, i8*, i64, i64)* noundef @_out_fct, i8* noundef %16, i64 noundef -1, i8* noundef %17, i8* noundef %18)
  store i32 %19, i32* %9, align 4
  %20 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %20)
  %21 = load i32, i32* %9, align 4
  ret i32 %21
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @_out_fct(i8 noundef signext %0, i8* noundef %1, i64 noundef %2, i64 noundef %3) #0 {
  %5 = alloca i8, align 1
  %6 = alloca i8*, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store i8 %0, i8* %5, align 1
  store i8* %1, i8** %6, align 8
  store i64 %2, i64* %7, align 8
  store i64 %3, i64* %8, align 8
  %9 = load i64, i64* %7, align 8
  %10 = load i64, i64* %8, align 8
  %11 = load i8, i8* %5, align 1
  %12 = icmp ne i8 %11, 0
  br i1 %12, label %13, label %23

13:                                               ; preds = %4
  %14 = load i8*, i8** %6, align 8
  %15 = bitcast i8* %14 to %struct.out_fct_wrap_type*
  %16 = getelementptr inbounds %struct.out_fct_wrap_type, %struct.out_fct_wrap_type* %15, i32 0, i32 0
  %17 = load void (i8, i8*)*, void (i8, i8*)** %16, align 8
  %18 = load i8, i8* %5, align 1
  %19 = load i8*, i8** %6, align 8
  %20 = bitcast i8* %19 to %struct.out_fct_wrap_type*
  %21 = getelementptr inbounds %struct.out_fct_wrap_type, %struct.out_fct_wrap_type* %20, i32 0, i32 1
  %22 = load i8*, i8** %21, align 8
  call void %17(i8 noundef signext %18, i8* noundef %22)
  br label %23

23:                                               ; preds = %13, %4
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal void @_out_null(i8 noundef signext %0, i8* noundef %1, i64 noundef %2, i64 noundef %3) #0 {
  %5 = alloca i8, align 1
  %6 = alloca i8*, align 8
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  store i8 %0, i8* %5, align 1
  store i8* %1, i8** %6, align 8
  store i64 %2, i64* %7, align 8
  store i64 %3, i64* %8, align 8
  %9 = load i8, i8* %5, align 1
  %10 = load i8*, i8** %6, align 8
  %11 = load i64, i64* %7, align 8
  %12 = load i64, i64* %8, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal zeroext i1 @_is_digit(i8 noundef signext %0) #0 {
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
define internal i32 @_atoi(i8** noundef %0) #0 {
  %2 = alloca i8**, align 8
  %3 = alloca i32, align 4
  store i8** %0, i8*** %2, align 8
  store i32 0, i32* %3, align 4
  br label %4

4:                                                ; preds = %9, %1
  %5 = load i8**, i8*** %2, align 8
  %6 = load i8*, i8** %5, align 8
  %7 = load i8, i8* %6, align 1
  %8 = call zeroext i1 @_is_digit(i8 noundef signext %7)
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
  br label %4, !llvm.loop !17

19:                                               ; preds = %4
  %20 = load i32, i32* %3, align 4
  ret i32 %20
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_ntoa_long_long(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, i64 noundef %4, i1 noundef zeroext %5, i64 noundef %6, i32 noundef %7, i32 noundef %8, i32 noundef %9) #0 {
  %11 = alloca void (i8, i8*, i64, i64)*, align 8
  %12 = alloca i8*, align 8
  %13 = alloca i64, align 8
  %14 = alloca i64, align 8
  %15 = alloca i64, align 8
  %16 = alloca i8, align 1
  %17 = alloca i64, align 8
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca [32 x i8], align 1
  %22 = alloca i64, align 8
  %23 = alloca i8, align 1
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %11, align 8
  store i8* %1, i8** %12, align 8
  store i64 %2, i64* %13, align 8
  store i64 %3, i64* %14, align 8
  store i64 %4, i64* %15, align 8
  %24 = zext i1 %5 to i8
  store i8 %24, i8* %16, align 1
  store i64 %6, i64* %17, align 8
  store i32 %7, i32* %18, align 4
  store i32 %8, i32* %19, align 4
  store i32 %9, i32* %20, align 4
  store i64 0, i64* %22, align 8
  %25 = load i64, i64* %15, align 8
  %26 = icmp ne i64 %25, 0
  br i1 %26, label %30, label %27

27:                                               ; preds = %10
  %28 = load i32, i32* %20, align 4
  %29 = and i32 %28, -17
  store i32 %29, i32* %20, align 4
  br label %30

30:                                               ; preds = %27, %10
  %31 = load i32, i32* %20, align 4
  %32 = and i32 %31, 1024
  %33 = icmp ne i32 %32, 0
  br i1 %33, label %34, label %37

34:                                               ; preds = %30
  %35 = load i64, i64* %15, align 8
  %36 = icmp ne i64 %35, 0
  br i1 %36, label %37, label %78

37:                                               ; preds = %34, %30
  br label %38

38:                                               ; preds = %75, %37
  %39 = load i64, i64* %15, align 8
  %40 = load i64, i64* %17, align 8
  %41 = urem i64 %39, %40
  %42 = trunc i64 %41 to i8
  store i8 %42, i8* %23, align 1
  %43 = load i8, i8* %23, align 1
  %44 = sext i8 %43 to i32
  %45 = icmp slt i32 %44, 10
  br i1 %45, label %46, label %50

46:                                               ; preds = %38
  %47 = load i8, i8* %23, align 1
  %48 = sext i8 %47 to i32
  %49 = add nsw i32 48, %48
  br label %60

50:                                               ; preds = %38
  %51 = load i32, i32* %20, align 4
  %52 = and i32 %51, 32
  %53 = icmp ne i32 %52, 0
  %54 = zext i1 %53 to i64
  %55 = select i1 %53, i32 65, i32 97
  %56 = load i8, i8* %23, align 1
  %57 = sext i8 %56 to i32
  %58 = add nsw i32 %55, %57
  %59 = sub nsw i32 %58, 10
  br label %60

60:                                               ; preds = %50, %46
  %61 = phi i32 [ %49, %46 ], [ %59, %50 ]
  %62 = trunc i32 %61 to i8
  %63 = load i64, i64* %22, align 8
  %64 = add i64 %63, 1
  store i64 %64, i64* %22, align 8
  %65 = getelementptr inbounds [32 x i8], [32 x i8]* %21, i64 0, i64 %63
  store i8 %62, i8* %65, align 1
  %66 = load i64, i64* %17, align 8
  %67 = load i64, i64* %15, align 8
  %68 = udiv i64 %67, %66
  store i64 %68, i64* %15, align 8
  br label %69

69:                                               ; preds = %60
  %70 = load i64, i64* %15, align 8
  %71 = icmp ne i64 %70, 0
  br i1 %71, label %72, label %75

72:                                               ; preds = %69
  %73 = load i64, i64* %22, align 8
  %74 = icmp ult i64 %73, 32
  br label %75

75:                                               ; preds = %72, %69
  %76 = phi i1 [ false, %69 ], [ %74, %72 ]
  br i1 %76, label %38, label %77, !llvm.loop !18

77:                                               ; preds = %75
  br label %78

78:                                               ; preds = %77, %34
  %79 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %11, align 8
  %80 = load i8*, i8** %12, align 8
  %81 = load i64, i64* %13, align 8
  %82 = load i64, i64* %14, align 8
  %83 = getelementptr inbounds [32 x i8], [32 x i8]* %21, i64 0, i64 0
  %84 = load i64, i64* %22, align 8
  %85 = load i8, i8* %16, align 1
  %86 = trunc i8 %85 to i1
  %87 = load i64, i64* %17, align 8
  %88 = trunc i64 %87 to i32
  %89 = load i32, i32* %18, align 4
  %90 = load i32, i32* %19, align 4
  %91 = load i32, i32* %20, align 4
  %92 = call i64 @_ntoa_format(void (i8, i8*, i64, i64)* noundef %79, i8* noundef %80, i64 noundef %81, i64 noundef %82, i8* noundef %83, i64 noundef %84, i1 noundef zeroext %86, i32 noundef %88, i32 noundef %89, i32 noundef %90, i32 noundef %91)
  ret i64 %92
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, i64 noundef %4, i1 noundef zeroext %5, i64 noundef %6, i32 noundef %7, i32 noundef %8, i32 noundef %9) #0 {
  %11 = alloca void (i8, i8*, i64, i64)*, align 8
  %12 = alloca i8*, align 8
  %13 = alloca i64, align 8
  %14 = alloca i64, align 8
  %15 = alloca i64, align 8
  %16 = alloca i8, align 1
  %17 = alloca i64, align 8
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca [32 x i8], align 1
  %22 = alloca i64, align 8
  %23 = alloca i8, align 1
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %11, align 8
  store i8* %1, i8** %12, align 8
  store i64 %2, i64* %13, align 8
  store i64 %3, i64* %14, align 8
  store i64 %4, i64* %15, align 8
  %24 = zext i1 %5 to i8
  store i8 %24, i8* %16, align 1
  store i64 %6, i64* %17, align 8
  store i32 %7, i32* %18, align 4
  store i32 %8, i32* %19, align 4
  store i32 %9, i32* %20, align 4
  store i64 0, i64* %22, align 8
  %25 = load i64, i64* %15, align 8
  %26 = icmp ne i64 %25, 0
  br i1 %26, label %30, label %27

27:                                               ; preds = %10
  %28 = load i32, i32* %20, align 4
  %29 = and i32 %28, -17
  store i32 %29, i32* %20, align 4
  br label %30

30:                                               ; preds = %27, %10
  %31 = load i32, i32* %20, align 4
  %32 = and i32 %31, 1024
  %33 = icmp ne i32 %32, 0
  br i1 %33, label %34, label %37

34:                                               ; preds = %30
  %35 = load i64, i64* %15, align 8
  %36 = icmp ne i64 %35, 0
  br i1 %36, label %37, label %78

37:                                               ; preds = %34, %30
  br label %38

38:                                               ; preds = %75, %37
  %39 = load i64, i64* %15, align 8
  %40 = load i64, i64* %17, align 8
  %41 = urem i64 %39, %40
  %42 = trunc i64 %41 to i8
  store i8 %42, i8* %23, align 1
  %43 = load i8, i8* %23, align 1
  %44 = sext i8 %43 to i32
  %45 = icmp slt i32 %44, 10
  br i1 %45, label %46, label %50

46:                                               ; preds = %38
  %47 = load i8, i8* %23, align 1
  %48 = sext i8 %47 to i32
  %49 = add nsw i32 48, %48
  br label %60

50:                                               ; preds = %38
  %51 = load i32, i32* %20, align 4
  %52 = and i32 %51, 32
  %53 = icmp ne i32 %52, 0
  %54 = zext i1 %53 to i64
  %55 = select i1 %53, i32 65, i32 97
  %56 = load i8, i8* %23, align 1
  %57 = sext i8 %56 to i32
  %58 = add nsw i32 %55, %57
  %59 = sub nsw i32 %58, 10
  br label %60

60:                                               ; preds = %50, %46
  %61 = phi i32 [ %49, %46 ], [ %59, %50 ]
  %62 = trunc i32 %61 to i8
  %63 = load i64, i64* %22, align 8
  %64 = add i64 %63, 1
  store i64 %64, i64* %22, align 8
  %65 = getelementptr inbounds [32 x i8], [32 x i8]* %21, i64 0, i64 %63
  store i8 %62, i8* %65, align 1
  %66 = load i64, i64* %17, align 8
  %67 = load i64, i64* %15, align 8
  %68 = udiv i64 %67, %66
  store i64 %68, i64* %15, align 8
  br label %69

69:                                               ; preds = %60
  %70 = load i64, i64* %15, align 8
  %71 = icmp ne i64 %70, 0
  br i1 %71, label %72, label %75

72:                                               ; preds = %69
  %73 = load i64, i64* %22, align 8
  %74 = icmp ult i64 %73, 32
  br label %75

75:                                               ; preds = %72, %69
  %76 = phi i1 [ false, %69 ], [ %74, %72 ]
  br i1 %76, label %38, label %77, !llvm.loop !19

77:                                               ; preds = %75
  br label %78

78:                                               ; preds = %77, %34
  %79 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %11, align 8
  %80 = load i8*, i8** %12, align 8
  %81 = load i64, i64* %13, align 8
  %82 = load i64, i64* %14, align 8
  %83 = getelementptr inbounds [32 x i8], [32 x i8]* %21, i64 0, i64 0
  %84 = load i64, i64* %22, align 8
  %85 = load i8, i8* %16, align 1
  %86 = trunc i8 %85 to i1
  %87 = load i64, i64* %17, align 8
  %88 = trunc i64 %87 to i32
  %89 = load i32, i32* %18, align 4
  %90 = load i32, i32* %19, align 4
  %91 = load i32, i32* %20, align 4
  %92 = call i64 @_ntoa_format(void (i8, i8*, i64, i64)* noundef %79, i8* noundef %80, i64 noundef %81, i64 noundef %82, i8* noundef %83, i64 noundef %84, i1 noundef zeroext %86, i32 noundef %88, i32 noundef %89, i32 noundef %90, i32 noundef %91)
  ret i64 %92
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_ftoa(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, double noundef %4, i32 noundef %5, i32 noundef %6, i32 noundef %7) #0 {
  %9 = alloca i64, align 8
  %10 = alloca void (i8, i8*, i64, i64)*, align 8
  %11 = alloca i8*, align 8
  %12 = alloca i64, align 8
  %13 = alloca i64, align 8
  %14 = alloca double, align 8
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca [32 x i8], align 1
  %19 = alloca i64, align 8
  %20 = alloca double, align 8
  %21 = alloca i8, align 1
  %22 = alloca i32, align 4
  %23 = alloca double, align 8
  %24 = alloca i64, align 8
  %25 = alloca i32, align 4
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %10, align 8
  store i8* %1, i8** %11, align 8
  store i64 %2, i64* %12, align 8
  store i64 %3, i64* %13, align 8
  store double %4, double* %14, align 8
  store i32 %5, i32* %15, align 4
  store i32 %6, i32* %16, align 4
  store i32 %7, i32* %17, align 4
  store i64 0, i64* %19, align 8
  store double 0.000000e+00, double* %20, align 8
  %26 = load double, double* %14, align 8
  %27 = load double, double* %14, align 8
  %28 = fcmp une double %26, %27
  br i1 %28, label %29, label %37

29:                                               ; preds = %8
  %30 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %31 = load i8*, i8** %11, align 8
  %32 = load i64, i64* %12, align 8
  %33 = load i64, i64* %13, align 8
  %34 = load i32, i32* %16, align 4
  %35 = load i32, i32* %17, align 4
  %36 = call i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %30, i8* noundef %31, i64 noundef %32, i64 noundef %33, i8* noundef getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0), i64 noundef 3, i32 noundef %34, i32 noundef %35)
  store i64 %36, i64* %9, align 8
  br label %318

37:                                               ; preds = %8
  %38 = load double, double* %14, align 8
  %39 = fcmp olt double %38, 0xFFEFFFFFFFFFFFFF
  br i1 %39, label %40, label %48

40:                                               ; preds = %37
  %41 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %42 = load i8*, i8** %11, align 8
  %43 = load i64, i64* %12, align 8
  %44 = load i64, i64* %13, align 8
  %45 = load i32, i32* %16, align 4
  %46 = load i32, i32* %17, align 4
  %47 = call i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %41, i8* noundef %42, i64 noundef %43, i64 noundef %44, i8* noundef getelementptr inbounds ([5 x i8], [5 x i8]* @.str.1, i64 0, i64 0), i64 noundef 4, i32 noundef %45, i32 noundef %46)
  store i64 %47, i64* %9, align 8
  br label %318

48:                                               ; preds = %37
  %49 = load double, double* %14, align 8
  %50 = fcmp ogt double %49, 0x7FEFFFFFFFFFFFFF
  br i1 %50, label %51, label %70

51:                                               ; preds = %48
  %52 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %53 = load i8*, i8** %11, align 8
  %54 = load i64, i64* %12, align 8
  %55 = load i64, i64* %13, align 8
  %56 = load i32, i32* %17, align 4
  %57 = and i32 %56, 4
  %58 = icmp ne i32 %57, 0
  %59 = zext i1 %58 to i64
  %60 = select i1 %58, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i64 0, i64 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.3, i64 0, i64 0)
  %61 = load i32, i32* %17, align 4
  %62 = and i32 %61, 4
  %63 = icmp ne i32 %62, 0
  %64 = zext i1 %63 to i64
  %65 = select i1 %63, i32 4, i32 3
  %66 = zext i32 %65 to i64
  %67 = load i32, i32* %16, align 4
  %68 = load i32, i32* %17, align 4
  %69 = call i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %52, i8* noundef %53, i64 noundef %54, i64 noundef %55, i8* noundef %60, i64 noundef %66, i32 noundef %67, i32 noundef %68)
  store i64 %69, i64* %9, align 8
  br label %318

70:                                               ; preds = %48
  %71 = load double, double* %14, align 8
  %72 = fcmp ogt double %71, 1.000000e+09
  br i1 %72, label %76, label %73

73:                                               ; preds = %70
  %74 = load double, double* %14, align 8
  %75 = fcmp olt double %74, -1.000000e+09
  br i1 %75, label %76, label %86

76:                                               ; preds = %73, %70
  %77 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %78 = load i8*, i8** %11, align 8
  %79 = load i64, i64* %12, align 8
  %80 = load i64, i64* %13, align 8
  %81 = load double, double* %14, align 8
  %82 = load i32, i32* %15, align 4
  %83 = load i32, i32* %16, align 4
  %84 = load i32, i32* %17, align 4
  %85 = call i64 @_etoa(void (i8, i8*, i64, i64)* noundef %77, i8* noundef %78, i64 noundef %79, i64 noundef %80, double noundef %81, i32 noundef %82, i32 noundef %83, i32 noundef %84)
  store i64 %85, i64* %9, align 8
  br label %318

86:                                               ; preds = %73
  store i8 0, i8* %21, align 1
  %87 = load double, double* %14, align 8
  %88 = fcmp olt double %87, 0.000000e+00
  br i1 %88, label %89, label %92

89:                                               ; preds = %86
  store i8 1, i8* %21, align 1
  %90 = load double, double* %14, align 8
  %91 = fsub double 0.000000e+00, %90
  store double %91, double* %14, align 8
  br label %92

92:                                               ; preds = %89, %86
  %93 = load i32, i32* %17, align 4
  %94 = and i32 %93, 1024
  %95 = icmp ne i32 %94, 0
  br i1 %95, label %97, label %96

96:                                               ; preds = %92
  store i32 6, i32* %15, align 4
  br label %97

97:                                               ; preds = %96, %92
  br label %98

98:                                               ; preds = %106, %97
  %99 = load i64, i64* %19, align 8
  %100 = icmp ult i64 %99, 32
  br i1 %100, label %101, label %104

101:                                              ; preds = %98
  %102 = load i32, i32* %15, align 4
  %103 = icmp ugt i32 %102, 9
  br label %104

104:                                              ; preds = %101, %98
  %105 = phi i1 [ false, %98 ], [ %103, %101 ]
  br i1 %105, label %106, label %112

106:                                              ; preds = %104
  %107 = load i64, i64* %19, align 8
  %108 = add i64 %107, 1
  store i64 %108, i64* %19, align 8
  %109 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %107
  store i8 48, i8* %109, align 1
  %110 = load i32, i32* %15, align 4
  %111 = add i32 %110, -1
  store i32 %111, i32* %15, align 4
  br label %98, !llvm.loop !20

112:                                              ; preds = %104
  %113 = load double, double* %14, align 8
  %114 = fptosi double %113 to i32
  store i32 %114, i32* %22, align 4
  %115 = load double, double* %14, align 8
  %116 = load i32, i32* %22, align 4
  %117 = sitofp i32 %116 to double
  %118 = fsub double %115, %117
  %119 = load i32, i32* %15, align 4
  %120 = zext i32 %119 to i64
  %121 = getelementptr inbounds [10 x double], [10 x double]* @_ftoa.pow10, i64 0, i64 %120
  %122 = load double, double* %121, align 8
  %123 = fmul double %118, %122
  store double %123, double* %23, align 8
  %124 = load double, double* %23, align 8
  %125 = fptoui double %124 to i64
  store i64 %125, i64* %24, align 8
  %126 = load double, double* %23, align 8
  %127 = load i64, i64* %24, align 8
  %128 = uitofp i64 %127 to double
  %129 = fsub double %126, %128
  store double %129, double* %20, align 8
  %130 = load double, double* %20, align 8
  %131 = fcmp ogt double %130, 5.000000e-01
  br i1 %131, label %132, label %146

132:                                              ; preds = %112
  %133 = load i64, i64* %24, align 8
  %134 = add i64 %133, 1
  store i64 %134, i64* %24, align 8
  %135 = load i64, i64* %24, align 8
  %136 = uitofp i64 %135 to double
  %137 = load i32, i32* %15, align 4
  %138 = zext i32 %137 to i64
  %139 = getelementptr inbounds [10 x double], [10 x double]* @_ftoa.pow10, i64 0, i64 %138
  %140 = load double, double* %139, align 8
  %141 = fcmp oge double %136, %140
  br i1 %141, label %142, label %145

142:                                              ; preds = %132
  store i64 0, i64* %24, align 8
  %143 = load i32, i32* %22, align 4
  %144 = add nsw i32 %143, 1
  store i32 %144, i32* %22, align 4
  br label %145

145:                                              ; preds = %142, %132
  br label %162

146:                                              ; preds = %112
  %147 = load double, double* %20, align 8
  %148 = fcmp olt double %147, 5.000000e-01
  br i1 %148, label %149, label %150

149:                                              ; preds = %146
  br label %161

150:                                              ; preds = %146
  %151 = load i64, i64* %24, align 8
  %152 = icmp eq i64 %151, 0
  br i1 %152, label %157, label %153

153:                                              ; preds = %150
  %154 = load i64, i64* %24, align 8
  %155 = and i64 %154, 1
  %156 = icmp ne i64 %155, 0
  br i1 %156, label %157, label %160

157:                                              ; preds = %153, %150
  %158 = load i64, i64* %24, align 8
  %159 = add i64 %158, 1
  store i64 %159, i64* %24, align 8
  br label %160

160:                                              ; preds = %157, %153
  br label %161

161:                                              ; preds = %160, %149
  br label %162

162:                                              ; preds = %161, %145
  %163 = load i32, i32* %15, align 4
  %164 = icmp eq i32 %163, 0
  br i1 %164, label %165, label %183

165:                                              ; preds = %162
  %166 = load double, double* %14, align 8
  %167 = load i32, i32* %22, align 4
  %168 = sitofp i32 %167 to double
  %169 = fsub double %166, %168
  store double %169, double* %20, align 8
  %170 = load double, double* %20, align 8
  %171 = fcmp olt double %170, 5.000000e-01
  br i1 %171, label %172, label %175

172:                                              ; preds = %165
  %173 = load double, double* %20, align 8
  %174 = fcmp ogt double %173, 5.000000e-01
  br i1 %174, label %175, label %182

175:                                              ; preds = %172, %165
  %176 = load i32, i32* %22, align 4
  %177 = and i32 %176, 1
  %178 = icmp ne i32 %177, 0
  br i1 %178, label %179, label %182

179:                                              ; preds = %175
  %180 = load i32, i32* %22, align 4
  %181 = add nsw i32 %180, 1
  store i32 %181, i32* %22, align 4
  br label %182

182:                                              ; preds = %179, %175, %172
  br label %225

183:                                              ; preds = %162
  %184 = load i32, i32* %15, align 4
  store i32 %184, i32* %25, align 4
  br label %185

185:                                              ; preds = %202, %183
  %186 = load i64, i64* %19, align 8
  %187 = icmp ult i64 %186, 32
  br i1 %187, label %188, label %203

188:                                              ; preds = %185
  %189 = load i32, i32* %25, align 4
  %190 = add i32 %189, -1
  store i32 %190, i32* %25, align 4
  %191 = load i64, i64* %24, align 8
  %192 = urem i64 %191, 10
  %193 = add i64 48, %192
  %194 = trunc i64 %193 to i8
  %195 = load i64, i64* %19, align 8
  %196 = add i64 %195, 1
  store i64 %196, i64* %19, align 8
  %197 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %195
  store i8 %194, i8* %197, align 1
  %198 = load i64, i64* %24, align 8
  %199 = udiv i64 %198, 10
  store i64 %199, i64* %24, align 8
  %200 = icmp ne i64 %199, 0
  br i1 %200, label %202, label %201

201:                                              ; preds = %188
  br label %203

202:                                              ; preds = %188
  br label %185, !llvm.loop !21

203:                                              ; preds = %201, %185
  br label %204

204:                                              ; preds = %213, %203
  %205 = load i64, i64* %19, align 8
  %206 = icmp ult i64 %205, 32
  br i1 %206, label %207, label %211

207:                                              ; preds = %204
  %208 = load i32, i32* %25, align 4
  %209 = add i32 %208, -1
  store i32 %209, i32* %25, align 4
  %210 = icmp ugt i32 %208, 0
  br label %211

211:                                              ; preds = %207, %204
  %212 = phi i1 [ false, %204 ], [ %210, %207 ]
  br i1 %212, label %213, label %217

213:                                              ; preds = %211
  %214 = load i64, i64* %19, align 8
  %215 = add i64 %214, 1
  store i64 %215, i64* %19, align 8
  %216 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %214
  store i8 48, i8* %216, align 1
  br label %204, !llvm.loop !22

217:                                              ; preds = %211
  %218 = load i64, i64* %19, align 8
  %219 = icmp ult i64 %218, 32
  br i1 %219, label %220, label %224

220:                                              ; preds = %217
  %221 = load i64, i64* %19, align 8
  %222 = add i64 %221, 1
  store i64 %222, i64* %19, align 8
  %223 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %221
  store i8 46, i8* %223, align 1
  br label %224

224:                                              ; preds = %220, %217
  br label %225

225:                                              ; preds = %224, %182
  br label %226

226:                                              ; preds = %241, %225
  %227 = load i64, i64* %19, align 8
  %228 = icmp ult i64 %227, 32
  br i1 %228, label %229, label %242

229:                                              ; preds = %226
  %230 = load i32, i32* %22, align 4
  %231 = srem i32 %230, 10
  %232 = add nsw i32 48, %231
  %233 = trunc i32 %232 to i8
  %234 = load i64, i64* %19, align 8
  %235 = add i64 %234, 1
  store i64 %235, i64* %19, align 8
  %236 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %234
  store i8 %233, i8* %236, align 1
  %237 = load i32, i32* %22, align 4
  %238 = sdiv i32 %237, 10
  store i32 %238, i32* %22, align 4
  %239 = icmp ne i32 %238, 0
  br i1 %239, label %241, label %240

240:                                              ; preds = %229
  br label %242

241:                                              ; preds = %229
  br label %226, !llvm.loop !23

242:                                              ; preds = %240, %226
  %243 = load i32, i32* %17, align 4
  %244 = and i32 %243, 2
  %245 = icmp ne i32 %244, 0
  br i1 %245, label %279, label %246

246:                                              ; preds = %242
  %247 = load i32, i32* %17, align 4
  %248 = and i32 %247, 1
  %249 = icmp ne i32 %248, 0
  br i1 %249, label %250, label %279

250:                                              ; preds = %246
  %251 = load i32, i32* %16, align 4
  %252 = icmp ne i32 %251, 0
  br i1 %252, label %253, label %263

253:                                              ; preds = %250
  %254 = load i8, i8* %21, align 1
  %255 = trunc i8 %254 to i1
  br i1 %255, label %260, label %256

256:                                              ; preds = %253
  %257 = load i32, i32* %17, align 4
  %258 = and i32 %257, 12
  %259 = icmp ne i32 %258, 0
  br i1 %259, label %260, label %263

260:                                              ; preds = %256, %253
  %261 = load i32, i32* %16, align 4
  %262 = add i32 %261, -1
  store i32 %262, i32* %16, align 4
  br label %263

263:                                              ; preds = %260, %256, %250
  br label %264

264:                                              ; preds = %274, %263
  %265 = load i64, i64* %19, align 8
  %266 = load i32, i32* %16, align 4
  %267 = zext i32 %266 to i64
  %268 = icmp ult i64 %265, %267
  br i1 %268, label %269, label %272

269:                                              ; preds = %264
  %270 = load i64, i64* %19, align 8
  %271 = icmp ult i64 %270, 32
  br label %272

272:                                              ; preds = %269, %264
  %273 = phi i1 [ false, %264 ], [ %271, %269 ]
  br i1 %273, label %274, label %278

274:                                              ; preds = %272
  %275 = load i64, i64* %19, align 8
  %276 = add i64 %275, 1
  store i64 %276, i64* %19, align 8
  %277 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %275
  store i8 48, i8* %277, align 1
  br label %264, !llvm.loop !24

278:                                              ; preds = %272
  br label %279

279:                                              ; preds = %278, %246, %242
  %280 = load i64, i64* %19, align 8
  %281 = icmp ult i64 %280, 32
  br i1 %281, label %282, label %308

282:                                              ; preds = %279
  %283 = load i8, i8* %21, align 1
  %284 = trunc i8 %283 to i1
  br i1 %284, label %285, label %289

285:                                              ; preds = %282
  %286 = load i64, i64* %19, align 8
  %287 = add i64 %286, 1
  store i64 %287, i64* %19, align 8
  %288 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %286
  store i8 45, i8* %288, align 1
  br label %307

289:                                              ; preds = %282
  %290 = load i32, i32* %17, align 4
  %291 = and i32 %290, 4
  %292 = icmp ne i32 %291, 0
  br i1 %292, label %293, label %297

293:                                              ; preds = %289
  %294 = load i64, i64* %19, align 8
  %295 = add i64 %294, 1
  store i64 %295, i64* %19, align 8
  %296 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %294
  store i8 43, i8* %296, align 1
  br label %306

297:                                              ; preds = %289
  %298 = load i32, i32* %17, align 4
  %299 = and i32 %298, 8
  %300 = icmp ne i32 %299, 0
  br i1 %300, label %301, label %305

301:                                              ; preds = %297
  %302 = load i64, i64* %19, align 8
  %303 = add i64 %302, 1
  store i64 %303, i64* %19, align 8
  %304 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 %302
  store i8 32, i8* %304, align 1
  br label %305

305:                                              ; preds = %301, %297
  br label %306

306:                                              ; preds = %305, %293
  br label %307

307:                                              ; preds = %306, %285
  br label %308

308:                                              ; preds = %307, %279
  %309 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %310 = load i8*, i8** %11, align 8
  %311 = load i64, i64* %12, align 8
  %312 = load i64, i64* %13, align 8
  %313 = getelementptr inbounds [32 x i8], [32 x i8]* %18, i64 0, i64 0
  %314 = load i64, i64* %19, align 8
  %315 = load i32, i32* %16, align 4
  %316 = load i32, i32* %17, align 4
  %317 = call i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %309, i8* noundef %310, i64 noundef %311, i64 noundef %312, i8* noundef %313, i64 noundef %314, i32 noundef %315, i32 noundef %316)
  store i64 %317, i64* %9, align 8
  br label %318

318:                                              ; preds = %308, %76, %51, %40, %29
  %319 = load i64, i64* %9, align 8
  ret i64 %319
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_etoa(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, double noundef %4, i32 noundef %5, i32 noundef %6, i32 noundef %7) #0 {
  %9 = alloca i64, align 8
  %10 = alloca void (i8, i8*, i64, i64)*, align 8
  %11 = alloca i8*, align 8
  %12 = alloca i64, align 8
  %13 = alloca i64, align 8
  %14 = alloca double, align 8
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i8, align 1
  %19 = alloca %union.anon, align 8
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  %22 = alloca double, align 8
  %23 = alloca double, align 8
  %24 = alloca i32, align 4
  %25 = alloca i32, align 4
  %26 = alloca i64, align 8
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %10, align 8
  store i8* %1, i8** %11, align 8
  store i64 %2, i64* %12, align 8
  store i64 %3, i64* %13, align 8
  store double %4, double* %14, align 8
  store i32 %5, i32* %15, align 4
  store i32 %6, i32* %16, align 4
  store i32 %7, i32* %17, align 4
  %27 = load double, double* %14, align 8
  %28 = load double, double* %14, align 8
  %29 = fcmp une double %27, %28
  br i1 %29, label %36, label %30

30:                                               ; preds = %8
  %31 = load double, double* %14, align 8
  %32 = fcmp ogt double %31, 0x7FEFFFFFFFFFFFFF
  br i1 %32, label %36, label %33

33:                                               ; preds = %30
  %34 = load double, double* %14, align 8
  %35 = fcmp olt double %34, 0xFFEFFFFFFFFFFFFF
  br i1 %35, label %36, label %46

36:                                               ; preds = %33, %30, %8
  %37 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %38 = load i8*, i8** %11, align 8
  %39 = load i64, i64* %12, align 8
  %40 = load i64, i64* %13, align 8
  %41 = load double, double* %14, align 8
  %42 = load i32, i32* %15, align 4
  %43 = load i32, i32* %16, align 4
  %44 = load i32, i32* %17, align 4
  %45 = call i64 @_ftoa(void (i8, i8*, i64, i64)* noundef %37, i8* noundef %38, i64 noundef %39, i64 noundef %40, double noundef %41, i32 noundef %42, i32 noundef %43, i32 noundef %44)
  store i64 %45, i64* %9, align 8
  br label %273

46:                                               ; preds = %33
  %47 = load double, double* %14, align 8
  %48 = fcmp olt double %47, 0.000000e+00
  %49 = zext i1 %48 to i8
  store i8 %49, i8* %18, align 1
  %50 = load i8, i8* %18, align 1
  %51 = trunc i8 %50 to i1
  br i1 %51, label %52, label %55

52:                                               ; preds = %46
  %53 = load double, double* %14, align 8
  %54 = fneg double %53
  store double %54, double* %14, align 8
  br label %55

55:                                               ; preds = %52, %46
  %56 = load i32, i32* %17, align 4
  %57 = and i32 %56, 1024
  %58 = icmp ne i32 %57, 0
  br i1 %58, label %60, label %59

59:                                               ; preds = %55
  store i32 6, i32* %15, align 4
  br label %60

60:                                               ; preds = %59, %55
  %61 = load double, double* %14, align 8
  %62 = bitcast %union.anon* %19 to double*
  store double %61, double* %62, align 8
  %63 = bitcast %union.anon* %19 to i64*
  %64 = load i64, i64* %63, align 8
  %65 = lshr i64 %64, 52
  %66 = and i64 %65, 2047
  %67 = trunc i64 %66 to i32
  %68 = sub nsw i32 %67, 1023
  store i32 %68, i32* %20, align 4
  %69 = bitcast %union.anon* %19 to i64*
  %70 = load i64, i64* %69, align 8
  %71 = and i64 %70, 4503599627370495
  %72 = or i64 %71, 4607182418800017408
  %73 = bitcast %union.anon* %19 to i64*
  store i64 %72, i64* %73, align 8
  %74 = load i32, i32* %20, align 4
  %75 = sitofp i32 %74 to double
  %76 = call double @llvm.fmuladd.f64(double %75, double 0x3FD34413509F79FB, double 0x3FC68A288B60C8B3)
  %77 = bitcast %union.anon* %19 to double*
  %78 = load double, double* %77, align 8
  %79 = fsub double %78, 1.500000e+00
  %80 = call double @llvm.fmuladd.f64(double %79, double 0x3FD287A7636F4361, double %76)
  %81 = fptosi double %80 to i32
  store i32 %81, i32* %21, align 4
  %82 = load i32, i32* %21, align 4
  %83 = sitofp i32 %82 to double
  %84 = call double @llvm.fmuladd.f64(double %83, double 0x400A934F0979A371, double 5.000000e-01)
  %85 = fptosi double %84 to i32
  store i32 %85, i32* %20, align 4
  %86 = load i32, i32* %21, align 4
  %87 = sitofp i32 %86 to double
  %88 = load i32, i32* %20, align 4
  %89 = sitofp i32 %88 to double
  %90 = fmul double %89, 0x3FE62E42FEFA39EF
  %91 = fneg double %90
  %92 = call double @llvm.fmuladd.f64(double %87, double 0x40026BB1BBB55516, double %91)
  store double %92, double* %22, align 8
  %93 = load double, double* %22, align 8
  %94 = load double, double* %22, align 8
  %95 = fmul double %93, %94
  store double %95, double* %23, align 8
  %96 = load i32, i32* %20, align 4
  %97 = add nsw i32 %96, 1023
  %98 = sext i32 %97 to i64
  %99 = shl i64 %98, 52
  %100 = bitcast %union.anon* %19 to i64*
  store i64 %99, i64* %100, align 8
  %101 = load double, double* %22, align 8
  %102 = fmul double 2.000000e+00, %101
  %103 = load double, double* %22, align 8
  %104 = fsub double 2.000000e+00, %103
  %105 = load double, double* %23, align 8
  %106 = load double, double* %23, align 8
  %107 = load double, double* %23, align 8
  %108 = fdiv double %107, 1.400000e+01
  %109 = fadd double 1.000000e+01, %108
  %110 = fdiv double %106, %109
  %111 = fadd double 6.000000e+00, %110
  %112 = fdiv double %105, %111
  %113 = fadd double %104, %112
  %114 = fdiv double %102, %113
  %115 = fadd double 1.000000e+00, %114
  %116 = bitcast %union.anon* %19 to double*
  %117 = load double, double* %116, align 8
  %118 = fmul double %117, %115
  store double %118, double* %116, align 8
  %119 = load double, double* %14, align 8
  %120 = bitcast %union.anon* %19 to double*
  %121 = load double, double* %120, align 8
  %122 = fcmp olt double %119, %121
  br i1 %122, label %123, label %129

123:                                              ; preds = %60
  %124 = load i32, i32* %21, align 4
  %125 = add nsw i32 %124, -1
  store i32 %125, i32* %21, align 4
  %126 = bitcast %union.anon* %19 to double*
  %127 = load double, double* %126, align 8
  %128 = fdiv double %127, 1.000000e+01
  store double %128, double* %126, align 8
  br label %129

129:                                              ; preds = %123, %60
  %130 = load i32, i32* %21, align 4
  %131 = icmp slt i32 %130, 100
  br i1 %131, label %132, label %135

132:                                              ; preds = %129
  %133 = load i32, i32* %21, align 4
  %134 = icmp sgt i32 %133, -100
  br label %135

135:                                              ; preds = %132, %129
  %136 = phi i1 [ false, %129 ], [ %134, %132 ]
  %137 = zext i1 %136 to i64
  %138 = select i1 %136, i32 4, i32 5
  store i32 %138, i32* %24, align 4
  %139 = load i32, i32* %17, align 4
  %140 = and i32 %139, 2048
  %141 = icmp ne i32 %140, 0
  br i1 %141, label %142, label %173

142:                                              ; preds = %135
  %143 = load double, double* %14, align 8
  %144 = fcmp oge double %143, 1.000000e-04
  br i1 %144, label %145, label %161

145:                                              ; preds = %142
  %146 = load double, double* %14, align 8
  %147 = fcmp olt double %146, 1.000000e+06
  br i1 %147, label %148, label %161

148:                                              ; preds = %145
  %149 = load i32, i32* %15, align 4
  %150 = load i32, i32* %21, align 4
  %151 = icmp sgt i32 %149, %150
  br i1 %151, label %152, label %157

152:                                              ; preds = %148
  %153 = load i32, i32* %15, align 4
  %154 = load i32, i32* %21, align 4
  %155 = sub nsw i32 %153, %154
  %156 = sub nsw i32 %155, 1
  store i32 %156, i32* %15, align 4
  br label %158

157:                                              ; preds = %148
  store i32 0, i32* %15, align 4
  br label %158

158:                                              ; preds = %157, %152
  %159 = load i32, i32* %17, align 4
  %160 = or i32 %159, 1024
  store i32 %160, i32* %17, align 4
  store i32 0, i32* %24, align 4
  store i32 0, i32* %21, align 4
  br label %172

161:                                              ; preds = %145, %142
  %162 = load i32, i32* %15, align 4
  %163 = icmp ugt i32 %162, 0
  br i1 %163, label %164, label %171

164:                                              ; preds = %161
  %165 = load i32, i32* %17, align 4
  %166 = and i32 %165, 1024
  %167 = icmp ne i32 %166, 0
  br i1 %167, label %168, label %171

168:                                              ; preds = %164
  %169 = load i32, i32* %15, align 4
  %170 = add i32 %169, -1
  store i32 %170, i32* %15, align 4
  br label %171

171:                                              ; preds = %168, %164, %161
  br label %172

172:                                              ; preds = %171, %158
  br label %173

173:                                              ; preds = %172, %135
  %174 = load i32, i32* %16, align 4
  store i32 %174, i32* %25, align 4
  %175 = load i32, i32* %16, align 4
  %176 = load i32, i32* %24, align 4
  %177 = icmp ugt i32 %175, %176
  br i1 %177, label %178, label %182

178:                                              ; preds = %173
  %179 = load i32, i32* %24, align 4
  %180 = load i32, i32* %25, align 4
  %181 = sub i32 %180, %179
  store i32 %181, i32* %25, align 4
  br label %183

182:                                              ; preds = %173
  store i32 0, i32* %25, align 4
  br label %183

183:                                              ; preds = %182, %178
  %184 = load i32, i32* %17, align 4
  %185 = and i32 %184, 2
  %186 = icmp ne i32 %185, 0
  br i1 %186, label %187, label %191

187:                                              ; preds = %183
  %188 = load i32, i32* %24, align 4
  %189 = icmp ne i32 %188, 0
  br i1 %189, label %190, label %191

190:                                              ; preds = %187
  store i32 0, i32* %25, align 4
  br label %191

191:                                              ; preds = %190, %187, %183
  %192 = load i32, i32* %21, align 4
  %193 = icmp ne i32 %192, 0
  br i1 %193, label %194, label %199

194:                                              ; preds = %191
  %195 = bitcast %union.anon* %19 to double*
  %196 = load double, double* %195, align 8
  %197 = load double, double* %14, align 8
  %198 = fdiv double %197, %196
  store double %198, double* %14, align 8
  br label %199

199:                                              ; preds = %194, %191
  %200 = load i64, i64* %12, align 8
  store i64 %200, i64* %26, align 8
  %201 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %202 = load i8*, i8** %11, align 8
  %203 = load i64, i64* %12, align 8
  %204 = load i64, i64* %13, align 8
  %205 = load i8, i8* %18, align 1
  %206 = trunc i8 %205 to i1
  br i1 %206, label %207, label %210

207:                                              ; preds = %199
  %208 = load double, double* %14, align 8
  %209 = fneg double %208
  br label %212

210:                                              ; preds = %199
  %211 = load double, double* %14, align 8
  br label %212

212:                                              ; preds = %210, %207
  %213 = phi double [ %209, %207 ], [ %211, %210 ]
  %214 = load i32, i32* %15, align 4
  %215 = load i32, i32* %25, align 4
  %216 = load i32, i32* %17, align 4
  %217 = and i32 %216, -2049
  %218 = call i64 @_ftoa(void (i8, i8*, i64, i64)* noundef %201, i8* noundef %202, i64 noundef %203, i64 noundef %204, double noundef %213, i32 noundef %214, i32 noundef %215, i32 noundef %217)
  store i64 %218, i64* %12, align 8
  %219 = load i32, i32* %24, align 4
  %220 = icmp ne i32 %219, 0
  br i1 %220, label %221, label %271

221:                                              ; preds = %212
  %222 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %223 = load i32, i32* %17, align 4
  %224 = and i32 %223, 32
  %225 = icmp ne i32 %224, 0
  %226 = zext i1 %225 to i64
  %227 = select i1 %225, i32 69, i32 101
  %228 = trunc i32 %227 to i8
  %229 = load i8*, i8** %11, align 8
  %230 = load i64, i64* %12, align 8
  %231 = add i64 %230, 1
  store i64 %231, i64* %12, align 8
  %232 = load i64, i64* %13, align 8
  call void %222(i8 noundef signext %228, i8* noundef %229, i64 noundef %230, i64 noundef %232)
  %233 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %234 = load i8*, i8** %11, align 8
  %235 = load i64, i64* %12, align 8
  %236 = load i64, i64* %13, align 8
  %237 = load i32, i32* %21, align 4
  %238 = icmp slt i32 %237, 0
  br i1 %238, label %239, label %242

239:                                              ; preds = %221
  %240 = load i32, i32* %21, align 4
  %241 = sub nsw i32 0, %240
  br label %244

242:                                              ; preds = %221
  %243 = load i32, i32* %21, align 4
  br label %244

244:                                              ; preds = %242, %239
  %245 = phi i32 [ %241, %239 ], [ %243, %242 ]
  %246 = sext i32 %245 to i64
  %247 = load i32, i32* %21, align 4
  %248 = icmp slt i32 %247, 0
  %249 = load i32, i32* %24, align 4
  %250 = sub i32 %249, 1
  %251 = call i64 @_ntoa_long(void (i8, i8*, i64, i64)* noundef %233, i8* noundef %234, i64 noundef %235, i64 noundef %236, i64 noundef %246, i1 noundef zeroext %248, i64 noundef 10, i32 noundef 0, i32 noundef %250, i32 noundef 5)
  store i64 %251, i64* %12, align 8
  %252 = load i32, i32* %17, align 4
  %253 = and i32 %252, 2
  %254 = icmp ne i32 %253, 0
  br i1 %254, label %255, label %270

255:                                              ; preds = %244
  br label %256

256:                                              ; preds = %263, %255
  %257 = load i64, i64* %12, align 8
  %258 = load i64, i64* %26, align 8
  %259 = sub i64 %257, %258
  %260 = load i32, i32* %16, align 4
  %261 = zext i32 %260 to i64
  %262 = icmp ult i64 %259, %261
  br i1 %262, label %263, label %269

263:                                              ; preds = %256
  %264 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %10, align 8
  %265 = load i8*, i8** %11, align 8
  %266 = load i64, i64* %12, align 8
  %267 = add i64 %266, 1
  store i64 %267, i64* %12, align 8
  %268 = load i64, i64* %13, align 8
  call void %264(i8 noundef signext 32, i8* noundef %265, i64 noundef %266, i64 noundef %268)
  br label %256, !llvm.loop !25

269:                                              ; preds = %256
  br label %270

270:                                              ; preds = %269, %244
  br label %271

271:                                              ; preds = %270, %212
  %272 = load i64, i64* %12, align 8
  store i64 %272, i64* %9, align 8
  br label %273

273:                                              ; preds = %271, %36
  %274 = load i64, i64* %9, align 8
  ret i64 %274
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i32 @_strnlen_s(i8* noundef %0, i64 noundef %1) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i64, align 8
  %5 = alloca i8*, align 8
  store i8* %0, i8** %3, align 8
  store i64 %1, i64* %4, align 8
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
  %13 = load i64, i64* %4, align 8
  %14 = add i64 %13, -1
  store i64 %14, i64* %4, align 8
  %15 = icmp ne i64 %13, 0
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
  br label %7, !llvm.loop !26

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
define internal i64 @_ntoa_format(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, i8* noundef %4, i64 noundef %5, i1 noundef zeroext %6, i32 noundef %7, i32 noundef %8, i32 noundef %9, i32 noundef %10) #0 {
  %12 = alloca void (i8, i8*, i64, i64)*, align 8
  %13 = alloca i8*, align 8
  %14 = alloca i64, align 8
  %15 = alloca i64, align 8
  %16 = alloca i8*, align 8
  %17 = alloca i64, align 8
  %18 = alloca i8, align 1
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  %22 = alloca i32, align 4
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %12, align 8
  store i8* %1, i8** %13, align 8
  store i64 %2, i64* %14, align 8
  store i64 %3, i64* %15, align 8
  store i8* %4, i8** %16, align 8
  store i64 %5, i64* %17, align 8
  %23 = zext i1 %6 to i8
  store i8 %23, i8* %18, align 1
  store i32 %7, i32* %19, align 4
  store i32 %8, i32* %20, align 4
  store i32 %9, i32* %21, align 4
  store i32 %10, i32* %22, align 4
  %24 = load i32, i32* %22, align 4
  %25 = and i32 %24, 2
  %26 = icmp ne i32 %25, 0
  br i1 %26, label %81, label %27

27:                                               ; preds = %11
  %28 = load i32, i32* %21, align 4
  %29 = icmp ne i32 %28, 0
  br i1 %29, label %30, label %44

30:                                               ; preds = %27
  %31 = load i32, i32* %22, align 4
  %32 = and i32 %31, 1
  %33 = icmp ne i32 %32, 0
  br i1 %33, label %34, label %44

34:                                               ; preds = %30
  %35 = load i8, i8* %18, align 1
  %36 = trunc i8 %35 to i1
  br i1 %36, label %41, label %37

37:                                               ; preds = %34
  %38 = load i32, i32* %22, align 4
  %39 = and i32 %38, 12
  %40 = icmp ne i32 %39, 0
  br i1 %40, label %41, label %44

41:                                               ; preds = %37, %34
  %42 = load i32, i32* %21, align 4
  %43 = add i32 %42, -1
  store i32 %43, i32* %21, align 4
  br label %44

44:                                               ; preds = %41, %37, %30, %27
  br label %45

45:                                               ; preds = %55, %44
  %46 = load i64, i64* %17, align 8
  %47 = load i32, i32* %20, align 4
  %48 = zext i32 %47 to i64
  %49 = icmp ult i64 %46, %48
  br i1 %49, label %50, label %53

50:                                               ; preds = %45
  %51 = load i64, i64* %17, align 8
  %52 = icmp ult i64 %51, 32
  br label %53

53:                                               ; preds = %50, %45
  %54 = phi i1 [ false, %45 ], [ %52, %50 ]
  br i1 %54, label %55, label %60

55:                                               ; preds = %53
  %56 = load i8*, i8** %16, align 8
  %57 = load i64, i64* %17, align 8
  %58 = add i64 %57, 1
  store i64 %58, i64* %17, align 8
  %59 = getelementptr inbounds i8, i8* %56, i64 %57
  store i8 48, i8* %59, align 1
  br label %45, !llvm.loop !27

60:                                               ; preds = %53
  br label %61

61:                                               ; preds = %75, %60
  %62 = load i32, i32* %22, align 4
  %63 = and i32 %62, 1
  %64 = icmp ne i32 %63, 0
  br i1 %64, label %65, label %73

65:                                               ; preds = %61
  %66 = load i64, i64* %17, align 8
  %67 = load i32, i32* %21, align 4
  %68 = zext i32 %67 to i64
  %69 = icmp ult i64 %66, %68
  br i1 %69, label %70, label %73

70:                                               ; preds = %65
  %71 = load i64, i64* %17, align 8
  %72 = icmp ult i64 %71, 32
  br label %73

73:                                               ; preds = %70, %65, %61
  %74 = phi i1 [ false, %65 ], [ false, %61 ], [ %72, %70 ]
  br i1 %74, label %75, label %80

75:                                               ; preds = %73
  %76 = load i8*, i8** %16, align 8
  %77 = load i64, i64* %17, align 8
  %78 = add i64 %77, 1
  store i64 %78, i64* %17, align 8
  %79 = getelementptr inbounds i8, i8* %76, i64 %77
  store i8 48, i8* %79, align 1
  br label %61, !llvm.loop !28

80:                                               ; preds = %73
  br label %81

81:                                               ; preds = %80, %11
  %82 = load i32, i32* %22, align 4
  %83 = and i32 %82, 16
  %84 = icmp ne i32 %83, 0
  br i1 %84, label %85, label %166

85:                                               ; preds = %81
  %86 = load i32, i32* %22, align 4
  %87 = and i32 %86, 1024
  %88 = icmp ne i32 %87, 0
  br i1 %88, label %114, label %89

89:                                               ; preds = %85
  %90 = load i64, i64* %17, align 8
  %91 = icmp ne i64 %90, 0
  br i1 %91, label %92, label %114

92:                                               ; preds = %89
  %93 = load i64, i64* %17, align 8
  %94 = load i32, i32* %20, align 4
  %95 = zext i32 %94 to i64
  %96 = icmp eq i64 %93, %95
  br i1 %96, label %102, label %97

97:                                               ; preds = %92
  %98 = load i64, i64* %17, align 8
  %99 = load i32, i32* %21, align 4
  %100 = zext i32 %99 to i64
  %101 = icmp eq i64 %98, %100
  br i1 %101, label %102, label %114

102:                                              ; preds = %97, %92
  %103 = load i64, i64* %17, align 8
  %104 = add i64 %103, -1
  store i64 %104, i64* %17, align 8
  %105 = load i64, i64* %17, align 8
  %106 = icmp ne i64 %105, 0
  br i1 %106, label %107, label %113

107:                                              ; preds = %102
  %108 = load i32, i32* %19, align 4
  %109 = icmp eq i32 %108, 16
  br i1 %109, label %110, label %113

110:                                              ; preds = %107
  %111 = load i64, i64* %17, align 8
  %112 = add i64 %111, -1
  store i64 %112, i64* %17, align 8
  br label %113

113:                                              ; preds = %110, %107, %102
  br label %114

114:                                              ; preds = %113, %97, %89, %85
  %115 = load i32, i32* %19, align 4
  %116 = icmp eq i32 %115, 16
  br i1 %116, label %117, label %129

117:                                              ; preds = %114
  %118 = load i32, i32* %22, align 4
  %119 = and i32 %118, 32
  %120 = icmp ne i32 %119, 0
  br i1 %120, label %129, label %121

121:                                              ; preds = %117
  %122 = load i64, i64* %17, align 8
  %123 = icmp ult i64 %122, 32
  br i1 %123, label %124, label %129

124:                                              ; preds = %121
  %125 = load i8*, i8** %16, align 8
  %126 = load i64, i64* %17, align 8
  %127 = add i64 %126, 1
  store i64 %127, i64* %17, align 8
  %128 = getelementptr inbounds i8, i8* %125, i64 %126
  store i8 120, i8* %128, align 1
  br label %157

129:                                              ; preds = %121, %117, %114
  %130 = load i32, i32* %19, align 4
  %131 = icmp eq i32 %130, 16
  br i1 %131, label %132, label %144

132:                                              ; preds = %129
  %133 = load i32, i32* %22, align 4
  %134 = and i32 %133, 32
  %135 = icmp ne i32 %134, 0
  br i1 %135, label %136, label %144

136:                                              ; preds = %132
  %137 = load i64, i64* %17, align 8
  %138 = icmp ult i64 %137, 32
  br i1 %138, label %139, label %144

139:                                              ; preds = %136
  %140 = load i8*, i8** %16, align 8
  %141 = load i64, i64* %17, align 8
  %142 = add i64 %141, 1
  store i64 %142, i64* %17, align 8
  %143 = getelementptr inbounds i8, i8* %140, i64 %141
  store i8 88, i8* %143, align 1
  br label %156

144:                                              ; preds = %136, %132, %129
  %145 = load i32, i32* %19, align 4
  %146 = icmp eq i32 %145, 2
  br i1 %146, label %147, label %155

147:                                              ; preds = %144
  %148 = load i64, i64* %17, align 8
  %149 = icmp ult i64 %148, 32
  br i1 %149, label %150, label %155

150:                                              ; preds = %147
  %151 = load i8*, i8** %16, align 8
  %152 = load i64, i64* %17, align 8
  %153 = add i64 %152, 1
  store i64 %153, i64* %17, align 8
  %154 = getelementptr inbounds i8, i8* %151, i64 %152
  store i8 98, i8* %154, align 1
  br label %155

155:                                              ; preds = %150, %147, %144
  br label %156

156:                                              ; preds = %155, %139
  br label %157

157:                                              ; preds = %156, %124
  %158 = load i64, i64* %17, align 8
  %159 = icmp ult i64 %158, 32
  br i1 %159, label %160, label %165

160:                                              ; preds = %157
  %161 = load i8*, i8** %16, align 8
  %162 = load i64, i64* %17, align 8
  %163 = add i64 %162, 1
  store i64 %163, i64* %17, align 8
  %164 = getelementptr inbounds i8, i8* %161, i64 %162
  store i8 48, i8* %164, align 1
  br label %165

165:                                              ; preds = %160, %157
  br label %166

166:                                              ; preds = %165, %81
  %167 = load i64, i64* %17, align 8
  %168 = icmp ult i64 %167, 32
  br i1 %168, label %169, label %198

169:                                              ; preds = %166
  %170 = load i8, i8* %18, align 1
  %171 = trunc i8 %170 to i1
  br i1 %171, label %172, label %177

172:                                              ; preds = %169
  %173 = load i8*, i8** %16, align 8
  %174 = load i64, i64* %17, align 8
  %175 = add i64 %174, 1
  store i64 %175, i64* %17, align 8
  %176 = getelementptr inbounds i8, i8* %173, i64 %174
  store i8 45, i8* %176, align 1
  br label %197

177:                                              ; preds = %169
  %178 = load i32, i32* %22, align 4
  %179 = and i32 %178, 4
  %180 = icmp ne i32 %179, 0
  br i1 %180, label %181, label %186

181:                                              ; preds = %177
  %182 = load i8*, i8** %16, align 8
  %183 = load i64, i64* %17, align 8
  %184 = add i64 %183, 1
  store i64 %184, i64* %17, align 8
  %185 = getelementptr inbounds i8, i8* %182, i64 %183
  store i8 43, i8* %185, align 1
  br label %196

186:                                              ; preds = %177
  %187 = load i32, i32* %22, align 4
  %188 = and i32 %187, 8
  %189 = icmp ne i32 %188, 0
  br i1 %189, label %190, label %195

190:                                              ; preds = %186
  %191 = load i8*, i8** %16, align 8
  %192 = load i64, i64* %17, align 8
  %193 = add i64 %192, 1
  store i64 %193, i64* %17, align 8
  %194 = getelementptr inbounds i8, i8* %191, i64 %192
  store i8 32, i8* %194, align 1
  br label %195

195:                                              ; preds = %190, %186
  br label %196

196:                                              ; preds = %195, %181
  br label %197

197:                                              ; preds = %196, %172
  br label %198

198:                                              ; preds = %197, %166
  %199 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %12, align 8
  %200 = load i8*, i8** %13, align 8
  %201 = load i64, i64* %14, align 8
  %202 = load i64, i64* %15, align 8
  %203 = load i8*, i8** %16, align 8
  %204 = load i64, i64* %17, align 8
  %205 = load i32, i32* %21, align 4
  %206 = load i32, i32* %22, align 4
  %207 = call i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %199, i8* noundef %200, i64 noundef %201, i64 noundef %202, i8* noundef %203, i64 noundef %204, i32 noundef %205, i32 noundef %206)
  ret i64 %207
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define internal i64 @_out_rev(void (i8, i8*, i64, i64)* noundef %0, i8* noundef %1, i64 noundef %2, i64 noundef %3, i8* noundef %4, i64 noundef %5, i32 noundef %6, i32 noundef %7) #0 {
  %9 = alloca void (i8, i8*, i64, i64)*, align 8
  %10 = alloca i8*, align 8
  %11 = alloca i64, align 8
  %12 = alloca i64, align 8
  %13 = alloca i8*, align 8
  %14 = alloca i64, align 8
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i64, align 8
  %18 = alloca i64, align 8
  store void (i8, i8*, i64, i64)* %0, void (i8, i8*, i64, i64)** %9, align 8
  store i8* %1, i8** %10, align 8
  store i64 %2, i64* %11, align 8
  store i64 %3, i64* %12, align 8
  store i8* %4, i8** %13, align 8
  store i64 %5, i64* %14, align 8
  store i32 %6, i32* %15, align 4
  store i32 %7, i32* %16, align 4
  %19 = load i64, i64* %11, align 8
  store i64 %19, i64* %17, align 8
  %20 = load i32, i32* %16, align 4
  %21 = and i32 %20, 2
  %22 = icmp ne i32 %21, 0
  br i1 %22, label %44, label %23

23:                                               ; preds = %8
  %24 = load i32, i32* %16, align 4
  %25 = and i32 %24, 1
  %26 = icmp ne i32 %25, 0
  br i1 %26, label %44, label %27

27:                                               ; preds = %23
  %28 = load i64, i64* %14, align 8
  store i64 %28, i64* %18, align 8
  br label %29

29:                                               ; preds = %40, %27
  %30 = load i64, i64* %18, align 8
  %31 = load i32, i32* %15, align 4
  %32 = zext i32 %31 to i64
  %33 = icmp ult i64 %30, %32
  br i1 %33, label %34, label %43

34:                                               ; preds = %29
  %35 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %9, align 8
  %36 = load i8*, i8** %10, align 8
  %37 = load i64, i64* %11, align 8
  %38 = add i64 %37, 1
  store i64 %38, i64* %11, align 8
  %39 = load i64, i64* %12, align 8
  call void %35(i8 noundef signext 32, i8* noundef %36, i64 noundef %37, i64 noundef %39)
  br label %40

40:                                               ; preds = %34
  %41 = load i64, i64* %18, align 8
  %42 = add i64 %41, 1
  store i64 %42, i64* %18, align 8
  br label %29, !llvm.loop !29

43:                                               ; preds = %29
  br label %44

44:                                               ; preds = %43, %23, %8
  br label %45

45:                                               ; preds = %48, %44
  %46 = load i64, i64* %14, align 8
  %47 = icmp ne i64 %46, 0
  br i1 %47, label %48, label %59

48:                                               ; preds = %45
  %49 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %9, align 8
  %50 = load i8*, i8** %13, align 8
  %51 = load i64, i64* %14, align 8
  %52 = add i64 %51, -1
  store i64 %52, i64* %14, align 8
  %53 = getelementptr inbounds i8, i8* %50, i64 %52
  %54 = load i8, i8* %53, align 1
  %55 = load i8*, i8** %10, align 8
  %56 = load i64, i64* %11, align 8
  %57 = add i64 %56, 1
  store i64 %57, i64* %11, align 8
  %58 = load i64, i64* %12, align 8
  call void %49(i8 noundef signext %54, i8* noundef %55, i64 noundef %56, i64 noundef %58)
  br label %45, !llvm.loop !30

59:                                               ; preds = %45
  %60 = load i32, i32* %16, align 4
  %61 = and i32 %60, 2
  %62 = icmp ne i32 %61, 0
  br i1 %62, label %63, label %78

63:                                               ; preds = %59
  br label %64

64:                                               ; preds = %71, %63
  %65 = load i64, i64* %11, align 8
  %66 = load i64, i64* %17, align 8
  %67 = sub i64 %65, %66
  %68 = load i32, i32* %15, align 4
  %69 = zext i32 %68 to i64
  %70 = icmp ult i64 %67, %69
  br i1 %70, label %71, label %77

71:                                               ; preds = %64
  %72 = load void (i8, i8*, i64, i64)*, void (i8, i8*, i64, i64)** %9, align 8
  %73 = load i8*, i8** %10, align 8
  %74 = load i64, i64* %11, align 8
  %75 = add i64 %74, 1
  store i64 %75, i64* %11, align 8
  %76 = load i64, i64* %12, align 8
  call void %72(i8 noundef signext 32, i8* noundef %73, i64 noundef %74, i64 noundef %76)
  br label %64, !llvm.loop !31

77:                                               ; preds = %64
  br label %78

78:                                               ; preds = %77, %59
  %79 = load i64, i64* %11, align 8
  ret i64 %79
}

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
