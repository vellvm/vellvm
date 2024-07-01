; ModuleID = 'your_project_printf.cc'
source_filename = "your_project_printf.cc"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx14.0.0"

%struct.npf_format_spec = type { i8, i8, i32, i32, i8, i8, i32, i32, i32, i32, i8 }
%struct.npf_cnt_putc_ctx = type { void (i32, i8*)*, i8*, i32 }
%union.anon = type { i64, [16 x i8] }
%struct.npf_bufputc_ctx = type { i8*, i64, i64 }

@.str = private unnamed_addr constant [4 x i8] c"NAN\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"FNI\00", align 1
@.str.2 = private unnamed_addr constant [4 x i8] c"RRE\00", align 1

; Function Attrs: mustprogress noinline optnone ssp uwtable
define i32 @npf_vpprintf(void (i32, i8*)* noundef %0, i8* noundef %1, i8* noundef %2, i8* noundef %3) #0 {
  %5 = alloca void (i32, i8*)*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i8*, align 8
  %9 = alloca %struct.npf_format_spec, align 4
  %10 = alloca i8*, align 8
  %11 = alloca %struct.npf_cnt_putc_ctx, align 8
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca %union.anon, align 8
  %16 = alloca i8*, align 8
  %17 = alloca i8, align 1
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i8, align 1
  %22 = alloca i32, align 4
  %23 = alloca i32, align 4
  %24 = alloca i32, align 4
  %25 = alloca i8*, align 8
  %26 = alloca i8*, align 8
  %27 = alloca i64, align 8
  %28 = alloca i32, align 4
  %29 = alloca i32, align 4
  %30 = alloca i32, align 4
  %31 = alloca i32, align 4
  %32 = alloca i64, align 8
  %33 = alloca i64, align 8
  %34 = alloca i64, align 8
  %35 = alloca i64, align 8
  %36 = alloca i64, align 8
  %37 = alloca i64, align 8
  %38 = alloca i64, align 8
  %39 = alloca i32, align 4
  %40 = alloca i32, align 4
  %41 = alloca i32, align 4
  %42 = alloca i32, align 4
  %43 = alloca i64, align 8
  %44 = alloca i64, align 8
  %45 = alloca i64, align 8
  %46 = alloca i64, align 8
  %47 = alloca i64, align 8
  %48 = alloca i8, align 1
  %49 = alloca i8*, align 8
  %50 = alloca double, align 8
  %51 = alloca double, align 8
  %52 = alloca double, align 8
  %53 = alloca i32, align 4
  store void (i32, i8*)* %0, void (i32, i8*)** %5, align 8
  store i8* %1, i8** %6, align 8
  store i8* %2, i8** %7, align 8
  store i8* %3, i8** %8, align 8
  %54 = load i8*, i8** %7, align 8
  store i8* %54, i8** %10, align 8
  %55 = load void (i32, i8*)*, void (i32, i8*)** %5, align 8
  %56 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %11, i32 0, i32 0
  store void (i32, i8*)* %55, void (i32, i8*)** %56, align 8
  %57 = load i8*, i8** %6, align 8
  %58 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %11, i32 0, i32 1
  store i8* %57, i8** %58, align 8
  %59 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %11, i32 0, i32 2
  store i32 0, i32* %59, align 8
  br label %60

60:                                               ; preds = %650, %84, %4
  %61 = load i8*, i8** %10, align 8
  %62 = load i8, i8* %61, align 1
  %63 = icmp ne i8 %62, 0
  br i1 %63, label %64, label %651

64:                                               ; preds = %60
  %65 = load i8*, i8** %10, align 8
  %66 = load i8, i8* %65, align 1
  %67 = sext i8 %66 to i32
  %68 = icmp ne i32 %67, 37
  br i1 %68, label %69, label %70

69:                                               ; preds = %64
  br label %73

70:                                               ; preds = %64
  %71 = load i8*, i8** %10, align 8
  %72 = call noundef i32 @_ZL21npf_parse_format_specPKcP15npf_format_spec(i8* noundef %71, %struct.npf_format_spec* noundef %9)
  br label %73

73:                                               ; preds = %70, %69
  %74 = phi i32 [ 0, %69 ], [ %72, %70 ]
  store i32 %74, i32* %12, align 4
  %75 = load i32, i32* %12, align 4
  %76 = icmp ne i32 %75, 0
  br i1 %76, label %85, label %77

77:                                               ; preds = %73
  br label %78

78:                                               ; preds = %77
  %79 = load i8*, i8** %10, align 8
  %80 = getelementptr inbounds i8, i8* %79, i32 1
  store i8* %80, i8** %10, align 8
  %81 = load i8, i8* %79, align 1
  %82 = sext i8 %81 to i32
  %83 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %82, i8* noundef %83)
  br label %84

84:                                               ; preds = %78
  br label %60, !llvm.loop !9

85:                                               ; preds = %73
  %86 = load i32, i32* %12, align 4
  %87 = load i8*, i8** %10, align 8
  %88 = sext i32 %86 to i64
  %89 = getelementptr inbounds i8, i8* %87, i64 %88
  store i8* %89, i8** %10, align 8
  %90 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 2
  %91 = load i32, i32* %90, align 4
  %92 = icmp eq i32 %91, 2
  br i1 %92, label %93, label %108

93:                                               ; preds = %85
  %94 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 2
  store i32 1, i32* %94, align 4
  %95 = va_arg i8** %8, i32
  store i32 %95, i32* %13, align 4
  %96 = load i32, i32* %13, align 4
  %97 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 3
  store i32 %96, i32* %97, align 4
  %98 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 3
  %99 = load i32, i32* %98, align 4
  %100 = icmp slt i32 %99, 0
  br i1 %100, label %101, label %107

101:                                              ; preds = %93
  %102 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 3
  %103 = load i32, i32* %102, align 4
  %104 = sub nsw i32 0, %103
  %105 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 3
  store i32 %104, i32* %105, align 4
  %106 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 4
  store i8 1, i8* %106, align 4
  br label %107

107:                                              ; preds = %101, %93
  br label %108

108:                                              ; preds = %107, %85
  %109 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  %110 = load i32, i32* %109, align 4
  %111 = icmp eq i32 %110, 2
  br i1 %111, label %112, label %123

112:                                              ; preds = %108
  %113 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  store i32 0, i32* %113, align 4
  %114 = va_arg i8** %8, i32
  store i32 %114, i32* %14, align 4
  %115 = load i32, i32* %14, align 4
  %116 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  store i32 %115, i32* %116, align 4
  %117 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %118 = load i32, i32* %117, align 4
  %119 = icmp sge i32 %118, 0
  br i1 %119, label %120, label %122

120:                                              ; preds = %112
  %121 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  store i32 1, i32* %121, align 4
  br label %122

122:                                              ; preds = %120, %112
  br label %123

123:                                              ; preds = %122, %108
  %124 = bitcast %union.anon* %15 to [23 x i8]*
  %125 = getelementptr inbounds [23 x i8], [23 x i8]* %124, i64 0, i64 0
  store i8* %125, i8** %16, align 8
  store i8 0, i8* %17, align 1
  store i32 0, i32* %18, align 4
  store i32 0, i32* %19, align 4
  store i32 0, i32* %20, align 4
  store i8 0, i8* %21, align 1
  store i32 0, i32* %22, align 4
  store i32 0, i32* %23, align 4
  %126 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %127 = load i32, i32* %126, align 4
  switch i32 %127, label %406 [
    i32 0, label %128
    i32 1, label %130
    i32 2, label %135
    i32 3, label %161
    i32 4, label %236
    i32 5, label %236
    i32 6, label %236
    i32 7, label %236
    i32 8, label %375
    i32 9, label %381
    i32 10, label %381
    i32 11, label %381
    i32 12, label %381
  ]

128:                                              ; preds = %123
  %129 = load i8*, i8** %16, align 8
  store i8 37, i8* %129, align 1
  store i32 1, i32* %18, align 4
  br label %407

130:                                              ; preds = %123
  %131 = va_arg i8** %8, i32
  store i32 %131, i32* %24, align 4
  %132 = load i32, i32* %24, align 4
  %133 = trunc i32 %132 to i8
  %134 = load i8*, i8** %16, align 8
  store i8 %133, i8* %134, align 1
  store i32 1, i32* %18, align 4
  br label %407

135:                                              ; preds = %123
  %136 = va_arg i8** %8, i8*
  store i8* %136, i8** %25, align 8
  %137 = load i8*, i8** %25, align 8
  store i8* %137, i8** %16, align 8
  %138 = load i8*, i8** %16, align 8
  store i8* %138, i8** %26, align 8
  br label %139

139:                                              ; preds = %155, %135
  %140 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  %141 = load i32, i32* %140, align 4
  %142 = icmp eq i32 %141, 0
  br i1 %142, label %148, label %143

143:                                              ; preds = %139
  %144 = load i32, i32* %18, align 4
  %145 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %146 = load i32, i32* %145, align 4
  %147 = icmp slt i32 %144, %146
  br i1 %147, label %148, label %152

148:                                              ; preds = %143, %139
  %149 = load i8*, i8** %26, align 8
  %150 = load i8, i8* %149, align 1
  %151 = icmp ne i8 %150, 0
  br label %152

152:                                              ; preds = %148, %143
  %153 = phi i1 [ false, %143 ], [ %151, %148 ]
  br i1 %153, label %154, label %160

154:                                              ; preds = %152
  br label %155

155:                                              ; preds = %154
  %156 = load i8*, i8** %26, align 8
  %157 = getelementptr inbounds i8, i8* %156, i32 1
  store i8* %157, i8** %26, align 8
  %158 = load i32, i32* %18, align 4
  %159 = add nsw i32 %158, 1
  store i32 %159, i32* %18, align 4
  br label %139, !llvm.loop !11

160:                                              ; preds = %152
  br label %407

161:                                              ; preds = %123
  store i64 0, i64* %27, align 8
  %162 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 8
  %163 = load i32, i32* %162, align 4
  switch i32 %163, label %197 [
    i32 0, label %164
    i32 1, label %168
    i32 2, label %173
    i32 3, label %177
    i32 4, label %182
    i32 5, label %185
    i32 6, label %188
    i32 7, label %191
    i32 8, label %194
  ]

164:                                              ; preds = %161
  %165 = va_arg i8** %8, i32
  store i32 %165, i32* %28, align 4
  %166 = load i32, i32* %28, align 4
  %167 = sext i32 %166 to i64
  store i64 %167, i64* %27, align 8
  br label %198

168:                                              ; preds = %161
  %169 = va_arg i8** %8, i32
  store i32 %169, i32* %29, align 4
  %170 = load i32, i32* %29, align 4
  %171 = trunc i32 %170 to i16
  %172 = sext i16 %171 to i64
  store i64 %172, i64* %27, align 8
  br label %198

173:                                              ; preds = %161
  %174 = va_arg i8** %8, i32
  store i32 %174, i32* %30, align 4
  %175 = load i32, i32* %30, align 4
  %176 = sext i32 %175 to i64
  store i64 %176, i64* %27, align 8
  br label %198

177:                                              ; preds = %161
  %178 = va_arg i8** %8, i32
  store i32 %178, i32* %31, align 4
  %179 = load i32, i32* %31, align 4
  %180 = trunc i32 %179 to i8
  %181 = sext i8 %180 to i64
  store i64 %181, i64* %27, align 8
  br label %198

182:                                              ; preds = %161
  %183 = va_arg i8** %8, i64
  store i64 %183, i64* %32, align 8
  %184 = load i64, i64* %32, align 8
  store i64 %184, i64* %27, align 8
  br label %198

185:                                              ; preds = %161
  %186 = va_arg i8** %8, i64
  store i64 %186, i64* %33, align 8
  %187 = load i64, i64* %33, align 8
  store i64 %187, i64* %27, align 8
  br label %198

188:                                              ; preds = %161
  %189 = va_arg i8** %8, i64
  store i64 %189, i64* %34, align 8
  %190 = load i64, i64* %34, align 8
  store i64 %190, i64* %27, align 8
  br label %198

191:                                              ; preds = %161
  %192 = va_arg i8** %8, i64
  store i64 %192, i64* %35, align 8
  %193 = load i64, i64* %35, align 8
  store i64 %193, i64* %27, align 8
  br label %198

194:                                              ; preds = %161
  %195 = va_arg i8** %8, i64
  store i64 %195, i64* %36, align 8
  %196 = load i64, i64* %36, align 8
  store i64 %196, i64* %27, align 8
  br label %198

197:                                              ; preds = %161
  br label %198

198:                                              ; preds = %197, %194, %191, %188, %185, %182, %177, %173, %168, %164
  %199 = load i64, i64* %27, align 8
  %200 = icmp slt i64 %199, 0
  br i1 %200, label %201, label %202

201:                                              ; preds = %198
  br label %205

202:                                              ; preds = %198
  %203 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 0
  %204 = load i8, i8* %203, align 4
  br label %205

205:                                              ; preds = %202, %201
  %206 = phi i8 [ 45, %201 ], [ %204, %202 ]
  store i8 %206, i8* %17, align 1
  %207 = load i64, i64* %27, align 8
  %208 = icmp ne i64 %207, 0
  %209 = xor i1 %208, true
  %210 = zext i1 %209 to i32
  store i32 %210, i32* %23, align 4
  %211 = load i64, i64* %27, align 8
  %212 = icmp ne i64 %211, 0
  br i1 %212, label %222, label %213

213:                                              ; preds = %205
  %214 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  %215 = load i32, i32* %214, align 4
  %216 = icmp eq i32 %215, 1
  br i1 %216, label %217, label %222

217:                                              ; preds = %213
  %218 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %219 = load i32, i32* %218, align 4
  %220 = icmp ne i32 %219, 0
  br i1 %220, label %222, label %221

221:                                              ; preds = %217
  store i32 0, i32* %18, align 4
  br label %235

222:                                              ; preds = %217, %213, %205
  %223 = load i64, i64* %27, align 8
  store i64 %223, i64* %37, align 8
  %224 = load i64, i64* %27, align 8
  %225 = icmp slt i64 %224, 0
  br i1 %225, label %226, label %229

226:                                              ; preds = %222
  %227 = load i64, i64* %37, align 8
  %228 = sub i64 0, %227
  store i64 %228, i64* %37, align 8
  br label %229

229:                                              ; preds = %226, %222
  %230 = load i64, i64* %37, align 8
  %231 = load i8*, i8** %16, align 8
  %232 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 10
  %233 = load i8, i8* %232, align 4
  %234 = call noundef i32 @_ZL12npf_utoa_revmPchc(i64 noundef %230, i8* noundef %231, i8 noundef zeroext 10, i8 noundef signext %233)
  store i32 %234, i32* %18, align 4
  br label %235

235:                                              ; preds = %229, %221
  br label %407

236:                                              ; preds = %123, %123, %123, %123
  store i64 0, i64* %38, align 8
  %237 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 8
  %238 = load i32, i32* %237, align 4
  switch i32 %238, label %272 [
    i32 0, label %239
    i32 1, label %243
    i32 2, label %248
    i32 3, label %252
    i32 4, label %257
    i32 5, label %260
    i32 6, label %263
    i32 7, label %266
    i32 8, label %269
  ]

239:                                              ; preds = %236
  %240 = va_arg i8** %8, i32
  store i32 %240, i32* %39, align 4
  %241 = load i32, i32* %39, align 4
  %242 = zext i32 %241 to i64
  store i64 %242, i64* %38, align 8
  br label %273

243:                                              ; preds = %236
  %244 = va_arg i8** %8, i32
  store i32 %244, i32* %40, align 4
  %245 = load i32, i32* %40, align 4
  %246 = trunc i32 %245 to i16
  %247 = zext i16 %246 to i64
  store i64 %247, i64* %38, align 8
  br label %273

248:                                              ; preds = %236
  %249 = va_arg i8** %8, i32
  store i32 %249, i32* %41, align 4
  %250 = load i32, i32* %41, align 4
  %251 = zext i32 %250 to i64
  store i64 %251, i64* %38, align 8
  br label %273

252:                                              ; preds = %236
  %253 = va_arg i8** %8, i32
  store i32 %253, i32* %42, align 4
  %254 = load i32, i32* %42, align 4
  %255 = trunc i32 %254 to i8
  %256 = zext i8 %255 to i64
  store i64 %256, i64* %38, align 8
  br label %273

257:                                              ; preds = %236
  %258 = va_arg i8** %8, i64
  store i64 %258, i64* %43, align 8
  %259 = load i64, i64* %43, align 8
  store i64 %259, i64* %38, align 8
  br label %273

260:                                              ; preds = %236
  %261 = va_arg i8** %8, i64
  store i64 %261, i64* %44, align 8
  %262 = load i64, i64* %44, align 8
  store i64 %262, i64* %38, align 8
  br label %273

263:                                              ; preds = %236
  %264 = va_arg i8** %8, i64
  store i64 %264, i64* %45, align 8
  %265 = load i64, i64* %45, align 8
  store i64 %265, i64* %38, align 8
  br label %273

266:                                              ; preds = %236
  %267 = va_arg i8** %8, i64
  store i64 %267, i64* %46, align 8
  %268 = load i64, i64* %46, align 8
  store i64 %268, i64* %38, align 8
  br label %273

269:                                              ; preds = %236
  %270 = va_arg i8** %8, i64
  store i64 %270, i64* %47, align 8
  %271 = load i64, i64* %47, align 8
  store i64 %271, i64* %38, align 8
  br label %273

272:                                              ; preds = %236
  br label %273

273:                                              ; preds = %272, %269, %266, %263, %260, %257, %252, %248, %243, %239
  %274 = load i64, i64* %38, align 8
  %275 = icmp ne i64 %274, 0
  %276 = xor i1 %275, true
  %277 = zext i1 %276 to i32
  store i32 %277, i32* %23, align 4
  %278 = load i64, i64* %38, align 8
  %279 = icmp ne i64 %278, 0
  br i1 %279, label %299, label %280

280:                                              ; preds = %273
  %281 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  %282 = load i32, i32* %281, align 4
  %283 = icmp eq i32 %282, 1
  br i1 %283, label %284, label %299

284:                                              ; preds = %280
  %285 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %286 = load i32, i32* %285, align 4
  %287 = icmp ne i32 %286, 0
  br i1 %287, label %299, label %288

288:                                              ; preds = %284
  %289 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %290 = load i32, i32* %289, align 4
  %291 = icmp eq i32 %290, 5
  br i1 %291, label %292, label %298

292:                                              ; preds = %288
  %293 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 1
  %294 = load i8, i8* %293, align 1
  %295 = icmp ne i8 %294, 0
  br i1 %295, label %296, label %298

296:                                              ; preds = %292
  %297 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  store i32 1, i32* %297, align 4
  br label %298

298:                                              ; preds = %296, %292, %288
  br label %329

299:                                              ; preds = %284, %280, %273
  %300 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %301 = load i32, i32* %300, align 4
  %302 = icmp eq i32 %301, 4
  br i1 %302, label %303, label %308

303:                                              ; preds = %299
  %304 = load i64, i64* %38, align 8
  %305 = call noundef i32 @_ZL11npf_bin_lenm(i64 noundef %304)
  store i32 %305, i32* %18, align 4
  %306 = load i64, i64* %38, align 8
  %307 = bitcast %union.anon* %15 to i64*
  store i64 %306, i64* %307, align 8
  br label %328

308:                                              ; preds = %299
  %309 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %310 = load i32, i32* %309, align 4
  %311 = icmp eq i32 %310, 5
  br i1 %311, label %312, label %313

312:                                              ; preds = %308
  br label %319

313:                                              ; preds = %308
  %314 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %315 = load i32, i32* %314, align 4
  %316 = icmp eq i32 %315, 6
  %317 = zext i1 %316 to i64
  %318 = select i1 %316, i32 16, i32 10
  br label %319

319:                                              ; preds = %313, %312
  %320 = phi i32 [ 8, %312 ], [ %318, %313 ]
  %321 = trunc i32 %320 to i8
  store i8 %321, i8* %48, align 1
  %322 = load i64, i64* %38, align 8
  %323 = load i8*, i8** %16, align 8
  %324 = load i8, i8* %48, align 1
  %325 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 10
  %326 = load i8, i8* %325, align 4
  %327 = call noundef i32 @_ZL12npf_utoa_revmPchc(i64 noundef %322, i8* noundef %323, i8 noundef zeroext %324, i8 noundef signext %326)
  store i32 %327, i32* %18, align 4
  br label %328

328:                                              ; preds = %319, %303
  br label %329

329:                                              ; preds = %328, %298
  %330 = load i64, i64* %38, align 8
  %331 = icmp ne i64 %330, 0
  br i1 %331, label %332, label %346

332:                                              ; preds = %329
  %333 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 1
  %334 = load i8, i8* %333, align 1
  %335 = icmp ne i8 %334, 0
  br i1 %335, label %336, label %346

336:                                              ; preds = %332
  %337 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %338 = load i32, i32* %337, align 4
  %339 = icmp eq i32 %338, 5
  br i1 %339, label %340, label %346

340:                                              ; preds = %336
  %341 = load i8*, i8** %16, align 8
  %342 = load i32, i32* %18, align 4
  %343 = add nsw i32 %342, 1
  store i32 %343, i32* %18, align 4
  %344 = sext i32 %342 to i64
  %345 = getelementptr inbounds i8, i8* %341, i64 %344
  store i8 48, i8* %345, align 1
  br label %346

346:                                              ; preds = %340, %336, %332, %329
  %347 = load i64, i64* %38, align 8
  %348 = icmp ne i64 %347, 0
  br i1 %348, label %349, label %374

349:                                              ; preds = %346
  %350 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 1
  %351 = load i8, i8* %350, align 1
  %352 = icmp ne i8 %351, 0
  br i1 %352, label %353, label %374

353:                                              ; preds = %349
  %354 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %355 = load i32, i32* %354, align 4
  %356 = icmp eq i32 %355, 6
  br i1 %356, label %357, label %358

357:                                              ; preds = %353
  store i32 88, i32* %19, align 4
  br label %364

358:                                              ; preds = %353
  %359 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %360 = load i32, i32* %359, align 4
  %361 = icmp eq i32 %360, 4
  br i1 %361, label %362, label %363

362:                                              ; preds = %358
  store i32 66, i32* %19, align 4
  br label %363

363:                                              ; preds = %362, %358
  br label %364

364:                                              ; preds = %363, %357
  %365 = load i32, i32* %19, align 4
  %366 = icmp ne i32 %365, 0
  br i1 %366, label %367, label %373

367:                                              ; preds = %364
  %368 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 10
  %369 = load i8, i8* %368, align 4
  %370 = sext i8 %369 to i32
  %371 = load i32, i32* %19, align 4
  %372 = add nsw i32 %371, %370
  store i32 %372, i32* %19, align 4
  br label %373

373:                                              ; preds = %367, %364
  br label %374

374:                                              ; preds = %373, %349, %346
  br label %407

375:                                              ; preds = %123
  %376 = va_arg i8** %8, i8*
  store i8* %376, i8** %49, align 8
  %377 = load i8*, i8** %49, align 8
  %378 = ptrtoint i8* %377 to i64
  %379 = load i8*, i8** %16, align 8
  %380 = call noundef i32 @_ZL12npf_utoa_revmPchc(i64 noundef %378, i8* noundef %379, i8 noundef zeroext 16, i8 noundef signext 32)
  store i32 %380, i32* %18, align 4
  store i32 120, i32* %19, align 4
  br label %407

381:                                              ; preds = %123, %123, %123, %123
  %382 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 8
  %383 = load i32, i32* %382, align 4
  %384 = icmp eq i32 %383, 2
  br i1 %384, label %385, label %388

385:                                              ; preds = %381
  %386 = va_arg i8** %8, double
  store double %386, double* %51, align 8
  %387 = load double, double* %51, align 8
  store double %387, double* %50, align 8
  br label %391

388:                                              ; preds = %381
  %389 = va_arg i8** %8, double
  store double %389, double* %52, align 8
  %390 = load double, double* %52, align 8
  store double %390, double* %50, align 8
  br label %391

391:                                              ; preds = %388, %385
  %392 = load double, double* %50, align 8
  %393 = fcmp olt double %392, 0.000000e+00
  br i1 %393, label %394, label %395

394:                                              ; preds = %391
  br label %398

395:                                              ; preds = %391
  %396 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 0
  %397 = load i8, i8* %396, align 4
  br label %398

398:                                              ; preds = %395, %394
  %399 = phi i8 [ 45, %394 ], [ %397, %395 ]
  store i8 %399, i8* %17, align 1
  %400 = load double, double* %50, align 8
  %401 = fcmp oeq double %400, 0.000000e+00
  %402 = zext i1 %401 to i32
  store i32 %402, i32* %23, align 4
  %403 = load i8*, i8** %16, align 8
  %404 = load double, double* %50, align 8
  %405 = call noundef i32 @_ZL12npf_ftoa_revPcPK15npf_format_specd(i8* noundef %403, %struct.npf_format_spec* noundef %9, double noundef %404)
  store i32 %405, i32* %18, align 4
  br label %407

406:                                              ; preds = %123
  br label %407

407:                                              ; preds = %406, %398, %375, %374, %235, %160, %130, %128
  %408 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 2
  %409 = load i32, i32* %408, align 4
  %410 = icmp eq i32 %409, 1
  br i1 %410, label %411, label %444

411:                                              ; preds = %407
  %412 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 5
  %413 = load i8, i8* %412, align 1
  %414 = icmp ne i8 %413, 0
  br i1 %414, label %415, label %442

415:                                              ; preds = %411
  %416 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %417 = load i32, i32* %416, align 4
  %418 = icmp ne i32 %417, 2
  br i1 %418, label %419, label %441

419:                                              ; preds = %415
  %420 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %421 = load i32, i32* %420, align 4
  %422 = icmp ne i32 %421, 1
  br i1 %422, label %423, label %441

423:                                              ; preds = %419
  %424 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %425 = load i32, i32* %424, align 4
  %426 = icmp ne i32 %425, 0
  br i1 %426, label %427, label %441

427:                                              ; preds = %423
  %428 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 6
  %429 = load i32, i32* %428, align 4
  %430 = icmp eq i32 %429, 1
  br i1 %430, label %431, label %439

431:                                              ; preds = %427
  %432 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %433 = load i32, i32* %432, align 4
  %434 = icmp ne i32 %433, 0
  br i1 %434, label %439, label %435

435:                                              ; preds = %431
  %436 = load i32, i32* %23, align 4
  %437 = icmp ne i32 %436, 0
  br i1 %437, label %438, label %439

438:                                              ; preds = %435
  store i8 32, i8* %21, align 1
  br label %440

439:                                              ; preds = %435, %431, %427
  store i8 48, i8* %21, align 1
  br label %440

440:                                              ; preds = %439, %438
  br label %441

441:                                              ; preds = %440, %423, %419, %415
  br label %443

442:                                              ; preds = %411
  store i8 32, i8* %21, align 1
  br label %443

443:                                              ; preds = %442, %441
  br label %444

444:                                              ; preds = %443, %407
  %445 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %446 = load i32, i32* %445, align 4
  %447 = icmp ne i32 %446, 2
  br i1 %447, label %448, label %459

448:                                              ; preds = %444
  %449 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %450 = load i32, i32* %449, align 4
  %451 = icmp ne i32 %450, 9
  br i1 %451, label %452, label %458

452:                                              ; preds = %448
  %453 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 7
  %454 = load i32, i32* %453, align 4
  %455 = load i32, i32* %18, align 4
  %456 = sub nsw i32 %454, %455
  %457 = call noundef i32 @_ZL7npf_maxii(i32 noundef 0, i32 noundef %456)
  store i32 %457, i32* %22, align 4
  br label %458

458:                                              ; preds = %452, %448
  br label %459

459:                                              ; preds = %458, %444
  %460 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 3
  %461 = load i32, i32* %460, align 4
  %462 = load i32, i32* %18, align 4
  %463 = sub nsw i32 %461, %462
  %464 = load i8, i8* %17, align 1
  %465 = icmp ne i8 %464, 0
  %466 = xor i1 %465, true
  %467 = xor i1 %466, true
  %468 = zext i1 %467 to i32
  %469 = sub nsw i32 %463, %468
  store i32 %469, i32* %20, align 4
  %470 = load i32, i32* %19, align 4
  %471 = icmp ne i32 %470, 0
  br i1 %471, label %472, label %475

472:                                              ; preds = %459
  %473 = load i32, i32* %20, align 4
  %474 = sub nsw i32 %473, 2
  store i32 %474, i32* %20, align 4
  br label %475

475:                                              ; preds = %472, %459
  %476 = load i32, i32* %22, align 4
  %477 = load i32, i32* %20, align 4
  %478 = sub nsw i32 %477, %476
  store i32 %478, i32* %20, align 4
  %479 = load i32, i32* %20, align 4
  %480 = call noundef i32 @_ZL7npf_maxii(i32 noundef 0, i32 noundef %479)
  store i32 %480, i32* %20, align 4
  %481 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 4
  %482 = load i8, i8* %481, align 4
  %483 = icmp ne i8 %482, 0
  br i1 %483, label %539, label %484

484:                                              ; preds = %475
  %485 = load i8, i8* %21, align 1
  %486 = icmp ne i8 %485, 0
  br i1 %486, label %487, label %539

487:                                              ; preds = %484
  %488 = load i8, i8* %21, align 1
  %489 = sext i8 %488 to i32
  %490 = icmp eq i32 %489, 48
  br i1 %490, label %491, label %512

491:                                              ; preds = %487
  %492 = load i8, i8* %17, align 1
  %493 = icmp ne i8 %492, 0
  br i1 %493, label %494, label %500

494:                                              ; preds = %491
  br label %495

495:                                              ; preds = %494
  %496 = load i8, i8* %17, align 1
  %497 = sext i8 %496 to i32
  %498 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %497, i8* noundef %498)
  br label %499

499:                                              ; preds = %495
  store i8 0, i8* %17, align 1
  br label %500

500:                                              ; preds = %499, %491
  %501 = load i32, i32* %19, align 4
  %502 = icmp ne i32 %501, 0
  br i1 %502, label %503, label %511

503:                                              ; preds = %500
  br label %504

504:                                              ; preds = %503
  %505 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef 48, i8* noundef %505)
  br label %506

506:                                              ; preds = %504
  br label %507

507:                                              ; preds = %506
  %508 = load i32, i32* %19, align 4
  %509 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %508, i8* noundef %509)
  br label %510

510:                                              ; preds = %507
  br label %511

511:                                              ; preds = %510, %500
  br label %512

512:                                              ; preds = %511, %487
  br label %513

513:                                              ; preds = %522, %512
  %514 = load i32, i32* %20, align 4
  %515 = add nsw i32 %514, -1
  store i32 %515, i32* %20, align 4
  %516 = icmp sgt i32 %514, 0
  br i1 %516, label %517, label %523

517:                                              ; preds = %513
  br label %518

518:                                              ; preds = %517
  %519 = load i8, i8* %21, align 1
  %520 = sext i8 %519 to i32
  %521 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %520, i8* noundef %521)
  br label %522

522:                                              ; preds = %518
  br label %513, !llvm.loop !12

523:                                              ; preds = %513
  %524 = load i8, i8* %21, align 1
  %525 = sext i8 %524 to i32
  %526 = icmp ne i32 %525, 48
  br i1 %526, label %527, label %538

527:                                              ; preds = %523
  %528 = load i32, i32* %19, align 4
  %529 = icmp ne i32 %528, 0
  br i1 %529, label %530, label %538

530:                                              ; preds = %527
  br label %531

531:                                              ; preds = %530
  %532 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef 48, i8* noundef %532)
  br label %533

533:                                              ; preds = %531
  br label %534

534:                                              ; preds = %533
  %535 = load i32, i32* %19, align 4
  %536 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %535, i8* noundef %536)
  br label %537

537:                                              ; preds = %534
  br label %538

538:                                              ; preds = %537, %527, %523
  br label %551

539:                                              ; preds = %484, %475
  %540 = load i32, i32* %19, align 4
  %541 = icmp ne i32 %540, 0
  br i1 %541, label %542, label %550

542:                                              ; preds = %539
  br label %543

543:                                              ; preds = %542
  %544 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef 48, i8* noundef %544)
  br label %545

545:                                              ; preds = %543
  br label %546

546:                                              ; preds = %545
  %547 = load i32, i32* %19, align 4
  %548 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %547, i8* noundef %548)
  br label %549

549:                                              ; preds = %546
  br label %550

550:                                              ; preds = %549, %539
  br label %551

551:                                              ; preds = %550, %538
  %552 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %553 = load i32, i32* %552, align 4
  %554 = icmp eq i32 %553, 2
  br i1 %554, label %555, label %574

555:                                              ; preds = %551
  store i32 0, i32* %53, align 4
  br label %556

556:                                              ; preds = %570, %555
  %557 = load i32, i32* %53, align 4
  %558 = load i32, i32* %18, align 4
  %559 = icmp slt i32 %557, %558
  br i1 %559, label %560, label %573

560:                                              ; preds = %556
  br label %561

561:                                              ; preds = %560
  %562 = load i8*, i8** %16, align 8
  %563 = load i32, i32* %53, align 4
  %564 = sext i32 %563 to i64
  %565 = getelementptr inbounds i8, i8* %562, i64 %564
  %566 = load i8, i8* %565, align 1
  %567 = sext i8 %566 to i32
  %568 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %567, i8* noundef %568)
  br label %569

569:                                              ; preds = %561
  br label %570

570:                                              ; preds = %569
  %571 = load i32, i32* %53, align 4
  %572 = add nsw i32 %571, 1
  store i32 %572, i32* %53, align 4
  br label %556, !llvm.loop !13

573:                                              ; preds = %556
  br label %631

574:                                              ; preds = %551
  %575 = load i8, i8* %17, align 1
  %576 = icmp ne i8 %575, 0
  br i1 %576, label %577, label %583

577:                                              ; preds = %574
  br label %578

578:                                              ; preds = %577
  %579 = load i8, i8* %17, align 1
  %580 = sext i8 %579 to i32
  %581 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %580, i8* noundef %581)
  br label %582

582:                                              ; preds = %578
  br label %583

583:                                              ; preds = %582, %574
  br label %584

584:                                              ; preds = %591, %583
  %585 = load i32, i32* %22, align 4
  %586 = add nsw i32 %585, -1
  store i32 %586, i32* %22, align 4
  %587 = icmp sgt i32 %585, 0
  br i1 %587, label %588, label %592

588:                                              ; preds = %584
  br label %589

589:                                              ; preds = %588
  %590 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef 48, i8* noundef %590)
  br label %591

591:                                              ; preds = %589
  br label %584, !llvm.loop !14

592:                                              ; preds = %584
  %593 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 9
  %594 = load i32, i32* %593, align 4
  %595 = icmp eq i32 %594, 4
  br i1 %595, label %596, label %614

596:                                              ; preds = %592
  br label %597

597:                                              ; preds = %612, %596
  %598 = load i32, i32* %18, align 4
  %599 = icmp ne i32 %598, 0
  br i1 %599, label %600, label %613

600:                                              ; preds = %597
  br label %601

601:                                              ; preds = %600
  %602 = bitcast %union.anon* %15 to i64*
  %603 = load i64, i64* %602, align 8
  %604 = load i32, i32* %18, align 4
  %605 = add nsw i32 %604, -1
  store i32 %605, i32* %18, align 4
  %606 = zext i32 %605 to i64
  %607 = lshr i64 %603, %606
  %608 = and i64 %607, 1
  %609 = add i64 48, %608
  %610 = trunc i64 %609 to i32
  %611 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %610, i8* noundef %611)
  br label %612

612:                                              ; preds = %601
  br label %597, !llvm.loop !15

613:                                              ; preds = %597
  br label %630

614:                                              ; preds = %592
  br label %615

615:                                              ; preds = %628, %614
  %616 = load i32, i32* %18, align 4
  %617 = add nsw i32 %616, -1
  store i32 %617, i32* %18, align 4
  %618 = icmp sgt i32 %616, 0
  br i1 %618, label %619, label %629

619:                                              ; preds = %615
  br label %620

620:                                              ; preds = %619
  %621 = load i8*, i8** %16, align 8
  %622 = load i32, i32* %18, align 4
  %623 = sext i32 %622 to i64
  %624 = getelementptr inbounds i8, i8* %621, i64 %623
  %625 = load i8, i8* %624, align 1
  %626 = sext i8 %625 to i32
  %627 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %626, i8* noundef %627)
  br label %628

628:                                              ; preds = %620
  br label %615, !llvm.loop !16

629:                                              ; preds = %615
  br label %630

630:                                              ; preds = %629, %613
  br label %631

631:                                              ; preds = %630, %573
  %632 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 4
  %633 = load i8, i8* %632, align 4
  %634 = icmp ne i8 %633, 0
  br i1 %634, label %635, label %650

635:                                              ; preds = %631
  %636 = load i8, i8* %21, align 1
  %637 = icmp ne i8 %636, 0
  br i1 %637, label %638, label %650

638:                                              ; preds = %635
  br label %639

639:                                              ; preds = %648, %638
  %640 = load i32, i32* %20, align 4
  %641 = add nsw i32 %640, -1
  store i32 %641, i32* %20, align 4
  %642 = icmp sgt i32 %640, 0
  br i1 %642, label %643, label %649

643:                                              ; preds = %639
  br label %644

644:                                              ; preds = %643
  %645 = load i8, i8* %21, align 1
  %646 = sext i8 %645 to i32
  %647 = bitcast %struct.npf_cnt_putc_ctx* %11 to i8*
  call void @_ZL12npf_putc_cntiPv(i32 noundef %646, i8* noundef %647)
  br label %648

648:                                              ; preds = %644
  br label %639, !llvm.loop !17

649:                                              ; preds = %639
  br label %650

650:                                              ; preds = %649, %635, %631
  br label %60, !llvm.loop !9

651:                                              ; preds = %60
  %652 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %11, i32 0, i32 2
  %653 = load i32, i32* %652, align 8
  ret i32 %653
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal noundef i32 @_ZL21npf_parse_format_specPKcP15npf_format_spec(i8* noundef %0, %struct.npf_format_spec* noundef %1) #1 {
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 8
  %5 = alloca %struct.npf_format_spec*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i32, align 4
  store i8* %0, i8** %4, align 8
  store %struct.npf_format_spec* %1, %struct.npf_format_spec** %5, align 8
  %8 = load i8*, i8** %4, align 8
  store i8* %8, i8** %6, align 8
  %9 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %10 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %9, i32 0, i32 4
  store i8 0, i8* %10, align 4
  %11 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %12 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %11, i32 0, i32 5
  store i8 0, i8* %12, align 1
  %13 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %14 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %13, i32 0, i32 10
  store i8 32, i8* %14, align 4
  %15 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %16 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %15, i32 0, i32 0
  store i8 0, i8* %16, align 4
  %17 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %18 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %17, i32 0, i32 1
  store i8 0, i8* %18, align 1
  br label %19

19:                                               ; preds = %55, %54, %42, %33, %28, %2
  %20 = load i8*, i8** %6, align 8
  %21 = getelementptr inbounds i8, i8* %20, i32 1
  store i8* %21, i8** %6, align 8
  %22 = load i8, i8* %21, align 1
  %23 = icmp ne i8 %22, 0
  br i1 %23, label %24, label %60

24:                                               ; preds = %19
  %25 = load i8*, i8** %6, align 8
  %26 = load i8, i8* %25, align 1
  %27 = sext i8 %26 to i32
  switch i32 %27, label %58 [
    i32 45, label %28
    i32 48, label %33
    i32 43, label %42
    i32 32, label %45
    i32 35, label %55
  ]

28:                                               ; preds = %24
  %29 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %30 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %29, i32 0, i32 4
  store i8 45, i8* %30, align 4
  %31 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %32 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %31, i32 0, i32 5
  store i8 0, i8* %32, align 1
  br label %19, !llvm.loop !18

33:                                               ; preds = %24
  %34 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %35 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %34, i32 0, i32 4
  %36 = load i8, i8* %35, align 4
  %37 = icmp ne i8 %36, 0
  %38 = xor i1 %37, true
  %39 = zext i1 %38 to i8
  %40 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %41 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %40, i32 0, i32 5
  store i8 %39, i8* %41, align 1
  br label %19, !llvm.loop !18

42:                                               ; preds = %24
  %43 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %44 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %43, i32 0, i32 0
  store i8 43, i8* %44, align 4
  br label %19, !llvm.loop !18

45:                                               ; preds = %24
  %46 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %47 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %46, i32 0, i32 0
  %48 = load i8, i8* %47, align 4
  %49 = sext i8 %48 to i32
  %50 = icmp eq i32 %49, 0
  br i1 %50, label %51, label %54

51:                                               ; preds = %45
  %52 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %53 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %52, i32 0, i32 0
  store i8 32, i8* %53, align 4
  br label %54

54:                                               ; preds = %51, %45
  br label %19, !llvm.loop !18

55:                                               ; preds = %24
  %56 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %57 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %56, i32 0, i32 1
  store i8 35, i8* %57, align 1
  br label %19, !llvm.loop !18

58:                                               ; preds = %24
  br label %59

59:                                               ; preds = %58
  br label %60

60:                                               ; preds = %59, %19
  %61 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %62 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %61, i32 0, i32 2
  store i32 0, i32* %62, align 4
  %63 = load i8*, i8** %6, align 8
  %64 = load i8, i8* %63, align 1
  %65 = sext i8 %64 to i32
  %66 = icmp eq i32 %65, 42
  br i1 %66, label %67, label %72

67:                                               ; preds = %60
  %68 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %69 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %68, i32 0, i32 2
  store i32 2, i32* %69, align 4
  %70 = load i8*, i8** %6, align 8
  %71 = getelementptr inbounds i8, i8* %70, i32 1
  store i8* %71, i8** %6, align 8
  br label %103

72:                                               ; preds = %60
  %73 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %74 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %73, i32 0, i32 3
  store i32 0, i32* %74, align 4
  br label %75

75:                                               ; preds = %87, %72
  %76 = load i8*, i8** %6, align 8
  %77 = load i8, i8* %76, align 1
  %78 = sext i8 %77 to i32
  %79 = icmp sge i32 %78, 48
  br i1 %79, label %80, label %85

80:                                               ; preds = %75
  %81 = load i8*, i8** %6, align 8
  %82 = load i8, i8* %81, align 1
  %83 = sext i8 %82 to i32
  %84 = icmp sle i32 %83, 57
  br label %85

85:                                               ; preds = %80, %75
  %86 = phi i1 [ false, %75 ], [ %84, %80 ]
  br i1 %86, label %87, label %102

87:                                               ; preds = %85
  %88 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %89 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %88, i32 0, i32 2
  store i32 1, i32* %89, align 4
  %90 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %91 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %90, i32 0, i32 3
  %92 = load i32, i32* %91, align 4
  %93 = mul nsw i32 %92, 10
  %94 = load i8*, i8** %6, align 8
  %95 = getelementptr inbounds i8, i8* %94, i32 1
  store i8* %95, i8** %6, align 8
  %96 = load i8, i8* %94, align 1
  %97 = sext i8 %96 to i32
  %98 = sub nsw i32 %97, 48
  %99 = add nsw i32 %93, %98
  %100 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %101 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %100, i32 0, i32 3
  store i32 %99, i32* %101, align 4
  br label %75, !llvm.loop !19

102:                                              ; preds = %85
  br label %103

103:                                              ; preds = %102, %67
  %104 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %105 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %104, i32 0, i32 7
  store i32 0, i32* %105, align 4
  %106 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %107 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %106, i32 0, i32 6
  store i32 0, i32* %107, align 4
  %108 = load i8*, i8** %6, align 8
  %109 = load i8, i8* %108, align 1
  %110 = sext i8 %109 to i32
  %111 = icmp eq i32 %110, 46
  br i1 %111, label %112, label %165

112:                                              ; preds = %103
  %113 = load i8*, i8** %6, align 8
  %114 = getelementptr inbounds i8, i8* %113, i32 1
  store i8* %114, i8** %6, align 8
  %115 = load i8*, i8** %6, align 8
  %116 = load i8, i8* %115, align 1
  %117 = sext i8 %116 to i32
  %118 = icmp eq i32 %117, 42
  br i1 %118, label %119, label %124

119:                                              ; preds = %112
  %120 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %121 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %120, i32 0, i32 6
  store i32 2, i32* %121, align 4
  %122 = load i8*, i8** %6, align 8
  %123 = getelementptr inbounds i8, i8* %122, i32 1
  store i8* %123, i8** %6, align 8
  br label %164

124:                                              ; preds = %112
  %125 = load i8*, i8** %6, align 8
  %126 = load i8, i8* %125, align 1
  %127 = sext i8 %126 to i32
  %128 = icmp eq i32 %127, 45
  br i1 %128, label %129, label %134

129:                                              ; preds = %124
  %130 = load i8*, i8** %6, align 8
  %131 = getelementptr inbounds i8, i8* %130, i32 1
  store i8* %131, i8** %6, align 8
  %132 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %133 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %132, i32 0, i32 6
  store i32 0, i32* %133, align 4
  br label %137

134:                                              ; preds = %124
  %135 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %136 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %135, i32 0, i32 6
  store i32 1, i32* %136, align 4
  br label %137

137:                                              ; preds = %134, %129
  br label %138

138:                                              ; preds = %150, %137
  %139 = load i8*, i8** %6, align 8
  %140 = load i8, i8* %139, align 1
  %141 = sext i8 %140 to i32
  %142 = icmp sge i32 %141, 48
  br i1 %142, label %143, label %148

143:                                              ; preds = %138
  %144 = load i8*, i8** %6, align 8
  %145 = load i8, i8* %144, align 1
  %146 = sext i8 %145 to i32
  %147 = icmp sle i32 %146, 57
  br label %148

148:                                              ; preds = %143, %138
  %149 = phi i1 [ false, %138 ], [ %147, %143 ]
  br i1 %149, label %150, label %163

150:                                              ; preds = %148
  %151 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %152 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %151, i32 0, i32 7
  %153 = load i32, i32* %152, align 4
  %154 = mul nsw i32 %153, 10
  %155 = load i8*, i8** %6, align 8
  %156 = getelementptr inbounds i8, i8* %155, i32 1
  store i8* %156, i8** %6, align 8
  %157 = load i8, i8* %155, align 1
  %158 = sext i8 %157 to i32
  %159 = sub nsw i32 %158, 48
  %160 = add nsw i32 %154, %159
  %161 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %162 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %161, i32 0, i32 7
  store i32 %160, i32* %162, align 4
  br label %138, !llvm.loop !20

163:                                              ; preds = %148
  br label %164

164:                                              ; preds = %163, %119
  br label %165

165:                                              ; preds = %164, %103
  store i32 -1, i32* %7, align 4
  %166 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %167 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %166, i32 0, i32 8
  store i32 0, i32* %167, align 4
  %168 = load i8*, i8** %6, align 8
  %169 = getelementptr inbounds i8, i8* %168, i32 1
  store i8* %169, i8** %6, align 8
  %170 = load i8, i8* %168, align 1
  %171 = sext i8 %170 to i32
  switch i32 %171, label %210 [
    i32 104, label %172
    i32 108, label %185
    i32 76, label %198
    i32 106, label %201
    i32 122, label %204
    i32 116, label %207
  ]

172:                                              ; preds = %165
  %173 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %174 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %173, i32 0, i32 8
  store i32 1, i32* %174, align 4
  %175 = load i8*, i8** %6, align 8
  %176 = load i8, i8* %175, align 1
  %177 = sext i8 %176 to i32
  %178 = icmp eq i32 %177, 104
  br i1 %178, label %179, label %184

179:                                              ; preds = %172
  %180 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %181 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %180, i32 0, i32 8
  store i32 3, i32* %181, align 4
  %182 = load i8*, i8** %6, align 8
  %183 = getelementptr inbounds i8, i8* %182, i32 1
  store i8* %183, i8** %6, align 8
  br label %184

184:                                              ; preds = %179, %172
  br label %213

185:                                              ; preds = %165
  %186 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %187 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %186, i32 0, i32 8
  store i32 4, i32* %187, align 4
  %188 = load i8*, i8** %6, align 8
  %189 = load i8, i8* %188, align 1
  %190 = sext i8 %189 to i32
  %191 = icmp eq i32 %190, 108
  br i1 %191, label %192, label %197

192:                                              ; preds = %185
  %193 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %194 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %193, i32 0, i32 8
  store i32 5, i32* %194, align 4
  %195 = load i8*, i8** %6, align 8
  %196 = getelementptr inbounds i8, i8* %195, i32 1
  store i8* %196, i8** %6, align 8
  br label %197

197:                                              ; preds = %192, %185
  br label %213

198:                                              ; preds = %165
  %199 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %200 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %199, i32 0, i32 8
  store i32 2, i32* %200, align 4
  br label %213

201:                                              ; preds = %165
  %202 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %203 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %202, i32 0, i32 8
  store i32 6, i32* %203, align 4
  br label %213

204:                                              ; preds = %165
  %205 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %206 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %205, i32 0, i32 8
  store i32 7, i32* %206, align 4
  br label %213

207:                                              ; preds = %165
  %208 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %209 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %208, i32 0, i32 8
  store i32 8, i32* %209, align 4
  br label %213

210:                                              ; preds = %165
  %211 = load i8*, i8** %6, align 8
  %212 = getelementptr inbounds i8, i8* %211, i32 -1
  store i8* %212, i8** %6, align 8
  br label %213

213:                                              ; preds = %210, %207, %204, %201, %198, %197, %184
  %214 = load i8*, i8** %6, align 8
  %215 = getelementptr inbounds i8, i8* %214, i32 1
  store i8* %215, i8** %6, align 8
  %216 = load i8, i8* %214, align 1
  %217 = sext i8 %216 to i32
  switch i32 %217, label %334 [
    i32 37, label %218
    i32 99, label %223
    i32 115, label %228
    i32 105, label %233
    i32 100, label %233
    i32 111, label %234
    i32 117, label %239
    i32 88, label %244
    i32 120, label %251
    i32 70, label %267
    i32 102, label %270
    i32 69, label %281
    i32 101, label %284
    i32 71, label %295
    i32 103, label %298
    i32 65, label %309
    i32 97, label %312
    i32 112, label %323
    i32 66, label %328
    i32 98, label %331
  ]

218:                                              ; preds = %213
  %219 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %220 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %219, i32 0, i32 9
  store i32 0, i32* %220, align 4
  %221 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %222 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %221, i32 0, i32 6
  store i32 0, i32* %222, align 4
  br label %335

223:                                              ; preds = %213
  %224 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %225 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %224, i32 0, i32 9
  store i32 1, i32* %225, align 4
  %226 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %227 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %226, i32 0, i32 6
  store i32 0, i32* %227, align 4
  br label %335

228:                                              ; preds = %213
  %229 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %230 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %229, i32 0, i32 9
  store i32 2, i32* %230, align 4
  %231 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %232 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %231, i32 0, i32 5
  store i8 0, i8* %232, align 1
  br label %335

233:                                              ; preds = %213, %213
  store i32 3, i32* %7, align 4
  br label %234

234:                                              ; preds = %213, %233
  %235 = load i32, i32* %7, align 4
  %236 = icmp eq i32 %235, -1
  br i1 %236, label %237, label %238

237:                                              ; preds = %234
  store i32 5, i32* %7, align 4
  br label %238

238:                                              ; preds = %237, %234
  br label %239

239:                                              ; preds = %213, %238
  %240 = load i32, i32* %7, align 4
  %241 = icmp eq i32 %240, -1
  br i1 %241, label %242, label %243

242:                                              ; preds = %239
  store i32 7, i32* %7, align 4
  br label %243

243:                                              ; preds = %242, %239
  br label %244

244:                                              ; preds = %213, %243
  %245 = load i32, i32* %7, align 4
  %246 = icmp eq i32 %245, -1
  br i1 %246, label %247, label %250

247:                                              ; preds = %244
  %248 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %249 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %248, i32 0, i32 10
  store i8 0, i8* %249, align 4
  br label %250

250:                                              ; preds = %247, %244
  br label %251

251:                                              ; preds = %213, %250
  %252 = load i32, i32* %7, align 4
  %253 = icmp eq i32 %252, -1
  br i1 %253, label %254, label %255

254:                                              ; preds = %251
  store i32 6, i32* %7, align 4
  br label %255

255:                                              ; preds = %254, %251
  %256 = load i32, i32* %7, align 4
  %257 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %258 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %257, i32 0, i32 9
  store i32 %256, i32* %258, align 4
  %259 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %260 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %259, i32 0, i32 6
  %261 = load i32, i32* %260, align 4
  %262 = icmp ne i32 %261, 0
  br i1 %262, label %263, label %266

263:                                              ; preds = %255
  %264 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %265 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %264, i32 0, i32 5
  store i8 0, i8* %265, align 1
  br label %266

266:                                              ; preds = %263, %255
  br label %335

267:                                              ; preds = %213
  %268 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %269 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %268, i32 0, i32 10
  store i8 0, i8* %269, align 4
  br label %270

270:                                              ; preds = %213, %267
  %271 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %272 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %271, i32 0, i32 9
  store i32 9, i32* %272, align 4
  %273 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %274 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %273, i32 0, i32 6
  %275 = load i32, i32* %274, align 4
  %276 = icmp eq i32 %275, 0
  br i1 %276, label %277, label %280

277:                                              ; preds = %270
  %278 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %279 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %278, i32 0, i32 7
  store i32 6, i32* %279, align 4
  br label %280

280:                                              ; preds = %277, %270
  br label %335

281:                                              ; preds = %213
  %282 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %283 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %282, i32 0, i32 10
  store i8 0, i8* %283, align 4
  br label %284

284:                                              ; preds = %213, %281
  %285 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %286 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %285, i32 0, i32 9
  store i32 10, i32* %286, align 4
  %287 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %288 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %287, i32 0, i32 6
  %289 = load i32, i32* %288, align 4
  %290 = icmp eq i32 %289, 0
  br i1 %290, label %291, label %294

291:                                              ; preds = %284
  %292 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %293 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %292, i32 0, i32 7
  store i32 6, i32* %293, align 4
  br label %294

294:                                              ; preds = %291, %284
  br label %335

295:                                              ; preds = %213
  %296 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %297 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %296, i32 0, i32 10
  store i8 0, i8* %297, align 4
  br label %298

298:                                              ; preds = %213, %295
  %299 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %300 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %299, i32 0, i32 9
  store i32 11, i32* %300, align 4
  %301 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %302 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %301, i32 0, i32 6
  %303 = load i32, i32* %302, align 4
  %304 = icmp eq i32 %303, 0
  br i1 %304, label %305, label %308

305:                                              ; preds = %298
  %306 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %307 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %306, i32 0, i32 7
  store i32 6, i32* %307, align 4
  br label %308

308:                                              ; preds = %305, %298
  br label %335

309:                                              ; preds = %213
  %310 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %311 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %310, i32 0, i32 10
  store i8 0, i8* %311, align 4
  br label %312

312:                                              ; preds = %213, %309
  %313 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %314 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %313, i32 0, i32 9
  store i32 12, i32* %314, align 4
  %315 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %316 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %315, i32 0, i32 6
  %317 = load i32, i32* %316, align 4
  %318 = icmp eq i32 %317, 0
  br i1 %318, label %319, label %322

319:                                              ; preds = %312
  %320 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %321 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %320, i32 0, i32 7
  store i32 6, i32* %321, align 4
  br label %322

322:                                              ; preds = %319, %312
  br label %335

323:                                              ; preds = %213
  %324 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %325 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %324, i32 0, i32 9
  store i32 8, i32* %325, align 4
  %326 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %327 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %326, i32 0, i32 6
  store i32 0, i32* %327, align 4
  br label %335

328:                                              ; preds = %213
  %329 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %330 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %329, i32 0, i32 10
  store i8 0, i8* %330, align 4
  br label %331

331:                                              ; preds = %213, %328
  %332 = load %struct.npf_format_spec*, %struct.npf_format_spec** %5, align 8
  %333 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %332, i32 0, i32 9
  store i32 4, i32* %333, align 4
  br label %335

334:                                              ; preds = %213
  store i32 0, i32* %3, align 4
  br label %342

335:                                              ; preds = %331, %323, %322, %308, %294, %280, %266, %228, %223, %218
  %336 = load i8*, i8** %6, align 8
  %337 = load i8*, i8** %4, align 8
  %338 = ptrtoint i8* %336 to i64
  %339 = ptrtoint i8* %337 to i64
  %340 = sub i64 %338, %339
  %341 = trunc i64 %340 to i32
  store i32 %341, i32* %3, align 4
  br label %342

342:                                              ; preds = %335, %334
  %343 = load i32, i32* %3, align 4
  ret i32 %343
}

; Function Attrs: mustprogress noinline optnone ssp uwtable
define internal void @_ZL12npf_putc_cntiPv(i32 noundef %0, i8* noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 8
  %5 = alloca %struct.npf_cnt_putc_ctx*, align 8
  store i32 %0, i32* %3, align 4
  store i8* %1, i8** %4, align 8
  %6 = load i8*, i8** %4, align 8
  %7 = bitcast i8* %6 to %struct.npf_cnt_putc_ctx*
  store %struct.npf_cnt_putc_ctx* %7, %struct.npf_cnt_putc_ctx** %5, align 8
  %8 = load %struct.npf_cnt_putc_ctx*, %struct.npf_cnt_putc_ctx** %5, align 8
  %9 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %8, i32 0, i32 2
  %10 = load i32, i32* %9, align 8
  %11 = add nsw i32 %10, 1
  store i32 %11, i32* %9, align 8
  %12 = load %struct.npf_cnt_putc_ctx*, %struct.npf_cnt_putc_ctx** %5, align 8
  %13 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %12, i32 0, i32 0
  %14 = load void (i32, i8*)*, void (i32, i8*)** %13, align 8
  %15 = load i32, i32* %3, align 4
  %16 = load %struct.npf_cnt_putc_ctx*, %struct.npf_cnt_putc_ctx** %5, align 8
  %17 = getelementptr inbounds %struct.npf_cnt_putc_ctx, %struct.npf_cnt_putc_ctx* %16, i32 0, i32 1
  %18 = load i8*, i8** %17, align 8
  call void %14(i32 noundef %15, i8* noundef %18)
  ret void
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal noundef i32 @_ZL12npf_utoa_revmPchc(i64 noundef %0, i8* noundef %1, i8 noundef zeroext %2, i8 noundef signext %3) #1 {
  %5 = alloca i64, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8, align 1
  %8 = alloca i8, align 1
  %9 = alloca i8, align 1
  %10 = alloca i8, align 1
  store i64 %0, i64* %5, align 8
  store i8* %1, i8** %6, align 8
  store i8 %2, i8* %7, align 1
  store i8 %3, i8* %8, align 1
  store i8 0, i8* %9, align 1
  br label %11

11:                                               ; preds = %39, %4
  %12 = load i64, i64* %5, align 8
  %13 = load i8, i8* %7, align 1
  %14 = zext i8 %13 to i64
  %15 = urem i64 %12, %14
  %16 = trunc i64 %15 to i8
  store i8 %16, i8* %10, align 1
  %17 = load i8, i8* %10, align 1
  %18 = sext i8 %17 to i32
  %19 = icmp slt i32 %18, 10
  br i1 %19, label %20, label %21

20:                                               ; preds = %11
  br label %25

21:                                               ; preds = %11
  %22 = load i8, i8* %8, align 1
  %23 = sext i8 %22 to i32
  %24 = add nsw i32 55, %23
  br label %25

25:                                               ; preds = %21, %20
  %26 = phi i32 [ 48, %20 ], [ %24, %21 ]
  %27 = load i8, i8* %10, align 1
  %28 = sext i8 %27 to i32
  %29 = add nsw i32 %26, %28
  %30 = trunc i32 %29 to i8
  %31 = load i8*, i8** %6, align 8
  %32 = getelementptr inbounds i8, i8* %31, i32 1
  store i8* %32, i8** %6, align 8
  store i8 %30, i8* %31, align 1
  %33 = load i8, i8* %9, align 1
  %34 = add i8 %33, 1
  store i8 %34, i8* %9, align 1
  %35 = load i8, i8* %7, align 1
  %36 = zext i8 %35 to i64
  %37 = load i64, i64* %5, align 8
  %38 = udiv i64 %37, %36
  store i64 %38, i64* %5, align 8
  br label %39

39:                                               ; preds = %25
  %40 = load i64, i64* %5, align 8
  %41 = icmp ne i64 %40, 0
  br i1 %41, label %11, label %42, !llvm.loop !21

42:                                               ; preds = %39
  %43 = load i8, i8* %9, align 1
  %44 = zext i8 %43 to i32
  ret i32 %44
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal noundef i32 @_ZL11npf_bin_lenm(i64 noundef %0) #1 {
  %2 = alloca i32, align 4
  %3 = alloca i64, align 8
  store i64 %0, i64* %3, align 8
  %4 = load i64, i64* %3, align 8
  %5 = icmp ne i64 %4, 0
  br i1 %5, label %7, label %6

6:                                                ; preds = %1
  store i32 1, i32* %2, align 4
  br label %14

7:                                                ; preds = %1
  %8 = load i64, i64* %3, align 8
  %9 = call i64 @llvm.ctlz.i64(i64 %8, i1 false)
  %10 = trunc i64 %9 to i32
  %11 = sext i32 %10 to i64
  %12 = sub i64 64, %11
  %13 = trunc i64 %12 to i32
  store i32 %13, i32* %2, align 4
  br label %14

14:                                               ; preds = %7, %6
  %15 = load i32, i32* %2, align 4
  ret i32 %15
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal noundef i32 @_ZL12npf_ftoa_revPcPK15npf_format_specd(i8* noundef %0, %struct.npf_format_spec* noundef %1, double noundef %2) #1 {
  %4 = alloca i32, align 4
  %5 = alloca i8*, align 8
  %6 = alloca %struct.npf_format_spec*, align 8
  %7 = alloca double, align 8
  %8 = alloca i8*, align 8
  %9 = alloca i64, align 8
  %10 = alloca i8*, align 8
  %11 = alloca i8*, align 8
  %12 = alloca i8, align 1
  %13 = alloca i16, align 2
  %14 = alloca i8, align 1
  %15 = alloca i8, align 1
  %16 = alloca i8, align 1
  %17 = alloca i32, align 4
  %18 = alloca i8, align 1
  %19 = alloca i16, align 2
  %20 = alloca i32, align 4
  %21 = alloca i8, align 1
  %22 = alloca i8, align 1
  %23 = alloca i16, align 2
  %24 = alloca i64, align 8
  %25 = alloca i8, align 1
  %26 = alloca i8, align 1
  store i8* %0, i8** %5, align 8
  store %struct.npf_format_spec* %1, %struct.npf_format_spec** %6, align 8
  store double %2, double* %7, align 8
  store i8* null, i8** %8, align 8
  %27 = bitcast double* %7 to i8*
  store i8* %27, i8** %10, align 8
  %28 = bitcast i64* %9 to i8*
  store i8* %28, i8** %11, align 8
  store i8 0, i8* %12, align 1
  br label %29

29:                                               ; preds = %43, %3
  %30 = load i8, i8* %12, align 1
  %31 = zext i8 %30 to i64
  %32 = icmp ult i64 %31, 8
  br i1 %32, label %33, label %46

33:                                               ; preds = %29
  %34 = load i8*, i8** %10, align 8
  %35 = load i8, i8* %12, align 1
  %36 = zext i8 %35 to i64
  %37 = getelementptr inbounds i8, i8* %34, i64 %36
  %38 = load i8, i8* %37, align 1
  %39 = load i8*, i8** %11, align 8
  %40 = load i8, i8* %12, align 1
  %41 = zext i8 %40 to i64
  %42 = getelementptr inbounds i8, i8* %39, i64 %41
  store i8 %38, i8* %42, align 1
  br label %43

43:                                               ; preds = %33
  %44 = load i8, i8* %12, align 1
  %45 = add i8 %44, 1
  store i8 %45, i8* %12, align 1
  br label %29, !llvm.loop !22

46:                                               ; preds = %29
  %47 = load i64, i64* %9, align 8
  %48 = lshr i64 %47, 52
  %49 = trunc i64 %48 to i16
  %50 = sext i16 %49 to i32
  %51 = and i32 %50, 2047
  %52 = trunc i32 %51 to i16
  store i16 %52, i16* %13, align 2
  %53 = load i64, i64* %9, align 8
  %54 = and i64 %53, 4503599627370495
  store i64 %54, i64* %9, align 8
  %55 = load i16, i16* %13, align 2
  %56 = sext i16 %55 to i32
  %57 = icmp eq i32 %56, 2047
  br i1 %57, label %58, label %66

58:                                               ; preds = %46
  %59 = load i64, i64* %9, align 8
  %60 = icmp ne i64 %59, 0
  br i1 %60, label %61, label %62

61:                                               ; preds = %58
  br label %63

62:                                               ; preds = %58
  br label %63

63:                                               ; preds = %62, %61
  %64 = phi [4 x i8]* [ @.str, %61 ], [ @.str.1, %62 ]
  %65 = getelementptr inbounds [4 x i8], [4 x i8]* %64, i64 0, i64 0
  store i8* %65, i8** %8, align 8
  br label %414

66:                                               ; preds = %46
  %67 = load %struct.npf_format_spec*, %struct.npf_format_spec** %6, align 8
  %68 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %67, i32 0, i32 7
  %69 = load i32, i32* %68, align 4
  %70 = icmp sgt i32 %69, 21
  br i1 %70, label %71, label %72

71:                                               ; preds = %66
  br label %414

72:                                               ; preds = %66
  %73 = load i16, i16* %13, align 2
  %74 = icmp ne i16 %73, 0
  br i1 %74, label %75, label %78

75:                                               ; preds = %72
  %76 = load i64, i64* %9, align 8
  %77 = or i64 %76, 4503599627370496
  store i64 %77, i64* %9, align 8
  br label %81

78:                                               ; preds = %72
  %79 = load i16, i16* %13, align 2
  %80 = add i16 %79, 1
  store i16 %80, i16* %13, align 2
  br label %81

81:                                               ; preds = %78, %75
  %82 = load i16, i16* %13, align 2
  %83 = sext i16 %82 to i32
  %84 = sub nsw i32 %83, 1023
  %85 = trunc i32 %84 to i16
  store i16 %85, i16* %13, align 2
  store i8 0, i8* %14, align 1
  %86 = load %struct.npf_format_spec*, %struct.npf_format_spec** %6, align 8
  %87 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %86, i32 0, i32 7
  %88 = load i32, i32* %87, align 4
  %89 = trunc i32 %88 to i8
  store i8 %89, i8* %16, align 1
  %90 = load i8, i8* %16, align 1
  %91 = icmp ne i8 %90, 0
  br i1 %91, label %97, label %92

92:                                               ; preds = %81
  %93 = load %struct.npf_format_spec*, %struct.npf_format_spec** %6, align 8
  %94 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %93, i32 0, i32 1
  %95 = load i8, i8* %94, align 1
  %96 = icmp ne i8 %95, 0
  br i1 %96, label %97, label %103

97:                                               ; preds = %92, %81
  %98 = load i8*, i8** %5, align 8
  %99 = load i8, i8* %16, align 1
  %100 = add i8 %99, 1
  store i8 %100, i8* %16, align 1
  %101 = zext i8 %99 to i64
  %102 = getelementptr inbounds i8, i8* %98, i64 %101
  store i8 46, i8* %102, align 1
  br label %103

103:                                              ; preds = %97, %92
  %104 = load i16, i16* %13, align 2
  %105 = sext i16 %104 to i32
  %106 = icmp sge i32 %105, 0
  br i1 %106, label %107, label %191

107:                                              ; preds = %103
  %108 = load i16, i16* %13, align 2
  %109 = sext i16 %108 to i32
  %110 = icmp sgt i32 %109, 31
  br i1 %110, label %111, label %112

111:                                              ; preds = %107
  br label %115

112:                                              ; preds = %107
  %113 = load i16, i16* %13, align 2
  %114 = sext i16 %113 to i32
  br label %115

115:                                              ; preds = %112, %111
  %116 = phi i32 [ 31, %111 ], [ %114, %112 ]
  %117 = trunc i32 %116 to i8
  store i8 %117, i8* %18, align 1
  %118 = load i16, i16* %13, align 2
  %119 = sext i16 %118 to i32
  %120 = load i8, i8* %18, align 1
  %121 = sext i8 %120 to i32
  %122 = sub nsw i32 %119, %121
  %123 = trunc i32 %122 to i16
  store i16 %123, i16* %19, align 2
  %124 = load i8, i8* %18, align 1
  %125 = sext i8 %124 to i32
  %126 = sub nsw i32 52, %125
  %127 = trunc i32 %126 to i8
  store i8 %127, i8* %18, align 1
  %128 = load i64, i64* %9, align 8
  %129 = load i8, i8* %18, align 1
  %130 = sext i8 %129 to i32
  %131 = zext i32 %130 to i64
  %132 = lshr i64 %128, %131
  %133 = trunc i64 %132 to i32
  store i32 %133, i32* %17, align 4
  %134 = load i16, i16* %19, align 2
  %135 = icmp ne i16 %134, 0
  br i1 %135, label %136, label %149

136:                                              ; preds = %115
  %137 = load i8, i8* %18, align 1
  %138 = icmp ne i8 %137, 0
  br i1 %138, label %139, label %148

139:                                              ; preds = %136
  %140 = load i64, i64* %9, align 8
  %141 = load i8, i8* %18, align 1
  %142 = sext i8 %141 to i32
  %143 = sub nsw i32 %142, 1
  %144 = zext i32 %143 to i64
  %145 = lshr i64 %140, %144
  %146 = and i64 %145, 1
  %147 = trunc i64 %146 to i8
  store i8 %147, i8* %14, align 1
  br label %148

148:                                              ; preds = %139, %136
  store i16 52, i16* %13, align 2
  br label %149

149:                                              ; preds = %148, %115
  br label %150

150:                                              ; preds = %187, %149
  %151 = load i16, i16* %19, align 2
  %152 = icmp ne i16 %151, 0
  br i1 %152, label %153, label %190

153:                                              ; preds = %150
  %154 = load i32, i32* %17, align 4
  %155 = and i32 %154, -2147483648
  %156 = icmp ne i32 %155, 0
  br i1 %156, label %164, label %157

157:                                              ; preds = %153
  %158 = load i32, i32* %17, align 4
  %159 = shl i32 %158, 1
  store i32 %159, i32* %17, align 4
  %160 = load i32, i32* %17, align 4
  %161 = load i8, i8* %14, align 1
  %162 = zext i8 %161 to i32
  %163 = or i32 %160, %162
  store i32 %163, i32* %17, align 4
  store i8 0, i8* %14, align 1
  br label %186

164:                                              ; preds = %153
  %165 = load i8, i8* %16, align 1
  %166 = zext i8 %165 to i32
  %167 = icmp sge i32 %166, 23
  br i1 %167, label %168, label %169

168:                                              ; preds = %164
  br label %414

169:                                              ; preds = %164
  %170 = load i8*, i8** %5, align 8
  %171 = load i8, i8* %16, align 1
  %172 = add i8 %171, 1
  store i8 %172, i8* %16, align 1
  %173 = zext i8 %171 to i64
  %174 = getelementptr inbounds i8, i8* %170, i64 %173
  store i8 48, i8* %174, align 1
  %175 = load i32, i32* %17, align 4
  %176 = urem i32 %175, 5
  %177 = trunc i32 %176 to i8
  %178 = zext i8 %177 to i32
  %179 = load i8, i8* %14, align 1
  %180 = zext i8 %179 to i32
  %181 = add nsw i32 %178, %180
  %182 = icmp sgt i32 %181, 2
  %183 = zext i1 %182 to i8
  store i8 %183, i8* %14, align 1
  %184 = load i32, i32* %17, align 4
  %185 = udiv i32 %184, 5
  store i32 %185, i32* %17, align 4
  br label %186

186:                                              ; preds = %169, %157
  br label %187

187:                                              ; preds = %186
  %188 = load i16, i16* %19, align 2
  %189 = add i16 %188, -1
  store i16 %189, i16* %19, align 2
  br label %150, !llvm.loop !23

190:                                              ; preds = %150
  br label %192

191:                                              ; preds = %103
  store i32 0, i32* %17, align 4
  br label %192

192:                                              ; preds = %191, %190
  %193 = load i8, i8* %16, align 1
  store i8 %193, i8* %15, align 1
  br label %194

194:                                              ; preds = %213, %192
  %195 = load i8, i8* %15, align 1
  %196 = zext i8 %195 to i32
  %197 = icmp sge i32 %196, 23
  br i1 %197, label %198, label %199

198:                                              ; preds = %194
  br label %414

199:                                              ; preds = %194
  %200 = load i32, i32* %17, align 4
  %201 = urem i32 %200, 10
  %202 = trunc i32 %201 to i8
  %203 = sext i8 %202 to i32
  %204 = add nsw i32 48, %203
  %205 = trunc i32 %204 to i8
  %206 = load i8*, i8** %5, align 8
  %207 = load i8, i8* %15, align 1
  %208 = add i8 %207, 1
  store i8 %208, i8* %15, align 1
  %209 = zext i8 %207 to i64
  %210 = getelementptr inbounds i8, i8* %206, i64 %209
  store i8 %205, i8* %210, align 1
  %211 = load i32, i32* %17, align 4
  %212 = udiv i32 %211, 10
  store i32 %212, i32* %17, align 4
  br label %213

213:                                              ; preds = %199
  %214 = load i32, i32* %17, align 4
  %215 = icmp ne i32 %214, 0
  br i1 %215, label %194, label %216, !llvm.loop !24

216:                                              ; preds = %213
  %217 = load %struct.npf_format_spec*, %struct.npf_format_spec** %6, align 8
  %218 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %217, i32 0, i32 7
  %219 = load i32, i32* %218, align 4
  %220 = trunc i32 %219 to i8
  store i8 %220, i8* %21, align 1
  %221 = load i16, i16* %13, align 2
  %222 = sext i16 %221 to i32
  %223 = icmp slt i32 %222, 52
  br i1 %223, label %224, label %310

224:                                              ; preds = %216
  %225 = load i16, i16* %13, align 2
  %226 = sext i16 %225 to i32
  %227 = icmp slt i32 %226, 0
  br i1 %227, label %228, label %229

228:                                              ; preds = %224
  br label %232

229:                                              ; preds = %224
  %230 = load i16, i16* %13, align 2
  %231 = sext i16 %230 to i32
  br label %232

232:                                              ; preds = %229, %228
  %233 = phi i32 [ -1, %228 ], [ %231, %229 ]
  %234 = trunc i32 %233 to i8
  store i8 %234, i8* %22, align 1
  %235 = load i16, i16* %13, align 2
  %236 = sext i16 %235 to i32
  %237 = load i8, i8* %22, align 1
  %238 = sext i8 %237 to i32
  %239 = sub nsw i32 %236, %238
  %240 = trunc i32 %239 to i16
  store i16 %240, i16* %23, align 2
  %241 = load i64, i64* %9, align 8
  %242 = load i8, i8* %22, align 1
  %243 = sext i8 %242 to i32
  %244 = add nsw i32 12, %243
  %245 = zext i32 %244 to i64
  %246 = shl i64 %241, %245
  store i64 %246, i64* %24, align 8
  %247 = load i64, i64* %24, align 8
  %248 = lshr i64 %247, 32
  %249 = trunc i64 %248 to i32
  store i32 %249, i32* %20, align 4
  %250 = load i64, i64* %24, align 8
  %251 = lshr i64 %250, 31
  %252 = and i64 %251, 1
  %253 = trunc i64 %252 to i8
  store i8 %253, i8* %14, align 1
  store i8 0, i8* %25, align 1
  br label %254

254:                                              ; preds = %298, %232
  %255 = load i8, i8* %21, align 1
  %256 = icmp ne i8 %255, 0
  br i1 %256, label %257, label %261

257:                                              ; preds = %254
  %258 = load i16, i16* %23, align 2
  %259 = sext i16 %258 to i32
  %260 = icmp slt i32 %259, 4
  br label %261

261:                                              ; preds = %257, %254
  %262 = phi i1 [ false, %254 ], [ %260, %257 ]
  br i1 %262, label %263, label %301

263:                                              ; preds = %261
  %264 = load i32, i32* %20, align 4
  %265 = icmp ugt i32 %264, 858993458
  br i1 %265, label %269, label %266

266:                                              ; preds = %263
  %267 = load i8, i8* %25, align 1
  %268 = icmp ne i8 %267, 0
  br i1 %268, label %269, label %275

269:                                              ; preds = %266, %263
  %270 = load i32, i32* %20, align 4
  %271 = and i32 %270, 1
  %272 = trunc i32 %271 to i8
  store i8 %272, i8* %14, align 1
  %273 = load i32, i32* %20, align 4
  %274 = lshr i32 %273, 1
  store i32 %274, i32* %20, align 4
  br label %297

275:                                              ; preds = %266
  %276 = load i32, i32* %20, align 4
  %277 = mul i32 %276, 5
  store i32 %277, i32* %20, align 4
  %278 = load i8, i8* %14, align 1
  %279 = icmp ne i8 %278, 0
  br i1 %279, label %280, label %283

280:                                              ; preds = %275
  %281 = load i32, i32* %20, align 4
  %282 = add i32 %281, 3
  store i32 %282, i32* %20, align 4
  store i8 0, i8* %14, align 1
  br label %283

283:                                              ; preds = %280, %275
  %284 = load i16, i16* %23, align 2
  %285 = sext i16 %284 to i32
  %286 = icmp slt i32 %285, 0
  br i1 %286, label %287, label %293

287:                                              ; preds = %283
  %288 = load i8*, i8** %5, align 8
  %289 = load i8, i8* %21, align 1
  %290 = add i8 %289, -1
  store i8 %290, i8* %21, align 1
  %291 = zext i8 %290 to i64
  %292 = getelementptr inbounds i8, i8* %288, i64 %291
  store i8 48, i8* %292, align 1
  br label %296

293:                                              ; preds = %283
  %294 = load i8, i8* %25, align 1
  %295 = add i8 %294, 1
  store i8 %295, i8* %25, align 1
  br label %296

296:                                              ; preds = %293, %287
  br label %297

297:                                              ; preds = %296, %269
  br label %298

298:                                              ; preds = %297
  %299 = load i16, i16* %23, align 2
  %300 = add i16 %299, 1
  store i16 %300, i16* %23, align 2
  br label %254, !llvm.loop !25

301:                                              ; preds = %261
  %302 = load i32, i32* %20, align 4
  %303 = load i8, i8* %14, align 1
  %304 = zext i8 %303 to i32
  %305 = add i32 %302, %304
  store i32 %305, i32* %20, align 4
  %306 = load i16, i16* %23, align 2
  %307 = sext i16 %306 to i32
  %308 = icmp sge i32 %307, 0
  %309 = zext i1 %308 to i8
  store i8 %309, i8* %14, align 1
  store i8 0, i8* %16, align 1
  br label %311

310:                                              ; preds = %216
  store i32 0, i32* %20, align 4
  br label %311

311:                                              ; preds = %310, %301
  %312 = load i8, i8* %21, align 1
  %313 = icmp ne i8 %312, 0
  br i1 %313, label %314, label %338

314:                                              ; preds = %311
  br label %315

315:                                              ; preds = %332, %314
  %316 = load i32, i32* %20, align 4
  %317 = lshr i32 %316, 28
  %318 = trunc i32 %317 to i8
  %319 = sext i8 %318 to i32
  %320 = add nsw i32 48, %319
  %321 = trunc i32 %320 to i8
  %322 = load i8*, i8** %5, align 8
  %323 = load i8, i8* %21, align 1
  %324 = add i8 %323, -1
  store i8 %324, i8* %21, align 1
  %325 = zext i8 %324 to i64
  %326 = getelementptr inbounds i8, i8* %322, i64 %325
  store i8 %321, i8* %326, align 1
  %327 = load i32, i32* %20, align 4
  %328 = and i32 %327, 268435455
  store i32 %328, i32* %20, align 4
  %329 = load i8, i8* %21, align 1
  %330 = icmp ne i8 %329, 0
  br i1 %330, label %332, label %331

331:                                              ; preds = %315
  br label %335

332:                                              ; preds = %315
  %333 = load i32, i32* %20, align 4
  %334 = mul i32 %333, 10
  store i32 %334, i32* %20, align 4
  br label %315, !llvm.loop !26

335:                                              ; preds = %331
  %336 = load i32, i32* %20, align 4
  %337 = shl i32 %336, 4
  store i32 %337, i32* %20, align 4
  br label %338

338:                                              ; preds = %335, %311
  %339 = load i16, i16* %13, align 2
  %340 = sext i16 %339 to i32
  %341 = icmp slt i32 %340, 52
  br i1 %341, label %342, label %351

342:                                              ; preds = %338
  %343 = load i32, i32* %20, align 4
  %344 = lshr i32 %343, 31
  %345 = trunc i32 %344 to i8
  %346 = zext i8 %345 to i32
  %347 = load i8, i8* %14, align 1
  %348 = zext i8 %347 to i32
  %349 = and i32 %348, %346
  %350 = trunc i32 %349 to i8
  store i8 %350, i8* %14, align 1
  br label %351

351:                                              ; preds = %342, %338
  br label %352

352:                                              ; preds = %408, %351
  %353 = load i8, i8* %14, align 1
  %354 = icmp ne i8 %353, 0
  br i1 %354, label %355, label %411

355:                                              ; preds = %352
  %356 = load i8, i8* %16, align 1
  %357 = zext i8 %356 to i32
  %358 = icmp sge i32 %357, 23
  br i1 %358, label %359, label %360

359:                                              ; preds = %355
  br label %414

360:                                              ; preds = %355
  %361 = load i8, i8* %16, align 1
  %362 = zext i8 %361 to i32
  %363 = load i8, i8* %15, align 1
  %364 = zext i8 %363 to i32
  %365 = icmp sge i32 %362, %364
  br i1 %365, label %366, label %372

366:                                              ; preds = %360
  %367 = load i8*, i8** %5, align 8
  %368 = load i8, i8* %15, align 1
  %369 = add i8 %368, 1
  store i8 %369, i8* %15, align 1
  %370 = zext i8 %368 to i64
  %371 = getelementptr inbounds i8, i8* %367, i64 %370
  store i8 48, i8* %371, align 1
  br label %372

372:                                              ; preds = %366, %360
  %373 = load i8*, i8** %5, align 8
  %374 = load i8, i8* %16, align 1
  %375 = zext i8 %374 to i64
  %376 = getelementptr inbounds i8, i8* %373, i64 %375
  %377 = load i8, i8* %376, align 1
  %378 = sext i8 %377 to i32
  %379 = icmp eq i32 %378, 46
  br i1 %379, label %380, label %381

380:                                              ; preds = %372
  br label %408

381:                                              ; preds = %372
  %382 = load i8*, i8** %5, align 8
  %383 = load i8, i8* %16, align 1
  %384 = zext i8 %383 to i64
  %385 = getelementptr inbounds i8, i8* %382, i64 %384
  %386 = load i8, i8* %385, align 1
  %387 = sext i8 %386 to i32
  %388 = icmp eq i32 %387, 57
  %389 = zext i1 %388 to i8
  store i8 %389, i8* %14, align 1
  %390 = load i8, i8* %14, align 1
  %391 = icmp ne i8 %390, 0
  br i1 %391, label %392, label %393

392:                                              ; preds = %381
  br label %401

393:                                              ; preds = %381
  %394 = load i8*, i8** %5, align 8
  %395 = load i8, i8* %16, align 1
  %396 = zext i8 %395 to i64
  %397 = getelementptr inbounds i8, i8* %394, i64 %396
  %398 = load i8, i8* %397, align 1
  %399 = sext i8 %398 to i32
  %400 = add nsw i32 %399, 1
  br label %401

401:                                              ; preds = %393, %392
  %402 = phi i32 [ 48, %392 ], [ %400, %393 ]
  %403 = trunc i32 %402 to i8
  %404 = load i8*, i8** %5, align 8
  %405 = load i8, i8* %16, align 1
  %406 = zext i8 %405 to i64
  %407 = getelementptr inbounds i8, i8* %404, i64 %406
  store i8 %403, i8* %407, align 1
  br label %408

408:                                              ; preds = %401, %380
  %409 = load i8, i8* %16, align 1
  %410 = add i8 %409, 1
  store i8 %410, i8* %16, align 1
  br label %352, !llvm.loop !27

411:                                              ; preds = %352
  %412 = load i8, i8* %15, align 1
  %413 = zext i8 %412 to i32
  store i32 %413, i32* %4, align 4
  br label %449

414:                                              ; preds = %359, %198, %168, %71, %63
  %415 = load i8*, i8** %8, align 8
  %416 = icmp ne i8* %415, null
  br i1 %416, label %418, label %417

417:                                              ; preds = %414
  store i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2, i64 0, i64 0), i8** %8, align 8
  br label %418

418:                                              ; preds = %417, %414
  store i8 0, i8* %26, align 1
  br label %419

419:                                              ; preds = %443, %418
  %420 = load i8*, i8** %8, align 8
  %421 = load i8, i8* %26, align 1
  %422 = zext i8 %421 to i64
  %423 = getelementptr inbounds i8, i8* %420, i64 %422
  %424 = load i8, i8* %423, align 1
  %425 = icmp ne i8 %424, 0
  br i1 %425, label %426, label %446

426:                                              ; preds = %419
  %427 = load i8*, i8** %8, align 8
  %428 = load i8, i8* %26, align 1
  %429 = zext i8 %428 to i64
  %430 = getelementptr inbounds i8, i8* %427, i64 %429
  %431 = load i8, i8* %430, align 1
  %432 = sext i8 %431 to i32
  %433 = load %struct.npf_format_spec*, %struct.npf_format_spec** %6, align 8
  %434 = getelementptr inbounds %struct.npf_format_spec, %struct.npf_format_spec* %433, i32 0, i32 10
  %435 = load i8, i8* %434, align 4
  %436 = sext i8 %435 to i32
  %437 = add nsw i32 %432, %436
  %438 = trunc i32 %437 to i8
  %439 = load i8*, i8** %5, align 8
  %440 = load i8, i8* %26, align 1
  %441 = zext i8 %440 to i64
  %442 = getelementptr inbounds i8, i8* %439, i64 %441
  store i8 %438, i8* %442, align 1
  br label %443

443:                                              ; preds = %426
  %444 = load i8, i8* %26, align 1
  %445 = add i8 %444, 1
  store i8 %445, i8* %26, align 1
  br label %419, !llvm.loop !28

446:                                              ; preds = %419
  %447 = load i8, i8* %26, align 1
  %448 = zext i8 %447 to i32
  store i32 %448, i32* %4, align 4
  br label %449

449:                                              ; preds = %446, %411
  %450 = load i32, i32* %4, align 4
  ret i32 %450
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal noundef i32 @_ZL7npf_maxii(i32 noundef %0, i32 noundef %1) #1 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %5 = load i32, i32* %3, align 4
  %6 = load i32, i32* %4, align 4
  %7 = icmp sgt i32 %5, %6
  br i1 %7, label %8, label %10

8:                                                ; preds = %2
  %9 = load i32, i32* %3, align 4
  br label %12

10:                                               ; preds = %2
  %11 = load i32, i32* %4, align 4
  br label %12

12:                                               ; preds = %10, %8
  %13 = phi i32 [ %9, %8 ], [ %11, %10 ]
  ret i32 %13
}

; Function Attrs: mustprogress noinline optnone ssp uwtable
define i32 @npf_pprintf(void (i32, i8*)* noundef %0, i8* noundef %1, i8* noundef %2, ...) #0 {
  %4 = alloca void (i32, i8*)*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i32, align 4
  store void (i32, i8*)* %0, void (i32, i8*)** %4, align 8
  store i8* %1, i8** %5, align 8
  store i8* %2, i8** %6, align 8
  %9 = bitcast i8** %7 to i8*
  call void @llvm.va_start(i8* %9)
  %10 = load void (i32, i8*)*, void (i32, i8*)** %4, align 8
  %11 = load i8*, i8** %5, align 8
  %12 = load i8*, i8** %6, align 8
  %13 = load i8*, i8** %7, align 8
  %14 = call i32 @npf_vpprintf(void (i32, i8*)* noundef %10, i8* noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_start(i8*) #2

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_end(i8*) #2

; Function Attrs: mustprogress noinline optnone ssp uwtable
define i32 @npf_snprintf(i8* noundef %0, i64 noundef %1, i8* noundef %2, ...) #0 {
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
  %14 = call i32 @npf_vsnprintf(i8* noundef %10, i64 noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: mustprogress noinline optnone ssp uwtable
define i32 @npf_vsnprintf(i8* noundef %0, i64 noundef %1, i8* noundef %2, i8* noundef %3) #0 {
  %5 = alloca i8*, align 8
  %6 = alloca i64, align 8
  %7 = alloca i8*, align 8
  %8 = alloca i8*, align 8
  %9 = alloca %struct.npf_bufputc_ctx, align 8
  %10 = alloca void (i32, i8*)*, align 8
  %11 = alloca i32, align 4
  store i8* %0, i8** %5, align 8
  store i64 %1, i64* %6, align 8
  store i8* %2, i8** %7, align 8
  store i8* %3, i8** %8, align 8
  %12 = load i8*, i8** %5, align 8
  %13 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %9, i32 0, i32 0
  store i8* %12, i8** %13, align 8
  %14 = load i64, i64* %6, align 8
  %15 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %9, i32 0, i32 1
  store i64 %14, i64* %15, align 8
  %16 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %9, i32 0, i32 2
  store i64 0, i64* %16, align 8
  %17 = load i8*, i8** %5, align 8
  %18 = icmp ne i8* %17, null
  br i1 %18, label %19, label %20

19:                                               ; preds = %4
  br label %21

20:                                               ; preds = %4
  br label %21

21:                                               ; preds = %20, %19
  %22 = phi void (i32, i8*)* [ @_ZL11npf_bufputciPv, %19 ], [ @_ZL15npf_bufputc_nopiPv, %20 ]
  store void (i32, i8*)* %22, void (i32, i8*)** %10, align 8
  %23 = load void (i32, i8*)*, void (i32, i8*)** %10, align 8
  %24 = bitcast %struct.npf_bufputc_ctx* %9 to i8*
  %25 = load i8*, i8** %7, align 8
  %26 = load i8*, i8** %8, align 8
  %27 = call i32 @npf_vpprintf(void (i32, i8*)* noundef %23, i8* noundef %24, i8* noundef %25, i8* noundef %26)
  store i32 %27, i32* %11, align 4
  %28 = load void (i32, i8*)*, void (i32, i8*)** %10, align 8
  %29 = bitcast %struct.npf_bufputc_ctx* %9 to i8*
  call void %28(i32 noundef 0, i8* noundef %29)
  %30 = load i8*, i8** %5, align 8
  %31 = icmp ne i8* %30, null
  br i1 %31, label %32, label %40

32:                                               ; preds = %21
  %33 = load i64, i64* %6, align 8
  %34 = icmp ne i64 %33, 0
  br i1 %34, label %35, label %40

35:                                               ; preds = %32
  %36 = load i8*, i8** %5, align 8
  %37 = load i64, i64* %6, align 8
  %38 = sub i64 %37, 1
  %39 = getelementptr inbounds i8, i8* %36, i64 %38
  store i8 0, i8* %39, align 1
  br label %40

40:                                               ; preds = %35, %32, %21
  %41 = load i32, i32* %11, align 4
  ret i32 %41
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal void @_ZL11npf_bufputciPv(i32 noundef %0, i8* noundef %1) #1 {
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 8
  %5 = alloca %struct.npf_bufputc_ctx*, align 8
  store i32 %0, i32* %3, align 4
  store i8* %1, i8** %4, align 8
  %6 = load i8*, i8** %4, align 8
  %7 = bitcast i8* %6 to %struct.npf_bufputc_ctx*
  store %struct.npf_bufputc_ctx* %7, %struct.npf_bufputc_ctx** %5, align 8
  %8 = load %struct.npf_bufputc_ctx*, %struct.npf_bufputc_ctx** %5, align 8
  %9 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %8, i32 0, i32 2
  %10 = load i64, i64* %9, align 8
  %11 = load %struct.npf_bufputc_ctx*, %struct.npf_bufputc_ctx** %5, align 8
  %12 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %11, i32 0, i32 1
  %13 = load i64, i64* %12, align 8
  %14 = icmp ult i64 %10, %13
  br i1 %14, label %15, label %26

15:                                               ; preds = %2
  %16 = load i32, i32* %3, align 4
  %17 = trunc i32 %16 to i8
  %18 = load %struct.npf_bufputc_ctx*, %struct.npf_bufputc_ctx** %5, align 8
  %19 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %18, i32 0, i32 0
  %20 = load i8*, i8** %19, align 8
  %21 = load %struct.npf_bufputc_ctx*, %struct.npf_bufputc_ctx** %5, align 8
  %22 = getelementptr inbounds %struct.npf_bufputc_ctx, %struct.npf_bufputc_ctx* %21, i32 0, i32 2
  %23 = load i64, i64* %22, align 8
  %24 = add i64 %23, 1
  store i64 %24, i64* %22, align 8
  %25 = getelementptr inbounds i8, i8* %20, i64 %23
  store i8 %17, i8* %25, align 1
  br label %26

26:                                               ; preds = %15, %2
  ret void
}

; Function Attrs: mustprogress noinline nounwind optnone ssp uwtable
define internal void @_ZL15npf_bufputc_nopiPv(i32 noundef %0, i8* noundef %1) #1 {
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 8
  store i32 %0, i32* %3, align 4
  store i8* %1, i8** %4, align 8
  ret void
}

; Function Attrs: mustprogress noinline optnone ssp uwtable
define noundef i32 @_Z21your_project_snprintfPcmPKcz(i8* noundef %0, i64 noundef %1, i8* noundef %2, ...) #0 {
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
  %14 = call i32 @npf_vsnprintf(i8* noundef %10, i64 noundef %11, i8* noundef %12, i8* noundef %13)
  store i32 %14, i32* %8, align 4
  %15 = bitcast i8** %7 to i8*
  call void @llvm.va_end(i8* %15)
  %16 = load i32, i32* %8, align 4
  ret i32 %16
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #3

attributes #0 = { mustprogress noinline optnone ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
attributes #1 = { mustprogress noinline nounwind optnone ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.5a,+zcm,+zcz" }
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
