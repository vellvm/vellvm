; ModuleID = 'variable_arrays.c'
source_filename = "variable_arrays.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nosync nounwind sspstrong uwtable writeonly
define void @use_arrays(i32 noundef %0, i32 noundef %1, i32* nocapture noundef writeonly %2) local_unnamed_addr #0 {
  %4 = mul i32 %0, %0
  %5 = zext i32 %4 to i64
  %6 = zext i32 %1 to i64
  %7 = icmp sgt i32 %4, 0
  %8 = icmp sgt i32 %1, 0
  %9 = mul nuw i64 %5, %6
  br i1 %7, label %10, label %175

10:                                               ; preds = %3
  %11 = and i64 %6, 4294967288
  %12 = add nsw i64 %11, -8
  %13 = lshr exact i64 %12, 3
  %14 = add nuw nsw i64 %13, 1
  %15 = icmp ult i32 %1, 8
  %16 = and i64 %6, 4294967288
  %17 = trunc i64 %16 to i32
  %18 = and i64 %14, 3
  %19 = icmp ult i64 %12, 24
  %20 = and i64 %14, 4611686018427387900
  %21 = icmp eq i64 %18, 0
  %22 = icmp eq i64 %16, %6
  br label %23

23:                                               ; preds = %10, %176
  %24 = phi i64 [ %178, %176 ], [ 0, %10 ]
  %25 = phi i32 [ %177, %176 ], [ 1, %10 ]
  br i1 %8, label %26, label %176

26:                                               ; preds = %23
  %27 = mul nuw nsw i64 %24, %6
  %28 = getelementptr i32, i32* %2, i64 %27
  br i1 %15, label %85, label %29

29:                                               ; preds = %26
  %30 = add i32 %25, %17
  %31 = insertelement <4 x i32> poison, i32 %25, i64 0
  %32 = shufflevector <4 x i32> %31, <4 x i32> poison, <4 x i32> zeroinitializer
  %33 = add <4 x i32> %32, <i32 0, i32 1, i32 2, i32 3>
  br i1 %19, label %68, label %34

34:                                               ; preds = %29, %34
  %35 = phi i64 [ %64, %34 ], [ 0, %29 ]
  %36 = phi <4 x i32> [ %65, %34 ], [ %33, %29 ]
  %37 = phi i64 [ %66, %34 ], [ 0, %29 ]
  %38 = add <4 x i32> %36, <i32 4, i32 4, i32 4, i32 4>
  %39 = getelementptr i32, i32* %28, i64 %35
  %40 = bitcast i32* %39 to <4 x i32>*
  store <4 x i32> %36, <4 x i32>* %40, align 4, !tbaa !5
  %41 = getelementptr i32, i32* %39, i64 4
  %42 = bitcast i32* %41 to <4 x i32>*
  store <4 x i32> %38, <4 x i32>* %42, align 4, !tbaa !5
  %43 = or i64 %35, 8
  %44 = add <4 x i32> %36, <i32 8, i32 8, i32 8, i32 8>
  %45 = add <4 x i32> %36, <i32 12, i32 12, i32 12, i32 12>
  %46 = getelementptr i32, i32* %28, i64 %43
  %47 = bitcast i32* %46 to <4 x i32>*
  store <4 x i32> %44, <4 x i32>* %47, align 4, !tbaa !5
  %48 = getelementptr i32, i32* %46, i64 4
  %49 = bitcast i32* %48 to <4 x i32>*
  store <4 x i32> %45, <4 x i32>* %49, align 4, !tbaa !5
  %50 = or i64 %35, 16
  %51 = add <4 x i32> %36, <i32 16, i32 16, i32 16, i32 16>
  %52 = add <4 x i32> %36, <i32 20, i32 20, i32 20, i32 20>
  %53 = getelementptr i32, i32* %28, i64 %50
  %54 = bitcast i32* %53 to <4 x i32>*
  store <4 x i32> %51, <4 x i32>* %54, align 4, !tbaa !5
  %55 = getelementptr i32, i32* %53, i64 4
  %56 = bitcast i32* %55 to <4 x i32>*
  store <4 x i32> %52, <4 x i32>* %56, align 4, !tbaa !5
  %57 = or i64 %35, 24
  %58 = add <4 x i32> %36, <i32 24, i32 24, i32 24, i32 24>
  %59 = add <4 x i32> %36, <i32 28, i32 28, i32 28, i32 28>
  %60 = getelementptr i32, i32* %28, i64 %57
  %61 = bitcast i32* %60 to <4 x i32>*
  store <4 x i32> %58, <4 x i32>* %61, align 4, !tbaa !5
  %62 = getelementptr i32, i32* %60, i64 4
  %63 = bitcast i32* %62 to <4 x i32>*
  store <4 x i32> %59, <4 x i32>* %63, align 4, !tbaa !5
  %64 = add nuw i64 %35, 32
  %65 = add <4 x i32> %36, <i32 32, i32 32, i32 32, i32 32>
  %66 = add i64 %37, 4
  %67 = icmp eq i64 %66, %20
  br i1 %67, label %68, label %34, !llvm.loop !9

68:                                               ; preds = %34, %29
  %69 = phi i64 [ 0, %29 ], [ %64, %34 ]
  %70 = phi <4 x i32> [ %33, %29 ], [ %65, %34 ]
  br i1 %21, label %84, label %71

71:                                               ; preds = %68, %71
  %72 = phi i64 [ %80, %71 ], [ %69, %68 ]
  %73 = phi <4 x i32> [ %81, %71 ], [ %70, %68 ]
  %74 = phi i64 [ %82, %71 ], [ 0, %68 ]
  %75 = add <4 x i32> %73, <i32 4, i32 4, i32 4, i32 4>
  %76 = getelementptr i32, i32* %28, i64 %72
  %77 = bitcast i32* %76 to <4 x i32>*
  store <4 x i32> %73, <4 x i32>* %77, align 4, !tbaa !5
  %78 = getelementptr i32, i32* %76, i64 4
  %79 = bitcast i32* %78 to <4 x i32>*
  store <4 x i32> %75, <4 x i32>* %79, align 4, !tbaa !5
  %80 = add nuw i64 %72, 8
  %81 = add <4 x i32> %73, <i32 8, i32 8, i32 8, i32 8>
  %82 = add i64 %74, 1
  %83 = icmp eq i64 %82, %18
  br i1 %83, label %84, label %71, !llvm.loop !12

84:                                               ; preds = %71, %68
  br i1 %22, label %176, label %85

85:                                               ; preds = %26, %84
  %86 = phi i64 [ 0, %26 ], [ %16, %84 ]
  %87 = phi i32 [ %25, %26 ], [ %30, %84 ]
  br label %180

88:                                               ; preds = %176
  br i1 %7, label %89, label %175

89:                                               ; preds = %88
  %90 = getelementptr i32, i32* %2, i64 %9
  %91 = icmp ult i32 %1, 8
  %92 = and i64 %6, 4294967288
  %93 = trunc i64 %92 to i32
  %94 = and i64 %14, 3
  %95 = icmp ult i64 %12, 24
  %96 = and i64 %14, 4611686018427387900
  %97 = icmp eq i64 %94, 0
  %98 = icmp eq i64 %92, %6
  br label %99

99:                                               ; preds = %171, %89
  %100 = phi i64 [ 0, %89 ], [ %173, %171 ]
  %101 = phi i32 [ %177, %89 ], [ %172, %171 ]
  br i1 %8, label %102, label %171

102:                                              ; preds = %99
  %103 = mul nuw nsw i64 %100, %6
  %104 = getelementptr i32, i32* %90, i64 %103
  br i1 %91, label %161, label %105

105:                                              ; preds = %102
  %106 = add i32 %101, %93
  %107 = insertelement <4 x i32> poison, i32 %101, i64 0
  %108 = shufflevector <4 x i32> %107, <4 x i32> poison, <4 x i32> zeroinitializer
  %109 = add <4 x i32> %108, <i32 0, i32 1, i32 2, i32 3>
  br i1 %95, label %144, label %110

110:                                              ; preds = %105, %110
  %111 = phi i64 [ %140, %110 ], [ 0, %105 ]
  %112 = phi <4 x i32> [ %141, %110 ], [ %109, %105 ]
  %113 = phi i64 [ %142, %110 ], [ 0, %105 ]
  %114 = add <4 x i32> %112, <i32 4, i32 4, i32 4, i32 4>
  %115 = getelementptr i32, i32* %104, i64 %111
  %116 = bitcast i32* %115 to <4 x i32>*
  store <4 x i32> %112, <4 x i32>* %116, align 4, !tbaa !5
  %117 = getelementptr i32, i32* %115, i64 4
  %118 = bitcast i32* %117 to <4 x i32>*
  store <4 x i32> %114, <4 x i32>* %118, align 4, !tbaa !5
  %119 = or i64 %111, 8
  %120 = add <4 x i32> %112, <i32 8, i32 8, i32 8, i32 8>
  %121 = add <4 x i32> %112, <i32 12, i32 12, i32 12, i32 12>
  %122 = getelementptr i32, i32* %104, i64 %119
  %123 = bitcast i32* %122 to <4 x i32>*
  store <4 x i32> %120, <4 x i32>* %123, align 4, !tbaa !5
  %124 = getelementptr i32, i32* %122, i64 4
  %125 = bitcast i32* %124 to <4 x i32>*
  store <4 x i32> %121, <4 x i32>* %125, align 4, !tbaa !5
  %126 = or i64 %111, 16
  %127 = add <4 x i32> %112, <i32 16, i32 16, i32 16, i32 16>
  %128 = add <4 x i32> %112, <i32 20, i32 20, i32 20, i32 20>
  %129 = getelementptr i32, i32* %104, i64 %126
  %130 = bitcast i32* %129 to <4 x i32>*
  store <4 x i32> %127, <4 x i32>* %130, align 4, !tbaa !5
  %131 = getelementptr i32, i32* %129, i64 4
  %132 = bitcast i32* %131 to <4 x i32>*
  store <4 x i32> %128, <4 x i32>* %132, align 4, !tbaa !5
  %133 = or i64 %111, 24
  %134 = add <4 x i32> %112, <i32 24, i32 24, i32 24, i32 24>
  %135 = add <4 x i32> %112, <i32 28, i32 28, i32 28, i32 28>
  %136 = getelementptr i32, i32* %104, i64 %133
  %137 = bitcast i32* %136 to <4 x i32>*
  store <4 x i32> %134, <4 x i32>* %137, align 4, !tbaa !5
  %138 = getelementptr i32, i32* %136, i64 4
  %139 = bitcast i32* %138 to <4 x i32>*
  store <4 x i32> %135, <4 x i32>* %139, align 4, !tbaa !5
  %140 = add nuw i64 %111, 32
  %141 = add <4 x i32> %112, <i32 32, i32 32, i32 32, i32 32>
  %142 = add i64 %113, 4
  %143 = icmp eq i64 %142, %96
  br i1 %143, label %144, label %110, !llvm.loop !14

144:                                              ; preds = %110, %105
  %145 = phi i64 [ 0, %105 ], [ %140, %110 ]
  %146 = phi <4 x i32> [ %109, %105 ], [ %141, %110 ]
  br i1 %97, label %160, label %147

147:                                              ; preds = %144, %147
  %148 = phi i64 [ %156, %147 ], [ %145, %144 ]
  %149 = phi <4 x i32> [ %157, %147 ], [ %146, %144 ]
  %150 = phi i64 [ %158, %147 ], [ 0, %144 ]
  %151 = add <4 x i32> %149, <i32 4, i32 4, i32 4, i32 4>
  %152 = getelementptr i32, i32* %104, i64 %148
  %153 = bitcast i32* %152 to <4 x i32>*
  store <4 x i32> %149, <4 x i32>* %153, align 4, !tbaa !5
  %154 = getelementptr i32, i32* %152, i64 4
  %155 = bitcast i32* %154 to <4 x i32>*
  store <4 x i32> %151, <4 x i32>* %155, align 4, !tbaa !5
  %156 = add nuw i64 %148, 8
  %157 = add <4 x i32> %149, <i32 8, i32 8, i32 8, i32 8>
  %158 = add i64 %150, 1
  %159 = icmp eq i64 %158, %94
  br i1 %159, label %160, label %147, !llvm.loop !15

160:                                              ; preds = %147, %144
  br i1 %98, label %171, label %161

161:                                              ; preds = %102, %160
  %162 = phi i64 [ 0, %102 ], [ %92, %160 ]
  %163 = phi i32 [ %101, %102 ], [ %106, %160 ]
  br label %164

164:                                              ; preds = %161, %164
  %165 = phi i64 [ %169, %164 ], [ %162, %161 ]
  %166 = phi i32 [ %167, %164 ], [ %163, %161 ]
  %167 = add i32 %166, 1
  %168 = getelementptr i32, i32* %104, i64 %165
  store i32 %166, i32* %168, align 4, !tbaa !5
  %169 = add nuw nsw i64 %165, 1
  %170 = icmp eq i64 %169, %6
  br i1 %170, label %171, label %164, !llvm.loop !16

171:                                              ; preds = %164, %160, %99
  %172 = phi i32 [ %101, %99 ], [ %106, %160 ], [ %167, %164 ]
  %173 = add nuw nsw i64 %100, 1
  %174 = icmp eq i64 %173, %5
  br i1 %174, label %175, label %99, !llvm.loop !18

175:                                              ; preds = %171, %3, %88
  ret void

176:                                              ; preds = %180, %84, %23
  %177 = phi i32 [ %25, %23 ], [ %30, %84 ], [ %183, %180 ]
  %178 = add nuw nsw i64 %24, 1
  %179 = icmp eq i64 %178, %5
  br i1 %179, label %88, label %23, !llvm.loop !18

180:                                              ; preds = %85, %180
  %181 = phi i64 [ %185, %180 ], [ %86, %85 ]
  %182 = phi i32 [ %183, %180 ], [ %87, %85 ]
  %183 = add i32 %182, 1
  %184 = getelementptr i32, i32* %28, i64 %181
  store i32 %182, i32* %184, align 4, !tbaa !5
  %185 = add nuw nsw i64 %181, 1
  %186 = icmp eq i64 %185, %6
  br i1 %186, label %176, label %180, !llvm.loop !19
}

; Function Attrs: argmemonly mustprogress nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly mustprogress nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nofree norecurse nosync nounwind sspstrong uwtable writeonly
define void @use_arrays2(i32 noundef %0, i32 noundef %1, i32* nocapture noundef writeonly %2) local_unnamed_addr #0 {
  %4 = mul i32 %0, %0
  %5 = zext i32 %4 to i64
  %6 = zext i32 %1 to i64
  %7 = icmp sgt i32 %4, 0
  %8 = icmp sgt i32 %1, 0
  %9 = mul nuw i64 %5, %6
  br i1 %7, label %10, label %175

10:                                               ; preds = %3
  %11 = and i64 %6, 4294967288
  %12 = add nsw i64 %11, -8
  %13 = lshr exact i64 %12, 3
  %14 = add nuw nsw i64 %13, 1
  %15 = icmp ult i32 %1, 8
  %16 = and i64 %6, 4294967288
  %17 = trunc i64 %16 to i32
  %18 = and i64 %14, 3
  %19 = icmp ult i64 %12, 24
  %20 = and i64 %14, 4611686018427387900
  %21 = icmp eq i64 %18, 0
  %22 = icmp eq i64 %16, %6
  br label %23

23:                                               ; preds = %10, %176
  %24 = phi i64 [ %178, %176 ], [ 0, %10 ]
  %25 = phi i32 [ %177, %176 ], [ 1, %10 ]
  br i1 %8, label %26, label %176

26:                                               ; preds = %23
  %27 = mul nuw nsw i64 %24, %6
  %28 = getelementptr i32, i32* %2, i64 %27
  br i1 %15, label %85, label %29

29:                                               ; preds = %26
  %30 = add i32 %25, %17
  %31 = insertelement <4 x i32> poison, i32 %25, i64 0
  %32 = shufflevector <4 x i32> %31, <4 x i32> poison, <4 x i32> zeroinitializer
  %33 = add <4 x i32> %32, <i32 0, i32 1, i32 2, i32 3>
  br i1 %19, label %68, label %34

34:                                               ; preds = %29, %34
  %35 = phi i64 [ %64, %34 ], [ 0, %29 ]
  %36 = phi <4 x i32> [ %65, %34 ], [ %33, %29 ]
  %37 = phi i64 [ %66, %34 ], [ 0, %29 ]
  %38 = add <4 x i32> %36, <i32 4, i32 4, i32 4, i32 4>
  %39 = getelementptr i32, i32* %28, i64 %35
  %40 = bitcast i32* %39 to <4 x i32>*
  store <4 x i32> %36, <4 x i32>* %40, align 4, !tbaa !5
  %41 = getelementptr i32, i32* %39, i64 4
  %42 = bitcast i32* %41 to <4 x i32>*
  store <4 x i32> %38, <4 x i32>* %42, align 4, !tbaa !5
  %43 = or i64 %35, 8
  %44 = add <4 x i32> %36, <i32 8, i32 8, i32 8, i32 8>
  %45 = add <4 x i32> %36, <i32 12, i32 12, i32 12, i32 12>
  %46 = getelementptr i32, i32* %28, i64 %43
  %47 = bitcast i32* %46 to <4 x i32>*
  store <4 x i32> %44, <4 x i32>* %47, align 4, !tbaa !5
  %48 = getelementptr i32, i32* %46, i64 4
  %49 = bitcast i32* %48 to <4 x i32>*
  store <4 x i32> %45, <4 x i32>* %49, align 4, !tbaa !5
  %50 = or i64 %35, 16
  %51 = add <4 x i32> %36, <i32 16, i32 16, i32 16, i32 16>
  %52 = add <4 x i32> %36, <i32 20, i32 20, i32 20, i32 20>
  %53 = getelementptr i32, i32* %28, i64 %50
  %54 = bitcast i32* %53 to <4 x i32>*
  store <4 x i32> %51, <4 x i32>* %54, align 4, !tbaa !5
  %55 = getelementptr i32, i32* %53, i64 4
  %56 = bitcast i32* %55 to <4 x i32>*
  store <4 x i32> %52, <4 x i32>* %56, align 4, !tbaa !5
  %57 = or i64 %35, 24
  %58 = add <4 x i32> %36, <i32 24, i32 24, i32 24, i32 24>
  %59 = add <4 x i32> %36, <i32 28, i32 28, i32 28, i32 28>
  %60 = getelementptr i32, i32* %28, i64 %57
  %61 = bitcast i32* %60 to <4 x i32>*
  store <4 x i32> %58, <4 x i32>* %61, align 4, !tbaa !5
  %62 = getelementptr i32, i32* %60, i64 4
  %63 = bitcast i32* %62 to <4 x i32>*
  store <4 x i32> %59, <4 x i32>* %63, align 4, !tbaa !5
  %64 = add nuw i64 %35, 32
  %65 = add <4 x i32> %36, <i32 32, i32 32, i32 32, i32 32>
  %66 = add i64 %37, 4
  %67 = icmp eq i64 %66, %20
  br i1 %67, label %68, label %34, !llvm.loop !20

68:                                               ; preds = %34, %29
  %69 = phi i64 [ 0, %29 ], [ %64, %34 ]
  %70 = phi <4 x i32> [ %33, %29 ], [ %65, %34 ]
  br i1 %21, label %84, label %71

71:                                               ; preds = %68, %71
  %72 = phi i64 [ %80, %71 ], [ %69, %68 ]
  %73 = phi <4 x i32> [ %81, %71 ], [ %70, %68 ]
  %74 = phi i64 [ %82, %71 ], [ 0, %68 ]
  %75 = add <4 x i32> %73, <i32 4, i32 4, i32 4, i32 4>
  %76 = getelementptr i32, i32* %28, i64 %72
  %77 = bitcast i32* %76 to <4 x i32>*
  store <4 x i32> %73, <4 x i32>* %77, align 4, !tbaa !5
  %78 = getelementptr i32, i32* %76, i64 4
  %79 = bitcast i32* %78 to <4 x i32>*
  store <4 x i32> %75, <4 x i32>* %79, align 4, !tbaa !5
  %80 = add nuw i64 %72, 8
  %81 = add <4 x i32> %73, <i32 8, i32 8, i32 8, i32 8>
  %82 = add i64 %74, 1
  %83 = icmp eq i64 %82, %18
  br i1 %83, label %84, label %71, !llvm.loop !21

84:                                               ; preds = %71, %68
  br i1 %22, label %176, label %85

85:                                               ; preds = %26, %84
  %86 = phi i64 [ 0, %26 ], [ %16, %84 ]
  %87 = phi i32 [ %25, %26 ], [ %30, %84 ]
  br label %180

88:                                               ; preds = %176
  br i1 %7, label %89, label %175

89:                                               ; preds = %88
  %90 = getelementptr i32, i32* %2, i64 %9
  %91 = icmp ult i32 %1, 8
  %92 = and i64 %6, 4294967288
  %93 = trunc i64 %92 to i32
  %94 = and i64 %14, 3
  %95 = icmp ult i64 %12, 24
  %96 = and i64 %14, 4611686018427387900
  %97 = icmp eq i64 %94, 0
  %98 = icmp eq i64 %92, %6
  br label %99

99:                                               ; preds = %171, %89
  %100 = phi i64 [ 0, %89 ], [ %173, %171 ]
  %101 = phi i32 [ %177, %89 ], [ %172, %171 ]
  br i1 %8, label %102, label %171

102:                                              ; preds = %99
  %103 = mul nuw nsw i64 %100, %6
  %104 = getelementptr i32, i32* %90, i64 %103
  br i1 %91, label %161, label %105

105:                                              ; preds = %102
  %106 = add i32 %101, %93
  %107 = insertelement <4 x i32> poison, i32 %101, i64 0
  %108 = shufflevector <4 x i32> %107, <4 x i32> poison, <4 x i32> zeroinitializer
  %109 = add <4 x i32> %108, <i32 0, i32 1, i32 2, i32 3>
  br i1 %95, label %144, label %110

110:                                              ; preds = %105, %110
  %111 = phi i64 [ %140, %110 ], [ 0, %105 ]
  %112 = phi <4 x i32> [ %141, %110 ], [ %109, %105 ]
  %113 = phi i64 [ %142, %110 ], [ 0, %105 ]
  %114 = add <4 x i32> %112, <i32 4, i32 4, i32 4, i32 4>
  %115 = getelementptr i32, i32* %104, i64 %111
  %116 = bitcast i32* %115 to <4 x i32>*
  store <4 x i32> %112, <4 x i32>* %116, align 4, !tbaa !5
  %117 = getelementptr i32, i32* %115, i64 4
  %118 = bitcast i32* %117 to <4 x i32>*
  store <4 x i32> %114, <4 x i32>* %118, align 4, !tbaa !5
  %119 = or i64 %111, 8
  %120 = add <4 x i32> %112, <i32 8, i32 8, i32 8, i32 8>
  %121 = add <4 x i32> %112, <i32 12, i32 12, i32 12, i32 12>
  %122 = getelementptr i32, i32* %104, i64 %119
  %123 = bitcast i32* %122 to <4 x i32>*
  store <4 x i32> %120, <4 x i32>* %123, align 4, !tbaa !5
  %124 = getelementptr i32, i32* %122, i64 4
  %125 = bitcast i32* %124 to <4 x i32>*
  store <4 x i32> %121, <4 x i32>* %125, align 4, !tbaa !5
  %126 = or i64 %111, 16
  %127 = add <4 x i32> %112, <i32 16, i32 16, i32 16, i32 16>
  %128 = add <4 x i32> %112, <i32 20, i32 20, i32 20, i32 20>
  %129 = getelementptr i32, i32* %104, i64 %126
  %130 = bitcast i32* %129 to <4 x i32>*
  store <4 x i32> %127, <4 x i32>* %130, align 4, !tbaa !5
  %131 = getelementptr i32, i32* %129, i64 4
  %132 = bitcast i32* %131 to <4 x i32>*
  store <4 x i32> %128, <4 x i32>* %132, align 4, !tbaa !5
  %133 = or i64 %111, 24
  %134 = add <4 x i32> %112, <i32 24, i32 24, i32 24, i32 24>
  %135 = add <4 x i32> %112, <i32 28, i32 28, i32 28, i32 28>
  %136 = getelementptr i32, i32* %104, i64 %133
  %137 = bitcast i32* %136 to <4 x i32>*
  store <4 x i32> %134, <4 x i32>* %137, align 4, !tbaa !5
  %138 = getelementptr i32, i32* %136, i64 4
  %139 = bitcast i32* %138 to <4 x i32>*
  store <4 x i32> %135, <4 x i32>* %139, align 4, !tbaa !5
  %140 = add nuw i64 %111, 32
  %141 = add <4 x i32> %112, <i32 32, i32 32, i32 32, i32 32>
  %142 = add i64 %113, 4
  %143 = icmp eq i64 %142, %96
  br i1 %143, label %144, label %110, !llvm.loop !22

144:                                              ; preds = %110, %105
  %145 = phi i64 [ 0, %105 ], [ %140, %110 ]
  %146 = phi <4 x i32> [ %109, %105 ], [ %141, %110 ]
  br i1 %97, label %160, label %147

147:                                              ; preds = %144, %147
  %148 = phi i64 [ %156, %147 ], [ %145, %144 ]
  %149 = phi <4 x i32> [ %157, %147 ], [ %146, %144 ]
  %150 = phi i64 [ %158, %147 ], [ 0, %144 ]
  %151 = add <4 x i32> %149, <i32 4, i32 4, i32 4, i32 4>
  %152 = getelementptr i32, i32* %104, i64 %148
  %153 = bitcast i32* %152 to <4 x i32>*
  store <4 x i32> %149, <4 x i32>* %153, align 4, !tbaa !5
  %154 = getelementptr i32, i32* %152, i64 4
  %155 = bitcast i32* %154 to <4 x i32>*
  store <4 x i32> %151, <4 x i32>* %155, align 4, !tbaa !5
  %156 = add nuw i64 %148, 8
  %157 = add <4 x i32> %149, <i32 8, i32 8, i32 8, i32 8>
  %158 = add i64 %150, 1
  %159 = icmp eq i64 %158, %94
  br i1 %159, label %160, label %147, !llvm.loop !23

160:                                              ; preds = %147, %144
  br i1 %98, label %171, label %161

161:                                              ; preds = %102, %160
  %162 = phi i64 [ 0, %102 ], [ %92, %160 ]
  %163 = phi i32 [ %101, %102 ], [ %106, %160 ]
  br label %164

164:                                              ; preds = %161, %164
  %165 = phi i64 [ %169, %164 ], [ %162, %161 ]
  %166 = phi i32 [ %167, %164 ], [ %163, %161 ]
  %167 = add i32 %166, 1
  %168 = getelementptr i32, i32* %104, i64 %165
  store i32 %166, i32* %168, align 4, !tbaa !5
  %169 = add nuw nsw i64 %165, 1
  %170 = icmp eq i64 %169, %6
  br i1 %170, label %171, label %164, !llvm.loop !24

171:                                              ; preds = %164, %160, %99
  %172 = phi i32 [ %101, %99 ], [ %106, %160 ], [ %167, %164 ]
  %173 = add nuw nsw i64 %100, 1
  %174 = icmp eq i64 %173, %5
  br i1 %174, label %175, label %99, !llvm.loop !25

175:                                              ; preds = %171, %3, %88
  ret void

176:                                              ; preds = %180, %84, %23
  %177 = phi i32 [ %25, %23 ], [ %30, %84 ], [ %183, %180 ]
  %178 = add nuw nsw i64 %24, 1
  %179 = icmp eq i64 %178, %5
  br i1 %179, label %88, label %23, !llvm.loop !25

180:                                              ; preds = %85, %180
  %181 = phi i64 [ %185, %180 ], [ %86, %85 ]
  %182 = phi i32 [ %183, %180 ], [ %87, %85 ]
  %183 = add i32 %182, 1
  %184 = getelementptr i32, i32* %28, i64 %181
  store i32 %182, i32* %184, align 4, !tbaa !5
  %185 = add nuw nsw i64 %181, 1
  %186 = icmp eq i64 %185, %6
  br i1 %186, label %176, label %180, !llvm.loop !26
}

; Function Attrs: nofree nosync nounwind sspstrong uwtable
define void @variable_arrays(i32* nocapture noundef writeonly %0) local_unnamed_addr #2 {
  %2 = alloca [4 x [4 x [5 x i32]]], align 16
  %3 = bitcast [4 x [4 x [5 x i32]]]* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 320, i8* nonnull %3) #4
  %4 = bitcast [4 x [4 x [5 x i32]]]* %2 to <4 x i32>*
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32>* %4, align 16, !tbaa !5
  %5 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 4
  %6 = bitcast i32* %5 to <4 x i32>*
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, <4 x i32>* %6, align 16, !tbaa !5
  %7 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 8
  %8 = bitcast i32* %7 to <4 x i32>*
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, <4 x i32>* %8, align 16, !tbaa !5
  %9 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 12
  %10 = bitcast i32* %9 to <4 x i32>*
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, <4 x i32>* %10, align 16, !tbaa !5
  %11 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 16
  %12 = bitcast i32* %11 to <4 x i32>*
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, <4 x i32>* %12, align 16, !tbaa !5
  %13 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 20
  %14 = bitcast i32* %13 to <4 x i32>*
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, <4 x i32>* %14, align 16, !tbaa !5
  %15 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 24
  %16 = bitcast i32* %15 to <4 x i32>*
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, <4 x i32>* %16, align 16, !tbaa !5
  %17 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 28
  %18 = bitcast i32* %17 to <4 x i32>*
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, <4 x i32>* %18, align 16, !tbaa !5
  %19 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 32
  %20 = bitcast i32* %19 to <4 x i32>*
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, <4 x i32>* %20, align 16, !tbaa !5
  %21 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 36
  %22 = bitcast i32* %21 to <4 x i32>*
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, <4 x i32>* %22, align 16, !tbaa !5
  %23 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 0
  %24 = bitcast i32* %23 to <4 x i32>*
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32>* %24, align 16, !tbaa !5
  %25 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 4
  %26 = bitcast i32* %25 to <4 x i32>*
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, <4 x i32>* %26, align 16, !tbaa !5
  %27 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 8
  %28 = bitcast i32* %27 to <4 x i32>*
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, <4 x i32>* %28, align 16, !tbaa !5
  %29 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 12
  %30 = bitcast i32* %29 to <4 x i32>*
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, <4 x i32>* %30, align 16, !tbaa !5
  %31 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 16
  %32 = bitcast i32* %31 to <4 x i32>*
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, <4 x i32>* %32, align 16, !tbaa !5
  %33 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 20
  %34 = bitcast i32* %33 to <4 x i32>*
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, <4 x i32>* %34, align 16, !tbaa !5
  %35 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 24
  %36 = bitcast i32* %35 to <4 x i32>*
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, <4 x i32>* %36, align 16, !tbaa !5
  %37 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 28
  %38 = bitcast i32* %37 to <4 x i32>*
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, <4 x i32>* %38, align 16, !tbaa !5
  %39 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 32
  %40 = bitcast i32* %39 to <4 x i32>*
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, <4 x i32>* %40, align 16, !tbaa !5
  %41 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 36
  %42 = bitcast i32* %41 to <4 x i32>*
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, <4 x i32>* %42, align 16, !tbaa !5
  %43 = bitcast [4 x [4 x [5 x i32]]]* %2 to <4 x i32>*
  %44 = load <4 x i32>, <4 x i32>* %43, align 16, !tbaa !5
  %45 = bitcast i32* %0 to <4 x i32>*
  store <4 x i32> %44, <4 x i32>* %45, align 4, !tbaa !5
  %46 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 4
  %47 = getelementptr i32, i32* %0, i64 4
  %48 = bitcast i32* %46 to <4 x i32>*
  %49 = load <4 x i32>, <4 x i32>* %48, align 16, !tbaa !5
  %50 = bitcast i32* %47 to <4 x i32>*
  store <4 x i32> %49, <4 x i32>* %50, align 4, !tbaa !5
  %51 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 1, i64 3
  %52 = getelementptr i32, i32* %0, i64 8
  %53 = bitcast i32* %51 to <4 x i32>*
  %54 = load <4 x i32>, <4 x i32>* %53, align 16, !tbaa !5
  %55 = bitcast i32* %52 to <4 x i32>*
  store <4 x i32> %54, <4 x i32>* %55, align 4, !tbaa !5
  %56 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 2, i64 2
  %57 = getelementptr i32, i32* %0, i64 12
  %58 = bitcast i32* %56 to <4 x i32>*
  %59 = load <4 x i32>, <4 x i32>* %58, align 16, !tbaa !5
  %60 = bitcast i32* %57 to <4 x i32>*
  store <4 x i32> %59, <4 x i32>* %60, align 4, !tbaa !5
  %61 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 3, i64 1
  %62 = getelementptr i32, i32* %0, i64 16
  %63 = bitcast i32* %61 to <4 x i32>*
  %64 = load <4 x i32>, <4 x i32>* %63, align 16, !tbaa !5
  %65 = bitcast i32* %62 to <4 x i32>*
  store <4 x i32> %64, <4 x i32>* %65, align 4, !tbaa !5
  %66 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 0, i64 0
  %67 = getelementptr i32, i32* %0, i64 20
  %68 = bitcast i32* %66 to <4 x i32>*
  %69 = load <4 x i32>, <4 x i32>* %68, align 16, !tbaa !5
  %70 = bitcast i32* %67 to <4 x i32>*
  store <4 x i32> %69, <4 x i32>* %70, align 4, !tbaa !5
  %71 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 0, i64 4
  %72 = getelementptr i32, i32* %0, i64 24
  %73 = bitcast i32* %71 to <4 x i32>*
  %74 = load <4 x i32>, <4 x i32>* %73, align 16, !tbaa !5
  %75 = bitcast i32* %72 to <4 x i32>*
  store <4 x i32> %74, <4 x i32>* %75, align 4, !tbaa !5
  %76 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 1, i64 3
  %77 = getelementptr i32, i32* %0, i64 28
  %78 = bitcast i32* %76 to <4 x i32>*
  %79 = load <4 x i32>, <4 x i32>* %78, align 16, !tbaa !5
  %80 = bitcast i32* %77 to <4 x i32>*
  store <4 x i32> %79, <4 x i32>* %80, align 4, !tbaa !5
  %81 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 2, i64 2
  %82 = getelementptr i32, i32* %0, i64 32
  %83 = bitcast i32* %81 to <4 x i32>*
  %84 = load <4 x i32>, <4 x i32>* %83, align 16, !tbaa !5
  %85 = bitcast i32* %82 to <4 x i32>*
  store <4 x i32> %84, <4 x i32>* %85, align 4, !tbaa !5
  %86 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 3, i64 1
  %87 = getelementptr i32, i32* %0, i64 36
  %88 = bitcast i32* %86 to <4 x i32>*
  %89 = load <4 x i32>, <4 x i32>* %88, align 16, !tbaa !5
  %90 = bitcast i32* %87 to <4 x i32>*
  store <4 x i32> %89, <4 x i32>* %90, align 4, !tbaa !5
  %91 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 0
  %92 = getelementptr i32, i32* %0, i64 40
  %93 = bitcast i32* %91 to <4 x i32>*
  %94 = load <4 x i32>, <4 x i32>* %93, align 16, !tbaa !5
  %95 = bitcast i32* %92 to <4 x i32>*
  store <4 x i32> %94, <4 x i32>* %95, align 4, !tbaa !5
  %96 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 4
  %97 = getelementptr i32, i32* %0, i64 44
  %98 = bitcast i32* %96 to <4 x i32>*
  %99 = load <4 x i32>, <4 x i32>* %98, align 16, !tbaa !5
  %100 = bitcast i32* %97 to <4 x i32>*
  store <4 x i32> %99, <4 x i32>* %100, align 4, !tbaa !5
  %101 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 1, i64 3
  %102 = getelementptr i32, i32* %0, i64 48
  %103 = bitcast i32* %101 to <4 x i32>*
  %104 = load <4 x i32>, <4 x i32>* %103, align 16, !tbaa !5
  %105 = bitcast i32* %102 to <4 x i32>*
  store <4 x i32> %104, <4 x i32>* %105, align 4, !tbaa !5
  %106 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 2, i64 2
  %107 = getelementptr i32, i32* %0, i64 52
  %108 = bitcast i32* %106 to <4 x i32>*
  %109 = load <4 x i32>, <4 x i32>* %108, align 16, !tbaa !5
  %110 = bitcast i32* %107 to <4 x i32>*
  store <4 x i32> %109, <4 x i32>* %110, align 4, !tbaa !5
  %111 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 3, i64 1
  %112 = getelementptr i32, i32* %0, i64 56
  %113 = bitcast i32* %111 to <4 x i32>*
  %114 = load <4 x i32>, <4 x i32>* %113, align 16, !tbaa !5
  %115 = bitcast i32* %112 to <4 x i32>*
  store <4 x i32> %114, <4 x i32>* %115, align 4, !tbaa !5
  %116 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 0, i64 0
  %117 = getelementptr i32, i32* %0, i64 60
  %118 = bitcast i32* %116 to <4 x i32>*
  %119 = load <4 x i32>, <4 x i32>* %118, align 16, !tbaa !5
  %120 = bitcast i32* %117 to <4 x i32>*
  store <4 x i32> %119, <4 x i32>* %120, align 4, !tbaa !5
  %121 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 0, i64 4
  %122 = getelementptr i32, i32* %0, i64 64
  %123 = bitcast i32* %121 to <4 x i32>*
  %124 = load <4 x i32>, <4 x i32>* %123, align 16, !tbaa !5
  %125 = bitcast i32* %122 to <4 x i32>*
  store <4 x i32> %124, <4 x i32>* %125, align 4, !tbaa !5
  %126 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 1, i64 3
  %127 = getelementptr i32, i32* %0, i64 68
  %128 = bitcast i32* %126 to <4 x i32>*
  %129 = load <4 x i32>, <4 x i32>* %128, align 16, !tbaa !5
  %130 = bitcast i32* %127 to <4 x i32>*
  store <4 x i32> %129, <4 x i32>* %130, align 4, !tbaa !5
  %131 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 2, i64 2
  %132 = getelementptr i32, i32* %0, i64 72
  %133 = bitcast i32* %131 to <4 x i32>*
  %134 = load <4 x i32>, <4 x i32>* %133, align 16, !tbaa !5
  %135 = bitcast i32* %132 to <4 x i32>*
  store <4 x i32> %134, <4 x i32>* %135, align 4, !tbaa !5
  %136 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 3, i64 1
  %137 = getelementptr i32, i32* %0, i64 76
  %138 = bitcast i32* %136 to <4 x i32>*
  %139 = load <4 x i32>, <4 x i32>* %138, align 16, !tbaa !5
  %140 = bitcast i32* %137 to <4 x i32>*
  store <4 x i32> %139, <4 x i32>* %140, align 4, !tbaa !5
  %141 = getelementptr i32, i32* %0, i64 80
  %142 = bitcast i32* %141 to <4 x i32>*
  store <4 x i32> <i32 0, i32 3, i32 6, i32 9>, <4 x i32>* %142, align 4, !tbaa !5
  %143 = getelementptr i32, i32* %0, i64 84
  %144 = bitcast i32* %143 to <4 x i32>*
  store <4 x i32> <i32 12, i32 15, i32 18, i32 21>, <4 x i32>* %144, align 4, !tbaa !5
  call void @llvm.lifetime.end.p0i8(i64 320, i8* nonnull %3) #4
  ret void
}

; Function Attrs: nofree nosync nounwind sspstrong uwtable writeonly
define void @alloca_arrays(i32* nocapture noundef writeonly %0) local_unnamed_addr #3 {
  %2 = alloca [4 x [4 x [5 x i32]]], align 16
  %3 = bitcast [4 x [4 x [5 x i32]]]* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 320, i8* nonnull %3) #4
  %4 = bitcast [4 x [4 x [5 x i32]]]* %2 to <4 x i32>*
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32>* %4, align 16, !tbaa !5
  %5 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 4
  %6 = bitcast i32* %5 to <4 x i32>*
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, <4 x i32>* %6, align 16, !tbaa !5
  %7 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 8
  %8 = bitcast i32* %7 to <4 x i32>*
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, <4 x i32>* %8, align 16, !tbaa !5
  %9 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 12
  %10 = bitcast i32* %9 to <4 x i32>*
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, <4 x i32>* %10, align 16, !tbaa !5
  %11 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 16
  %12 = bitcast i32* %11 to <4 x i32>*
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, <4 x i32>* %12, align 16, !tbaa !5
  %13 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 20
  %14 = bitcast i32* %13 to <4 x i32>*
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, <4 x i32>* %14, align 16, !tbaa !5
  %15 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 24
  %16 = bitcast i32* %15 to <4 x i32>*
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, <4 x i32>* %16, align 16, !tbaa !5
  %17 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 28
  %18 = bitcast i32* %17 to <4 x i32>*
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, <4 x i32>* %18, align 16, !tbaa !5
  %19 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 32
  %20 = bitcast i32* %19 to <4 x i32>*
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, <4 x i32>* %20, align 16, !tbaa !5
  %21 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 36
  %22 = bitcast i32* %21 to <4 x i32>*
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, <4 x i32>* %22, align 16, !tbaa !5
  %23 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 0
  %24 = bitcast i32* %23 to <4 x i32>*
  store <4 x i32> <i32 1, i32 2, i32 3, i32 4>, <4 x i32>* %24, align 16, !tbaa !5
  %25 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 4
  %26 = bitcast i32* %25 to <4 x i32>*
  store <4 x i32> <i32 5, i32 6, i32 7, i32 8>, <4 x i32>* %26, align 16, !tbaa !5
  %27 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 8
  %28 = bitcast i32* %27 to <4 x i32>*
  store <4 x i32> <i32 9, i32 10, i32 11, i32 12>, <4 x i32>* %28, align 16, !tbaa !5
  %29 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 12
  %30 = bitcast i32* %29 to <4 x i32>*
  store <4 x i32> <i32 13, i32 14, i32 15, i32 16>, <4 x i32>* %30, align 16, !tbaa !5
  %31 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 16
  %32 = bitcast i32* %31 to <4 x i32>*
  store <4 x i32> <i32 17, i32 18, i32 19, i32 20>, <4 x i32>* %32, align 16, !tbaa !5
  %33 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 20
  %34 = bitcast i32* %33 to <4 x i32>*
  store <4 x i32> <i32 21, i32 22, i32 23, i32 24>, <4 x i32>* %34, align 16, !tbaa !5
  %35 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 24
  %36 = bitcast i32* %35 to <4 x i32>*
  store <4 x i32> <i32 25, i32 26, i32 27, i32 28>, <4 x i32>* %36, align 16, !tbaa !5
  %37 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 28
  %38 = bitcast i32* %37 to <4 x i32>*
  store <4 x i32> <i32 29, i32 30, i32 31, i32 32>, <4 x i32>* %38, align 16, !tbaa !5
  %39 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 32
  %40 = bitcast i32* %39 to <4 x i32>*
  store <4 x i32> <i32 33, i32 34, i32 35, i32 36>, <4 x i32>* %40, align 16, !tbaa !5
  %41 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 36
  %42 = bitcast i32* %41 to <4 x i32>*
  store <4 x i32> <i32 37, i32 38, i32 39, i32 40>, <4 x i32>* %42, align 16, !tbaa !5
  %43 = bitcast [4 x [4 x [5 x i32]]]* %2 to <4 x i32>*
  %44 = load <4 x i32>, <4 x i32>* %43, align 16, !tbaa !5
  %45 = bitcast i32* %0 to <4 x i32>*
  store <4 x i32> %44, <4 x i32>* %45, align 4, !tbaa !5
  %46 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 0, i64 4
  %47 = getelementptr i32, i32* %0, i64 4
  %48 = bitcast i32* %46 to <4 x i32>*
  %49 = load <4 x i32>, <4 x i32>* %48, align 16, !tbaa !5
  %50 = bitcast i32* %47 to <4 x i32>*
  store <4 x i32> %49, <4 x i32>* %50, align 4, !tbaa !5
  %51 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 1, i64 3
  %52 = getelementptr i32, i32* %0, i64 8
  %53 = bitcast i32* %51 to <4 x i32>*
  %54 = load <4 x i32>, <4 x i32>* %53, align 16, !tbaa !5
  %55 = bitcast i32* %52 to <4 x i32>*
  store <4 x i32> %54, <4 x i32>* %55, align 4, !tbaa !5
  %56 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 2, i64 2
  %57 = getelementptr i32, i32* %0, i64 12
  %58 = bitcast i32* %56 to <4 x i32>*
  %59 = load <4 x i32>, <4 x i32>* %58, align 16, !tbaa !5
  %60 = bitcast i32* %57 to <4 x i32>*
  store <4 x i32> %59, <4 x i32>* %60, align 4, !tbaa !5
  %61 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 0, i64 3, i64 1
  %62 = getelementptr i32, i32* %0, i64 16
  %63 = bitcast i32* %61 to <4 x i32>*
  %64 = load <4 x i32>, <4 x i32>* %63, align 16, !tbaa !5
  %65 = bitcast i32* %62 to <4 x i32>*
  store <4 x i32> %64, <4 x i32>* %65, align 4, !tbaa !5
  %66 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 0, i64 0
  %67 = getelementptr i32, i32* %0, i64 20
  %68 = bitcast i32* %66 to <4 x i32>*
  %69 = load <4 x i32>, <4 x i32>* %68, align 16, !tbaa !5
  %70 = bitcast i32* %67 to <4 x i32>*
  store <4 x i32> %69, <4 x i32>* %70, align 4, !tbaa !5
  %71 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 0, i64 4
  %72 = getelementptr i32, i32* %0, i64 24
  %73 = bitcast i32* %71 to <4 x i32>*
  %74 = load <4 x i32>, <4 x i32>* %73, align 16, !tbaa !5
  %75 = bitcast i32* %72 to <4 x i32>*
  store <4 x i32> %74, <4 x i32>* %75, align 4, !tbaa !5
  %76 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 1, i64 3
  %77 = getelementptr i32, i32* %0, i64 28
  %78 = bitcast i32* %76 to <4 x i32>*
  %79 = load <4 x i32>, <4 x i32>* %78, align 16, !tbaa !5
  %80 = bitcast i32* %77 to <4 x i32>*
  store <4 x i32> %79, <4 x i32>* %80, align 4, !tbaa !5
  %81 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 2, i64 2
  %82 = getelementptr i32, i32* %0, i64 32
  %83 = bitcast i32* %81 to <4 x i32>*
  %84 = load <4 x i32>, <4 x i32>* %83, align 16, !tbaa !5
  %85 = bitcast i32* %82 to <4 x i32>*
  store <4 x i32> %84, <4 x i32>* %85, align 4, !tbaa !5
  %86 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 1, i64 3, i64 1
  %87 = getelementptr i32, i32* %0, i64 36
  %88 = bitcast i32* %86 to <4 x i32>*
  %89 = load <4 x i32>, <4 x i32>* %88, align 16, !tbaa !5
  %90 = bitcast i32* %87 to <4 x i32>*
  store <4 x i32> %89, <4 x i32>* %90, align 4, !tbaa !5
  %91 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 0
  %92 = getelementptr i32, i32* %0, i64 40
  %93 = bitcast i32* %91 to <4 x i32>*
  %94 = load <4 x i32>, <4 x i32>* %93, align 16, !tbaa !5
  %95 = bitcast i32* %92 to <4 x i32>*
  store <4 x i32> %94, <4 x i32>* %95, align 4, !tbaa !5
  %96 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 0, i64 4
  %97 = getelementptr i32, i32* %0, i64 44
  %98 = bitcast i32* %96 to <4 x i32>*
  %99 = load <4 x i32>, <4 x i32>* %98, align 16, !tbaa !5
  %100 = bitcast i32* %97 to <4 x i32>*
  store <4 x i32> %99, <4 x i32>* %100, align 4, !tbaa !5
  %101 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 1, i64 3
  %102 = getelementptr i32, i32* %0, i64 48
  %103 = bitcast i32* %101 to <4 x i32>*
  %104 = load <4 x i32>, <4 x i32>* %103, align 16, !tbaa !5
  %105 = bitcast i32* %102 to <4 x i32>*
  store <4 x i32> %104, <4 x i32>* %105, align 4, !tbaa !5
  %106 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 2, i64 2
  %107 = getelementptr i32, i32* %0, i64 52
  %108 = bitcast i32* %106 to <4 x i32>*
  %109 = load <4 x i32>, <4 x i32>* %108, align 16, !tbaa !5
  %110 = bitcast i32* %107 to <4 x i32>*
  store <4 x i32> %109, <4 x i32>* %110, align 4, !tbaa !5
  %111 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 2, i64 3, i64 1
  %112 = getelementptr i32, i32* %0, i64 56
  %113 = bitcast i32* %111 to <4 x i32>*
  %114 = load <4 x i32>, <4 x i32>* %113, align 16, !tbaa !5
  %115 = bitcast i32* %112 to <4 x i32>*
  store <4 x i32> %114, <4 x i32>* %115, align 4, !tbaa !5
  %116 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 0, i64 0
  %117 = getelementptr i32, i32* %0, i64 60
  %118 = bitcast i32* %116 to <4 x i32>*
  %119 = load <4 x i32>, <4 x i32>* %118, align 16, !tbaa !5
  %120 = bitcast i32* %117 to <4 x i32>*
  store <4 x i32> %119, <4 x i32>* %120, align 4, !tbaa !5
  %121 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 0, i64 4
  %122 = getelementptr i32, i32* %0, i64 64
  %123 = bitcast i32* %121 to <4 x i32>*
  %124 = load <4 x i32>, <4 x i32>* %123, align 16, !tbaa !5
  %125 = bitcast i32* %122 to <4 x i32>*
  store <4 x i32> %124, <4 x i32>* %125, align 4, !tbaa !5
  %126 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 1, i64 3
  %127 = getelementptr i32, i32* %0, i64 68
  %128 = bitcast i32* %126 to <4 x i32>*
  %129 = load <4 x i32>, <4 x i32>* %128, align 16, !tbaa !5
  %130 = bitcast i32* %127 to <4 x i32>*
  store <4 x i32> %129, <4 x i32>* %130, align 4, !tbaa !5
  %131 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 2, i64 2
  %132 = getelementptr i32, i32* %0, i64 72
  %133 = bitcast i32* %131 to <4 x i32>*
  %134 = load <4 x i32>, <4 x i32>* %133, align 16, !tbaa !5
  %135 = bitcast i32* %132 to <4 x i32>*
  store <4 x i32> %134, <4 x i32>* %135, align 4, !tbaa !5
  %136 = getelementptr inbounds [4 x [4 x [5 x i32]]], [4 x [4 x [5 x i32]]]* %2, i64 0, i64 3, i64 3, i64 1
  %137 = getelementptr i32, i32* %0, i64 76
  %138 = bitcast i32* %136 to <4 x i32>*
  %139 = load <4 x i32>, <4 x i32>* %138, align 16, !tbaa !5
  %140 = bitcast i32* %137 to <4 x i32>*
  store <4 x i32> %139, <4 x i32>* %140, align 4, !tbaa !5
  %141 = getelementptr i32, i32* %0, i64 80
  %142 = bitcast i32* %141 to <4 x i32>*
  store <4 x i32> <i32 0, i32 3, i32 6, i32 9>, <4 x i32>* %142, align 4, !tbaa !5
  %143 = getelementptr i32, i32* %0, i64 84
  %144 = bitcast i32* %143 to <4 x i32>*
  store <4 x i32> <i32 12, i32 15, i32 18, i32 21>, <4 x i32>* %144, align 4, !tbaa !5
  call void @llvm.lifetime.end.p0i8(i64 320, i8* nonnull %3) #4
  ret void
}

attributes #0 = { nofree norecurse nosync nounwind sspstrong uwtable writeonly "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { argmemonly mustprogress nofree nosync nounwind willreturn }
attributes #2 = { nofree nosync nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nofree nosync nounwind sspstrong uwtable writeonly "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nounwind }

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
!9 = distinct !{!9, !10, !11}
!10 = !{!"llvm.loop.mustprogress"}
!11 = !{!"llvm.loop.isvectorized", i32 1}
!12 = distinct !{!12, !13}
!13 = !{!"llvm.loop.unroll.disable"}
!14 = distinct !{!14, !10, !11}
!15 = distinct !{!15, !13}
!16 = distinct !{!16, !10, !17, !11}
!17 = !{!"llvm.loop.unroll.runtime.disable"}
!18 = distinct !{!18, !10}
!19 = distinct !{!19, !10, !17, !11}
!20 = distinct !{!20, !10, !11}
!21 = distinct !{!21, !13}
!22 = distinct !{!22, !10, !11}
!23 = distinct !{!23, !13}
!24 = distinct !{!24, !10, !17, !11}
!25 = distinct !{!25, !10}
!26 = distinct !{!26, !10, !17, !11}
