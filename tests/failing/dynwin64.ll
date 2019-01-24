; Global variables
@D = internal constant [3 x double] [double -140970442.972, double -283764497.129, double 199908331.327], align 16
; Prototypes for intrinsics we use
declare void @llvm.memcpy.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)
declare float @llvm.maxnum.f32(float, float)
declare double @llvm.maxnum.f64(double, double)
declare float @llvm.fabs.f32(float)
declare double @llvm.fabs.f64(double)
;  Top-level operator definition
define void @dynwin64([5 x double]* readonly align 16 nonnull %X, [1 x double]* align 16 nonnull %Y) {
; --- Operator: FSHCompose ---
b62:
  
  %l0 = alloca [2 x double], align 16
  br label %b61
; --- Operator: FSHHTSUMUnion ---
b61:
  
  %l13 = alloca [2 x double], align 16
  %l14 = alloca [2 x double], align 16
  br label %b60
; --- Operator: FSHCompose ---
b60:
  
  %l71 = alloca [1 x double], align 16
  br label %IReduction_init_loop_entry58
; --- Operator: FSHIReduction ---
IReduction_init_loop_entry58:
  
  %IReductoin_tmp75 = alloca [1 x double], align 16
  %l118 = icmp slt i64 0, 1
  br i1 %l118, label %IReduction_init_loop_loop59, label %IReduction_main_loop_entry54
IReduction_init_loop_loop59:
  %IReduction_init_i117 = phi i64 [0, %IReduction_init_loop_entry58], [%IReduction_init_loop_next_i120, %IReduction_init_lcont57]
  
  br label %IReduction_init56
IReduction_init56:
  
  %l116 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp75, i64 0, i64 %IReduction_init_i117
  ; void instr 68
  store double 0., double* %l116, align 8
  br label %IReduction_init_lcont57
IReduction_init_lcont57:
  
  %IReduction_init_loop_next_i120 = add i64 %IReduction_init_i117, 1
  %l119 = icmp slt i64 %IReduction_init_loop_next_i120, 1
  br i1 %l119, label %IReduction_init_loop_loop59, label %IReduction_main_loop_entry54
IReduction_main_loop_entry54:
  
  %l113 = icmp slt i64 0, 2
  br i1 %l113, label %IReduction_main_loop_loop55, label %eUnion35
IReduction_main_loop_loop55:
  %IReduction_main_i37 = phi i64 [0, %IReduction_main_loop_entry54], [%IReduction_main_loop_next_i115, %IReduction_main_lcont36]
  
  br label %b53
; --- Operator: FSHCompose ---
b53:
  
  %l85 = alloca [2 x double], align 16
  br label %Union_loop_entry51
; --- Operator: FSHIUnion ---
Union_loop_entry51:
  
  %l110 = icmp slt i64 0, 2
  br i1 %l110, label %Union_loop_loop52, label %BinOp_entry44
Union_loop_loop52:
  %Union_i47 = phi i64 [0, %Union_loop_entry51], [%Union_loop_next_i112, %Union_lcont46]
  
  br label %b50
; --- Operator: FSHCompose ---
b50:
  
  %l98 = alloca [1 x double], align 16
  br label %eT49
; --- Operator: FSHeT ---
eT49:
  
  %l105 = mul nuw nsw i64 %IReduction_main_i37, 1
  %l106 = add nuw nsw i64 1, %l105
  %l107 = mul nuw nsw i64 2, 1
  %l108 = mul nuw nsw i64 %Union_i47, %l107
  %l109 = add nuw nsw i64 %l106, %l108
  %l102 = getelementptr [5 x double], [5 x double]* %X, i64 0, i64 %l109
  %l104 = load double, double* %l102, align 8
  %l103 = getelementptr [1 x double], [1 x double]* %l98, i64 0, i64 0
  ; void instr 58
  store double %l104, double* %l103, align 8
  br label %eUnion48
; --- Operator: FSHeUnion ---
eUnion48:
  
  %l99 = getelementptr [1 x double], [1 x double]* %l98, i64 0, i64 0
  %l101 = load double, double* %l99, align 8
  %l100 = getelementptr [2 x double], [2 x double]* %l85, i64 0, i64 %Union_i47
  ; void instr 56
  store double %l101, double* %l100, align 8
  br label %Union_lcont46
Union_lcont46:
  
  %Union_loop_next_i112 = add i64 %Union_i47, 1
  %l111 = icmp slt i64 %Union_loop_next_i112, 2
  br i1 %l111, label %Union_loop_loop52, label %BinOp_entry44
; --- Operator: FSHBinOp ---
BinOp_entry44:
  
  %l95 = icmp slt i64 0, 1
  br i1 %l95, label %BinOp_loop45, label %IReduction_fold_loop_entry40
BinOp_loop45:
  %BinOp_i86 = phi i64 [0, %BinOp_entry44], [%BinOp_next_i97, %BinOp_lcont42]
  
  br label %BinOpLoopBody43
BinOpLoopBody43:
  
  %l88 = getelementptr [2 x double], [2 x double]* %l85, i64 0, i64 %BinOp_i86
  %l91 = load double, double* %l88, align 8
  %l87 = add i64 %BinOp_i86, 1
  %l89 = getelementptr [2 x double], [2 x double]* %l85, i64 0, i64 %l87
  %l92 = load double, double* %l89, align 8
  %l93 = fsub double %l91, %l92
  %l94 = call double @llvm.fabs.f64(double %l93)
  %l90 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp75, i64 0, i64 %BinOp_i86
  ; void instr 51
  store double %l94, double* %l90, align 8
  br label %BinOp_lcont42
BinOp_lcont42:
  
  %BinOp_next_i97 = add i64 %BinOp_i86, 1
  %l96 = icmp slt i64 %BinOp_next_i97, 1
  br i1 %l96, label %BinOp_loop45, label %IReduction_fold_loop_entry40
IReduction_fold_loop_entry40:
  
  %l82 = icmp slt i64 0, 1
  br i1 %l82, label %IReduction_fold_loop_loop41, label %IReduction_main_lcont36
IReduction_fold_loop_loop41:
  %IReduction_fold_i80 = phi i64 [0, %IReduction_fold_loop_entry40], [%IReduction_fold_loop_next_i84, %IReduction_fold_lcont39]
  
  br label %IReduction_fold38
IReduction_fold38:
  
  %l76 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp75, i64 0, i64 %IReduction_fold_i80
  %l77 = getelementptr [1 x double], [1 x double]* %l71, i64 0, i64 %IReduction_fold_i80
  %tv78 = load double, double* %l76, align 8
  %yv79 = load double, double* %l77, align 8
  %l81 = call double @llvm.maxnum.f64(double %yv79, double %tv78)
  ; void instr 45
  store double %l81, double* %l77, align 8
  br label %IReduction_fold_lcont39
IReduction_fold_lcont39:
  
  %IReduction_fold_loop_next_i84 = add i64 %IReduction_fold_i80, 1
  %l83 = icmp slt i64 %IReduction_fold_loop_next_i84, 1
  br i1 %l83, label %IReduction_fold_loop_loop41, label %IReduction_main_lcont36
IReduction_main_lcont36:
  
  %IReduction_main_loop_next_i115 = add i64 %IReduction_main_i37, 1
  %l114 = icmp slt i64 %IReduction_main_loop_next_i115, 2
  br i1 %l114, label %IReduction_main_loop_loop55, label %eUnion35
; --- Operator: FSHeUnion ---
eUnion35:
  
  %l72 = getelementptr [1 x double], [1 x double]* %l71, i64 0, i64 0
  %l74 = load double, double* %l72, align 8
  %l73 = getelementptr [2 x double], [2 x double]* %l14, i64 0, i64 1
  ; void instr 44
  store double %l74, double* %l73, align 8
  br label %b34
; --- Operator: FSHCompose ---
b34:
  
  %l25 = alloca [1 x double], align 16
  br label %IReduction_init_loop_entry32
; --- Operator: FSHIReduction ---
IReduction_init_loop_entry32:
  
  %IReductoin_tmp29 = alloca [1 x double], align 16
  %l68 = icmp slt i64 0, 1
  br i1 %l68, label %IReduction_init_loop_loop33, label %IReduction_main_loop_entry28
IReduction_init_loop_loop33:
  %IReduction_init_i67 = phi i64 [0, %IReduction_init_loop_entry32], [%IReduction_init_loop_next_i70, %IReduction_init_lcont31]
  
  br label %IReduction_init30
IReduction_init30:
  
  %l66 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp29, i64 0, i64 %IReduction_init_i67
  ; void instr 38
  store double 0., double* %l66, align 8
  br label %IReduction_init_lcont31
IReduction_init_lcont31:
  
  %IReduction_init_loop_next_i70 = add i64 %IReduction_init_i67, 1
  %l69 = icmp slt i64 %IReduction_init_loop_next_i70, 1
  br i1 %l69, label %IReduction_init_loop_loop33, label %IReduction_main_loop_entry28
IReduction_main_loop_entry28:
  
  %l63 = icmp slt i64 0, 3
  br i1 %l63, label %IReduction_main_loop_loop29, label %eUnion10
IReduction_main_loop_loop29:
  %IReduction_main_i12 = phi i64 [0, %IReduction_main_loop_entry28], [%IReduction_main_loop_next_i65, %IReduction_main_lcont11]
  
  br label %b27
; --- Operator: FSHCompose ---
b27:
  
  %l39 = alloca [1 x double], align 16
  br label %eT26
; --- Operator: FSHeT ---
eT26:
  
  %l60 = getelementptr [5 x double], [5 x double]* %X, i64 0, i64 0
  %l62 = load double, double* %l60, align 8
  %l61 = getelementptr [1 x double], [1 x double]* %l39, i64 0, i64 0
  ; void instr 32
  store double %l62, double* %l61, align 8
  br label %b25
; --- Operator: FSHCompose ---
b25:
  
  %l40 = alloca [1 x double], align 16
  br label %Inductor_entry23
; --- Operator: FSHInductor ---
Inductor_entry23:
  
  %l52 = getelementptr [1 x double], [1 x double]* %l40, i64 0, i64 0
  ; void instr 23
  store double 1., double* %l52, align 8
  %l57 = icmp slt i64 0, %IReduction_main_i12
  br i1 %l57, label %Inductor_loop24, label %Pointwise_entry19
Inductor_loop24:
  %Inductor_i51 = phi i64 [0, %Inductor_entry23], [%Inductor_next_i59, %Inductor_lcont21]
  
  br label %InductorLoopBody22
InductorLoopBody22:
  
  %l53 = getelementptr [1 x double], [1 x double]* %l39, i64 0, i64 0
  %l54 = load double, double* %l52, align 8
  %l55 = load double, double* %l53, align 8
  %l56 = fmul double %l55, %l54
  ; void instr 25
  store double %l56, double* %l52, align 8
  br label %Inductor_lcont21
Inductor_lcont21:
  
  %Inductor_next_i59 = add i64 %Inductor_i51, 1
  %l58 = icmp slt i64 %Inductor_next_i59, %IReduction_main_i12
  br i1 %l58, label %Inductor_loop24, label %Pointwise_entry19
; --- Operator: FSHPointwise ---
Pointwise_entry19:
  
  %l48 = icmp slt i64 0, 1
  br i1 %l48, label %Pointwise_loop20, label %IReduction_fold_loop_entry15
Pointwise_loop20:
  %Pointwise_i41 = phi i64 [0, %Pointwise_entry19], [%Pointwise_next_i50, %Pointwise_lcont17]
  
  br label %PointwiseLoopBody18
PointwiseLoopBody18:
  
  %l42 = getelementptr [1 x double], [1 x double]* %l40, i64 0, i64 %Pointwise_i41
  %l44 = load double, double* %l42, align 8
  %l45 = getelementptr [3 x double], [3 x double]* @D, i64 0, i64 %IReduction_main_i12
  %l46 = load double, double* %l45, align 8
  %l47 = fmul double %l44, %l46
  %l43 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp29, i64 0, i64 %Pointwise_i41
  ; void instr 19
  store double %l47, double* %l43, align 8
  br label %Pointwise_lcont17
Pointwise_lcont17:
  
  %Pointwise_next_i50 = add i64 %Pointwise_i41, 1
  %l49 = icmp slt i64 %Pointwise_next_i50, 1
  br i1 %l49, label %Pointwise_loop20, label %IReduction_fold_loop_entry15
IReduction_fold_loop_entry15:
  
  %l36 = icmp slt i64 0, 1
  br i1 %l36, label %IReduction_fold_loop_loop16, label %IReduction_main_lcont11
IReduction_fold_loop_loop16:
  %IReduction_fold_i34 = phi i64 [0, %IReduction_fold_loop_entry15], [%IReduction_fold_loop_next_i38, %IReduction_fold_lcont14]
  
  br label %IReduction_fold13
IReduction_fold13:
  
  %l30 = getelementptr [1 x double], [1 x double]* %IReductoin_tmp29, i64 0, i64 %IReduction_fold_i34
  %l31 = getelementptr [1 x double], [1 x double]* %l25, i64 0, i64 %IReduction_fold_i34
  %tv32 = load double, double* %l30, align 8
  %yv33 = load double, double* %l31, align 8
  %l35 = fadd double %yv33, %tv32
  ; void instr 13
  store double %l35, double* %l31, align 8
  br label %IReduction_fold_lcont14
IReduction_fold_lcont14:
  
  %IReduction_fold_loop_next_i38 = add i64 %IReduction_fold_i34, 1
  %l37 = icmp slt i64 %IReduction_fold_loop_next_i38, 1
  br i1 %l37, label %IReduction_fold_loop_loop16, label %IReduction_main_lcont11
IReduction_main_lcont11:
  
  %IReduction_main_loop_next_i65 = add i64 %IReduction_main_i12, 1
  %l64 = icmp slt i64 %IReduction_main_loop_next_i65, 3
  br i1 %l64, label %IReduction_main_loop_loop29, label %eUnion10
; --- Operator: FSHeUnion ---
eUnion10:
  
  %l26 = getelementptr [1 x double], [1 x double]* %l25, i64 0, i64 0
  %l28 = load double, double* %l26, align 8
  %l27 = getelementptr [2 x double], [2 x double]* %l13, i64 0, i64 0
  ; void instr 12
  store double %l28, double* %l27, align 8
  br label %HTSUMUnion_entry8
HTSUMUnion_entry8:
  
  %l22 = icmp slt i64 0, 2
  br i1 %l22, label %HTSUMUnion_loop9, label %BinOp_entry4
HTSUMUnion_loop9:
  %HTSUMUnion_i15 = phi i64 [0, %HTSUMUnion_entry8], [%HTSUMUnion_next_i24, %HTSUMUnion_lcont6]
  
  br label %genHTSUMUnionpBody7
genHTSUMUnionpBody7:
  
  %l16 = getelementptr [2 x double], [2 x double]* %l13, i64 0, i64 %HTSUMUnion_i15
  %l19 = load double, double* %l16, align 8
  %l17 = getelementptr [2 x double], [2 x double]* %l14, i64 0, i64 %HTSUMUnion_i15
  %l20 = load double, double* %l17, align 8
  %l21 = fadd double %l20, %l19
  %l18 = getelementptr [2 x double], [2 x double]* %l0, i64 0, i64 %HTSUMUnion_i15
  ; void instr 7
  store double %l21, double* %l18, align 8
  br label %HTSUMUnion_lcont6
HTSUMUnion_lcont6:
  
  %HTSUMUnion_next_i24 = add i64 %HTSUMUnion_i15, 1
  %l23 = icmp slt i64 %HTSUMUnion_next_i24, 2
  br i1 %l23, label %HTSUMUnion_loop9, label %BinOp_entry4
; --- Operator: FSHBinOp ---
BinOp_entry4:
  
  %l10 = icmp slt i64 0, 1
  br i1 %l10, label %BinOp_loop5, label %b0
BinOp_loop5:
  %BinOp_i1 = phi i64 [0, %BinOp_entry4], [%BinOp_next_i12, %BinOp_lcont2]
  
  br label %BinOpLoopBody3
BinOpLoopBody3:
  
  %l3 = getelementptr [2 x double], [2 x double]* %l0, i64 0, i64 %BinOp_i1
  %l6 = load double, double* %l3, align 8
  %l2 = add i64 %BinOp_i1, 1
  %l4 = getelementptr [2 x double], [2 x double]* %l0, i64 0, i64 %l2
  %l7 = load double, double* %l4, align 8
  %l8 = fcmp olt double %l6, %l7
  ; void instr 2
  ; Cast bool to float
  %l9 = uitofp i1 %l8 to double
  %l5 = getelementptr [1 x double], [1 x double]* %Y, i64 0, i64 %BinOp_i1
  ; void instr 1
  store double %l9, double* %l5, align 8
  br label %BinOp_lcont2
BinOp_lcont2:
  
  %BinOp_next_i12 = add i64 %BinOp_i1, 1
  %l11 = icmp slt i64 %BinOp_next_i12, 1
  br i1 %l11, label %BinOp_loop5, label %b0
b0:
  
  
  ret void
}
;  X data
@X = constant [5 x double] [double -229015563.992, double 244847285.666, double 239613514.765, double 302526799.931, double 69233830.4328]
;  Main function
define [1 x double] @main() {
main_block:
  
  %Y = alloca [1 x double], align 16
  ; void instr 0
  call void @dynwin64([5 x double]* @X, [1 x double]* %Y)
  %z = load [1 x double], [1 x double]* %Y
  ret [1 x double] %z
}
