; Global variables
@D = global [3 x double] [double 1.0, double 2.0, double 3.0], align 16
; Prototypes for intrinsics we use
declare float @llvm.fabs.f32(float)
declare double @llvm.fabs.f64(double)
declare float @llvm.maxnum.f32(float, float)
declare double @llvm.maxnum.f64(double, double)
declare float @minimum.f32(float, float)
declare double @llvm.minimum.f64(double, double)
declare void @llvm.memcpy.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)
; Top-level operator definition
define void @dynwin64([5 x double]* readonly align 16 nonnull %X, [1 x double]* align 16 nonnull %Y) {
; --- Operator: DSHAlloc 2---
b56:
  
  %a0 = alloca [2 x double], align 16
  br label %b55
; --- Operator: DSHAlloc 1---
; --- Operator: DSHSeq---
; --- Operator: DSHSeq---
b55:
  
  %a66 = alloca [1 x double], align 16
  br label %b54
; --- Operator: DSHAlloc 1---
; --- Operator: DSHSeq---
b54:
  
  %a70 = alloca [1 x double], align 16
  br label %MemInit_loop_entry52
; --- Operator: DSHMemInit (PVar 0) ...---
; --- Operator: DSHSeq---
MemInit_loop_entry52:
  
  %l111 = icmp slt i64 0, 1
  br i1 %l111, label %MemInit_loop_loop53, label %Loop_loop_entry48
MemInit_loop_loop53:
  %MemInit_init_i110 = phi i64 [0, %MemInit_loop_entry52], [%MemInit_loop_next_i113, %MemInit_init_lcont51]
  
  br label %MemInit_init50
MemInit_init50:
  
  %l109 = getelementptr [1 x double], [1 x double]* %a70, i64 0, i64 %MemInit_init_i110
  ; void instr 64
  store double 0x0, double* %l109, align 8
  br label %MemInit_init_lcont51
MemInit_init_lcont51:
  
  %MemInit_loop_next_i113 = add i64 %MemInit_init_i110, 1
  %l112 = icmp slt i64 %MemInit_loop_next_i113, 1
  br i1 %l112, label %MemInit_loop_loop53, label %Loop_loop_entry48
; --- Operator: DSHLoop 3 ---
Loop_loop_entry48:
  
  %l106 = icmp slt i64 0, 3
  br i1 %l106, label %Loop_loop_loop49, label %Assign31
Loop_loop_loop49:
  %Loop_i71 = phi i64 [0, %Loop_loop_entry48], [%Loop_loop_next_i108, %Loop_lcont32]
  
  br label %b47
; --- Operator: DSHAlloc 1---
; --- Operator: DSHSeq---
b47:
  
  %a82 = alloca [1 x double], align 16
  br label %Assign46
; --- Operator: DSHAssign ((PVar 7),0) ((PVar 0),0) ---
; --- Operator: DSHSeq---
Assign46:
  
  %l103 = getelementptr [3 x double], [3 x double]* @D, i64 0, i64 0
  %l105 = load double, double* %l103, align 8
  %l104 = getelementptr [1 x double], [1 x double]* %a82, i64 0, i64 0
  ; void instr 58
  store double %l105, double* %l104, align 8
  br label %b45
; --- Operator: DSHAlloc 1---
b45:
  
  %a83 = alloca [1 x double], align 16
  br label %Power_entry43
; --- Operator: DSHPower (NVar 2) ((PVar 1),0) ((PVar 0),0)...---
; --- Operator: DSHSeq---
Power_entry43:
  
  %l95 = getelementptr [1 x double], [1 x double]* %a83, i64 0, i64 0
  ; void instr 49
  store double 0x3FF0000000000000, double* %l95, align 8
  %l100 = icmp slt i64 0, %Loop_i71
  br i1 %l100, label %Power_loop44, label %IMap_entry39
Power_loop44:
  %Power_i94 = phi i64 [0, %Power_entry43], [%Power_next_i102, %Power_lcont41]
  
  br label %PowerLoopBody42
PowerLoopBody42:
  
  %l96 = getelementptr [1 x double], [1 x double]* %a82, i64 0, i64 0
  %l98 = load double, double* %l96, align 8
  %l97 = load double, double* %l95, align 8
  %l99 = fmul double %l97, %l98
  ; void instr 51
  store double %l99, double* %l95, align 8
  br label %Power_lcont41
Power_lcont41:
  
  %Power_next_i102 = add i64 %Power_i94, 1
  %l101 = icmp slt i64 %Power_next_i102, %Loop_i71
  br i1 %l101, label %Power_loop44, label %IMap_entry39
; --- Operator: DSHIMap 1 (PVar 0) (PVar 4) ...---
IMap_entry39:
  
  %l91 = icmp slt i64 0, 1
  br i1 %l91, label %IMap_loop40, label %MemMap2_entry35
IMap_loop40:
  %IMap_i84 = phi i64 [0, %IMap_entry39], [%IMap_next_i93, %IMap_lcont37]
  
  br label %IMapLoopBody38
IMapLoopBody38:
  
  %l85 = getelementptr [1 x double], [1 x double]* %a83, i64 0, i64 %IMap_i84
  %l87 = load double, double* %l85, align 8
  %l88 = getelementptr [1 x double], [1 x double]* %Y, i64 0, i64 %Loop_i71
  %l89 = load double, double* %l88, align 8
  %l90 = fmul double %l87, %l89
  %l86 = getelementptr [1 x double], [1 x double]* %a66, i64 0, i64 %IMap_i84
  ; void instr 45
  store double %l90, double* %l86, align 8
  br label %IMap_lcont37
IMap_lcont37:
  
  %IMap_next_i93 = add i64 %IMap_i84, 1
  %l92 = icmp slt i64 %IMap_next_i93, 1
  br i1 %l92, label %IMap_loop40, label %MemMap2_entry35
; --- Operator: DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2) ...---
MemMap2_entry35:
  
  %l79 = icmp slt i64 0, 1
  br i1 %l79, label %MemMap2_loop36, label %Loop_lcont32
MemMap2_loop36:
  %MemMap2_i72 = phi i64 [0, %MemMap2_entry35], [%MemMap2_next_i81, %MemMap2_lcont33]
  
  br label %MemMap2LoopBody34
MemMap2LoopBody34:
  
  %l73 = getelementptr [1 x double], [1 x double]* %a70, i64 0, i64 %MemMap2_i72
  %l76 = load double, double* %l73, align 8
  %l74 = getelementptr [1 x double], [1 x double]* %a66, i64 0, i64 %MemMap2_i72
  %l77 = load double, double* %l74, align 8
  %l78 = fadd double %l76, %l77
  %l75 = getelementptr [1 x double], [1 x double]* %a66, i64 0, i64 %MemMap2_i72
  ; void instr 40
  store double %l78, double* %l75, align 8
  br label %MemMap2_lcont33
MemMap2_lcont33:
  
  %MemMap2_next_i81 = add i64 %MemMap2_i72, 1
  %l80 = icmp slt i64 %MemMap2_next_i81, 1
  br i1 %l80, label %MemMap2_loop36, label %Loop_lcont32
Loop_lcont32:
  
  %Loop_loop_next_i108 = add i64 %Loop_i71, 1
  %l107 = icmp slt i64 %Loop_loop_next_i108, 3
  br i1 %l107, label %Loop_loop_loop49, label %Assign31
; --- Operator: DSHAssign ((PVar 0),0) ((PVar 1),0) ---
Assign31:
  
  %l67 = getelementptr [1 x double], [1 x double]* %a66, i64 0, i64 0
  %l69 = load double, double* %l67, align 8
  %l68 = getelementptr [2 x double], [2 x double]* %a0, i64 0, i64 0
  ; void instr 38
  store double %l69, double* %l68, align 8
  br label %b30
; --- Operator: DSHAlloc 1---
b30:
  
  %a13 = alloca [1 x double], align 16
  br label %b29
; --- Operator: DSHAlloc 1---
; --- Operator: DSHSeq---
b29:
  
  %a17 = alloca [1 x double], align 16
  br label %MemInit_loop_entry27
; --- Operator: DSHMemInit (PVar 0) ...---
; --- Operator: DSHSeq---
MemInit_loop_entry27:
  
  %l63 = icmp slt i64 0, 1
  br i1 %l63, label %MemInit_loop_loop28, label %Loop_loop_entry23
MemInit_loop_loop28:
  %MemInit_init_i62 = phi i64 [0, %MemInit_loop_entry27], [%MemInit_loop_next_i65, %MemInit_init_lcont26]
  
  br label %MemInit_init25
MemInit_init25:
  
  %l61 = getelementptr [1 x double], [1 x double]* %a17, i64 0, i64 %MemInit_init_i62
  ; void instr 31
  store double 0x0, double* %l61, align 8
  br label %MemInit_init_lcont26
MemInit_init_lcont26:
  
  %MemInit_loop_next_i65 = add i64 %MemInit_init_i62, 1
  %l64 = icmp slt i64 %MemInit_loop_next_i65, 1
  br i1 %l64, label %MemInit_loop_loop28, label %Loop_loop_entry23
; --- Operator: DSHLoop 2 ---
Loop_loop_entry23:
  
  %l58 = icmp slt i64 0, 2
  br i1 %l58, label %Loop_loop_loop24, label %Assign6
Loop_loop_loop24:
  %Loop_i18 = phi i64 [0, %Loop_loop_entry23], [%Loop_loop_next_i60, %Loop_lcont7]
  
  br label %b22
; --- Operator: DSHAlloc 2---
; --- Operator: DSHSeq---
b22:
  
  %a29 = alloca [2 x double], align 16
  br label %Loop_loop_entry20
; --- Operator: DSHLoop 2 ---
; --- Operator: DSHSeq---
Loop_loop_entry20:
  
  %l55 = icmp slt i64 0, 2
  br i1 %l55, label %Loop_loop_loop21, label %BinOp_entry14
Loop_loop_loop21:
  %Loop_i42 = phi i64 [0, %Loop_loop_entry20], [%Loop_loop_next_i57, %Loop_lcont16]
  
  br label %b19
; --- Operator: DSHAlloc 1---
b19:
  
  %a43 = alloca [1 x double], align 16
  br label %Assign18
; --- Operator: DSHAssign ((PVar 9),?) ((PVar 0),0) ---
; --- Operator: DSHSeq---
Assign18:
  
  %l50 = mul i64 %Loop_i18, 1
  %l51 = add i64 1, %l50
  %l52 = mul i64 2, 1
  %l53 = mul i64 %Loop_i42, %l52
  %l54 = add i64 %l51, %l53
  %l47 = getelementptr [3 x double], [3 x double]* @D, i64 0, i64 %l54
  %l49 = load double, double* %l47, align 8
  %l48 = getelementptr [1 x double], [1 x double]* %a43, i64 0, i64 0
  ; void instr 21
  store double %l49, double* %l48, align 8
  br label %Assign17
; --- Operator: DSHAssign ((PVar 0),0) ((PVar 2),(NVar 1)) ---
Assign17:
  
  %l44 = getelementptr [1 x double], [1 x double]* %a43, i64 0, i64 0
  %l46 = load double, double* %l44, align 8
  %l45 = getelementptr [2 x double], [2 x double]* %a29, i64 0, i64 %Loop_i42
  ; void instr 19
  store double %l46, double* %l45, align 8
  br label %Loop_lcont16
Loop_lcont16:
  
  %Loop_loop_next_i57 = add i64 %Loop_i42, 1
  %l56 = icmp slt i64 %Loop_loop_next_i57, 2
  br i1 %l56, label %Loop_loop_loop21, label %BinOp_entry14
; --- Operator: DSHBinOp 1 (PVar 0) (PVar 3) ...---
BinOp_entry14:
  
  %l39 = icmp slt i64 0, 1
  br i1 %l39, label %BinOp_loop15, label %MemMap2_entry10
BinOp_loop15:
  %BinOp_i30 = phi i64 [0, %BinOp_entry14], [%BinOp_next_i41, %BinOp_lcont12]
  
  br label %BinOpLoopBody13
BinOpLoopBody13:
  
  %l32 = getelementptr [2 x double], [2 x double]* %a29, i64 0, i64 %BinOp_i30
  %l35 = load double, double* %l32, align 8
  %l31 = add i64 %BinOp_i30, 1
  %l33 = getelementptr [2 x double], [2 x double]* %a29, i64 0, i64 %l31
  %l36 = load double, double* %l33, align 8
  %l37 = fsub double %l35, %l36
  %l38 = call double @llvm.fabs.f64(double %l37)
  %l34 = getelementptr [1 x double], [1 x double]* %a13, i64 0, i64 %BinOp_i30
  ; void instr 14
  store double %l38, double* %l34, align 8
  br label %BinOp_lcont12
BinOp_lcont12:
  
  %BinOp_next_i41 = add i64 %BinOp_i30, 1
  %l40 = icmp slt i64 %BinOp_next_i41, 1
  br i1 %l40, label %BinOp_loop15, label %MemMap2_entry10
; --- Operator: DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2) ...---
MemMap2_entry10:
  
  %l26 = icmp slt i64 0, 1
  br i1 %l26, label %MemMap2_loop11, label %Loop_lcont7
MemMap2_loop11:
  %MemMap2_i19 = phi i64 [0, %MemMap2_entry10], [%MemMap2_next_i28, %MemMap2_lcont8]
  
  br label %MemMap2LoopBody9
MemMap2LoopBody9:
  
  %l20 = getelementptr [1 x double], [1 x double]* %a17, i64 0, i64 %MemMap2_i19
  %l23 = load double, double* %l20, align 8
  %l21 = getelementptr [1 x double], [1 x double]* %a13, i64 0, i64 %MemMap2_i19
  %l24 = load double, double* %l21, align 8
  %l25 = call double @llvm.maxnum.f64(double %l23, double %l24)
  %l22 = getelementptr [1 x double], [1 x double]* %a13, i64 0, i64 %MemMap2_i19
  ; void instr 9
  store double %l25, double* %l22, align 8
  br label %MemMap2_lcont8
MemMap2_lcont8:
  
  %MemMap2_next_i28 = add i64 %MemMap2_i19, 1
  %l27 = icmp slt i64 %MemMap2_next_i28, 1
  br i1 %l27, label %MemMap2_loop11, label %Loop_lcont7
Loop_lcont7:
  
  %Loop_loop_next_i60 = add i64 %Loop_i18, 1
  %l59 = icmp slt i64 %Loop_loop_next_i60, 2
  br i1 %l59, label %Loop_loop_loop24, label %Assign6
; --- Operator: DSHAssign ((PVar 0),0) ((PVar 1),1) ---
Assign6:
  
  %l14 = getelementptr [1 x double], [1 x double]* %a13, i64 0, i64 0
  %l16 = load double, double* %l14, align 8
  %l15 = getelementptr [2 x double], [2 x double]* %a0, i64 0, i64 1
  ; void instr 7
  store double %l16, double* %l15, align 8
  br label %BinOp_entry4
; --- Operator: DSHBinOp 1 (PVar 0) (PVar 2) ...---
BinOp_entry4:
  
  %l10 = icmp slt i64 0, 1
  br i1 %l10, label %BinOp_loop5, label %b0
BinOp_loop5:
  %BinOp_i1 = phi i64 [0, %BinOp_entry4], [%BinOp_next_i12, %BinOp_lcont2]
  
  br label %BinOpLoopBody3
BinOpLoopBody3:
  
  %l3 = getelementptr [2 x double], [2 x double]* %a0, i64 0, i64 %BinOp_i1
  %l6 = load double, double* %l3, align 8
  %l2 = add i64 %BinOp_i1, 1
  %l4 = getelementptr [2 x double], [2 x double]* %a0, i64 0, i64 %l2
  %l7 = load double, double* %l4, align 8
  %l8 = fcmp olt double %l6, %l7
  ; void instr 2
  ; Casting bool to float
  %l9 = uitofp i1 %l8 to double
  %l5 = getelementptr [5 x double], [5 x double]* %X, i64 0, i64 %BinOp_i1
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


@IN = global [5 x double] [double 1.0, double 2.0, double 3.0, double 4.0, double 5.0], align 16
@OUT = global [1 x double] [double 0.0], align 16

define double @test() {
  call void @dynwin64([5 x double]* @IN, [1 x double]* @OUT)
  %ptr = getelementptr [1 x double], [1 x double]* @OUT, i64 0, i64 0
  %ans = load double, double* %ptr
  ret double %ans
}

define i32 @main(i64 %argc, i8** %arcv) {
  call void @dynwin64([5 x double]* @IN, [1 x double]* @OUT)
  ret i32 0
}

; ASSERT EQ: double 0.0 = call double @test()
