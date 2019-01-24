; Global variables
; Prototypes for intrinsics we use
declare void @llvm.memcpy.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)
declare float @llvm.maxnum.f32(float, float)
declare double @llvm.maxnum.f64(double, double)
declare float @llvm.fabs.f32(float)
declare double @llvm.fabs.f64(double)
;  Top-level operator definition
define void @sumunion([4 x double]* readonly align 16 nonnull %X, [4 x double]* align 16 nonnull %Y) {
; --- Operator: FSHHTSUMUnion ---
b8:
  
  %l0 = alloca [4 x double], align 16
  %l1 = alloca [4 x double], align 16
  br label %ID7
; --- Operator: FSHId ---
ID7:
  
  %l14 = bitcast [4 x double]* %X to i8*
  %l15 = bitcast [4 x double]* %l1 to i8*
  ; void instr 8
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %l15, i8* %l14, i32 32, i32 16, i1 0)
  br label %ID6
; --- Operator: FSHId ---
ID6:
  
  %l12 = bitcast [4 x double]* %X to i8*
  %l13 = bitcast [4 x double]* %l0 to i8*
  ; void instr 6
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %l13, i8* %l12, i32 32, i32 16, i1 0)
  br label %HTSUMUnion_entry4
HTSUMUnion_entry4:
  
  %l9 = icmp slt i64 0, 4
  br i1 %l9, label %HTSUMUnion_loop5, label %b0
HTSUMUnion_loop5:
  %HTSUMUnion_i2 = phi i64 [0, %HTSUMUnion_entry4], [%HTSUMUnion_next_i11, %HTSUMUnion_lcont2]
  
  br label %genHTSUMUnionpBody3
genHTSUMUnionpBody3:
  
  %l3 = getelementptr [4 x double], [4 x double]* %l0, i64 0, i64 %HTSUMUnion_i2
  %l6 = load double, double* %l3, align 8
  %l4 = getelementptr [4 x double], [4 x double]* %l1, i64 0, i64 %HTSUMUnion_i2
  %l7 = load double, double* %l4, align 8
  %l8 = fadd double %l7, %l6
  %l5 = getelementptr [4 x double], [4 x double]* %Y, i64 0, i64 %HTSUMUnion_i2
  ; void instr 1
  store double %l8, double* %l5, align 8
  br label %HTSUMUnion_lcont2
HTSUMUnion_lcont2:
  
  %HTSUMUnion_next_i11 = add i64 %HTSUMUnion_i2, 1
  %l10 = icmp slt i64 %HTSUMUnion_next_i11, 4
  br i1 %l10, label %HTSUMUnion_loop5, label %b0
b0:
  
  
  ret void
}
;  X data
@X = constant [4 x double] [double 10.0, double 20.0, double 1.0, double 2.0]
;  Main function
define [4 x double] @main() {
main_block:
  
  %Y = alloca [4 x double], align 16
  ; void instr 0
  call void @sumunion([4 x double]* @X, [4 x double]* %Y)
  %z = load [4 x double], [4 x double]* %Y
  ret [4 x double] %z
}
