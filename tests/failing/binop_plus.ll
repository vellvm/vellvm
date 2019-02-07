; Global variables
; Prototypes for intrinsics we use
declare void @llvm.memcpy.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)
declare float @llvm.maxnum.f32(float, float)
declare double @llvm.maxnum.f64(double, double)
declare float @llvm.fabs.f32(float)
declare double @llvm.fabs.f64(double)
;  Top-level operator definition
define void @binop_plus([4 x double]* readonly align 16 nonnull %X, [2 x double]* align 16 nonnull %Y) {
; --- Operator: FSHBinOp ---
BinOp_entry4:
  
  %l8 = icmp slt i64 0, 2
  br i1 %l8, label %BinOp_loop5, label %b0
BinOp_loop5:
  %BinOp_i0 = phi i64 [0, %BinOp_entry4], [%BinOp_next_i10, %BinOp_lcont2]
  
  br label %BinOpLoopBody3
BinOpLoopBody3:
  
  %l2 = getelementptr [4 x double], [4 x double]* %X, i64 0, i64 %BinOp_i0
  %l5 = load double, double* %l2, align 8
  %l1 = add i64 %BinOp_i0, 2
  %l3 = getelementptr [4 x double], [4 x double]* %X, i64 0, i64 %l1
  %l6 = load double, double* %l3, align 8
  %l7 = fadd double %l5, %l6
  %l4 = getelementptr [2 x double], [2 x double]* %Y, i64 0, i64 %BinOp_i0
  ; void instr 1
  store double %l7, double* %l4, align 8
  br label %BinOp_lcont2
BinOp_lcont2:
  
  %BinOp_next_i10 = add i64 %BinOp_i0, 1
  %l9 = icmp slt i64 %BinOp_next_i10, 2
  br i1 %l9, label %BinOp_loop5, label %b0
b0:
  
  
  ret void
}
;  X data
@X = constant [4 x double] [double 1.1, double 2.2, double 3.3, double 4.4]
;  Main function
define [2 x double] @main() {
main_block:
  
  %Y = alloca [2 x double], align 16
  ; void instr 0
  call void @binop_plus([4 x double]* @X, [2 x double]* %Y)
  %z = load [2 x double], [2 x double]* %Y
  ret [2 x double] %z
}
