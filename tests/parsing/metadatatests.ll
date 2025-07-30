define i32 @square(i32 %num) unnamed_addr #0 !dbg !1 {
start:
  %num.dbg.spill = alloca [4 x i8], align 4, !dbg !1
  ret i32 4
}

define void @foo() {
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7) #14
  ret void
}  

!1 = !DILocation(line: 11, column: 5, scope: !7)
!7 = !{}
