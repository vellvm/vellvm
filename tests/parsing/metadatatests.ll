@vtable.0 = private unnamed_addr constant <{ ptr, [16 x i8], ptr, ptr, ptr }> <{ ptr @"_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h196226712f618a69E", [16 x i8] c"\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h66ac8c8cfdead3faE", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E" }>, align 8, !dbg !0


define i32 @square(i32 %num, i32 %"xay\0\0") unnamed_addr !dbg !0 {
start:
  %num.dbg.spill = alloca [4 x i8], align 4, !dbg !0
  ret i32 4
}

define void @foo() {
  %1 = alloca i32
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  call void @llvm.dbg.value(metadata !24, metadata !25, metadata !26)  
  call void @llvm.dbg.value(metadata !24, metadata !25, metadata !26)
  call void @llvm.dbg.value(metadata ! 24, metadata !25, metadata ! {!{! {! 26, !25, !{ptr null}}}})  
  %2 = alloca i8*
  %self19.i.i.i.i.i.i = load i8*, i8** %2, align 8, !alias.scope !9, !noalias !15, !nonnull !4
  call void @llvm.dbg.declare(metadata {}* %1, metadata !9, metadata i32 0)
ret void
}  

!foo = !{!0}
!0 = !DILocation(line: 11, column: 5, scope: !7)
!7 = !{i32 17}
!4 = !{}
!9 = !{}
!15 = !{}
! 24 = !{}
!25 = ! {}
!26 = !{}
!30 = !{!"blabaskl", null, !0}
!1 = !{i32 42, null, !"string"}
!2 = distinct !{!7, !1, !{}}
!nontemporal = !{}
