; ModuleID = 'example.81b56bf8d265fdf5-cgu.0'
source_filename = "example.81b56bf8d265fdf5-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_9be5c135c0f7c91e35e471f025924b11 = private unnamed_addr constant [15 x i8] c"/app/example.rs", align 1
@alloc_62c0299f65c2f827fece334dbdc8f31e = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9be5c135c0f7c91e35e471f025924b11, [16 x i8] c"\0F\00\00\00\00\00\00\00\0B\00\00\00/\00\00\00" }>, align 8
@alloc_308c12cf9ccd7ddedc06a22e27c7e733 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9be5c135c0f7c91e35e471f025924b11, [16 x i8] c"\0F\00\00\00\00\00\00\00\0B\00\00\00\1E\00\00\00" }>, align 8

; Function Attrs: nonlazybind uwtable
define i32 @factorial(i32 %num) unnamed_addr #0 !dbg !7 {
start:
  %num.dbg.spill = alloca [4 x i8], align 4
  %_0 = alloca [4 x i8], align 4
  store i32 %num, ptr %num.dbg.spill, align 4
    #dbg_declare(ptr %num.dbg.spill, !14, !DIExpression(), !16)
  %0 = icmp eq i32 %num, 0, !dbg !17
  br i1 %0, label %bb1, label %bb2, !dbg !17

bb1:                                              ; preds = %start
  store i32 1, ptr %_0, align 4, !dbg !18
  br label %bb6, !dbg !19

bb2:                                              ; preds = %start
  %_4.0 = sub i32 %num, 1, !dbg !20
  %_4.1 = icmp ult i32 %num, 1, !dbg !20
  br i1 %_4.1, label %panic, label %bb3, !dbg !20

bb6:                                              ; preds = %bb5, %bb1
  %1 = load i32, ptr %_0, align 4, !dbg !21
  ret i32 %1, !dbg !21

bb3:                                              ; preds = %bb2
  %_2 = call i32 @factorial(i32 %_4.0), !dbg !22
  %2 = call { i32, i1 } @llvm.umul.with.overflow.i32(i32 %num, i32 %_2), !dbg !23
  %_5.0 = extractvalue { i32, i1 } %2, 0, !dbg !23
  %_5.1 = extractvalue { i32, i1 } %2, 1, !dbg !23
  br i1 %_5.1, label %panic1, label %bb5, !dbg !23

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h91779a4adcb9aa93E(ptr align 8 @alloc_62c0299f65c2f827fece334dbdc8f31e) #3, !dbg !20
  unreachable, !dbg !20

bb5:                                              ; preds = %bb3
  store i32 %_5.0, ptr %_0, align 4, !dbg !23
  br label %bb6, !dbg !19

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_mul_overflow17h0c89a1ab8bb38613E(ptr align 8 @alloc_308c12cf9ccd7ddedc06a22e27c7e733) #3, !dbg !23
  unreachable, !dbg !23
}

; example::main
; Function Attrs: nonlazybind uwtable
define i32 @main() unnamed_addr #0 !dbg !24 {
start:
  %_1 = call i32 @factorial(i32 5), !dbg !27
  ret i32 %_1
}

; core::panicking::panic_const::panic_const_sub_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h91779a4adcb9aa93E(ptr align 8) unnamed_addr #1

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.umul.with.overflow.i32(i32, i32) #2

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_ZN4core9panicking11panic_const24panic_const_mul_overflow17h0c89a1ab8bb38613E(ptr align 8) unnamed_addr #1

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #3 = { noreturn }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!llvm.dbg.cu = !{!5}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"Dwarf Version", i32 4}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{!"rustc version 1.88.0 (6b00bc388 2025-06-23)"}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6, producer: "clang LLVM (rustc version 1.88.0 (6b00bc388 2025-06-23))", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!6 = !DIFile(filename: "/app/example.rs/@/example.81b56bf8d265fdf5-cgu.0", directory: "/app")
!7 = distinct !DISubprogram(name: "factorial", scope: !9, file: !8, line: 10, type: !10, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !15, retainedNodes: !13)
!8 = !DIFile(filename: "example.rs", directory: "/app", checksumkind: CSK_MD5, checksum: "04439fe69a22bb1bab61d25912d1a284")
!9 = !DINamespace(name: "example", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12}
!12 = !DIBasicType(name: "u32", size: 32, encoding: DW_ATE_unsigned)
!13 = !{!14}
!14 = !DILocalVariable(name: "num", arg: 1, scope: !7, file: !8, line: 10, type: !12)
!15 = !{}
!16 = !DILocation(line: 10, column: 18, scope: !7)
!17 = !DILocation(line: 11, column: 8, scope: !7)
!18 = !DILocation(line: 11, column: 19, scope: !7)
!19 = !DILocation(line: 11, column: 5, scope: !7)
!20 = !DILocation(line: 11, column: 47, scope: !7)
!21 = !DILocation(line: 12, column: 2, scope: !7)
!22 = !DILocation(line: 11, column: 36, scope: !7)
!23 = !DILocation(line: 11, column: 30, scope: !7)
!24 = distinct !DISubprogram(name: "main", linkageName: "_ZN7example4main17hdc436770f0aefb4cE", scope: !9, file: !8, line: 14, type: !25, scopeLine: 14, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !15)
!25 = !DISubroutineType(types: !26)
!26 = !{null}
!27 = !DILocation(line: 15, column: 3, scope: !24)
!28 = !DILocation(line: 16, column: 2, scope: !24)

; ASSERT EQ: i32 120 = call i32 @main(i64 0, i8** null)
