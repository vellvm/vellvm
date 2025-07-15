; ModuleID = 'example.81b56bf8d265fdf5-cgu.0'
source_filename = "example.81b56bf8d265fdf5-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_9be5c135c0f7c91e35e471f025924b11 = private unnamed_addr constant [15 x i8] c"/app/example.rs", align 1
@alloc_da5cf958710295b96b156e93b9bd4d46 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9be5c135c0f7c91e35e471f025924b11, [16 x i8] c"\0F\00\00\00\00\00\00\00\0B\00\00\00\05\00\00\00" }>, align 8

; Function Attrs: nonlazybind uwtable
define i32 @square(i32 %num) unnamed_addr #0 !dbg !7 {
start:
  %num.dbg.spill = alloca [4 x i8], align 4
  store i32 %num, ptr %num.dbg.spill, align 4
    #dbg_declare(ptr %num.dbg.spill, !14, !DIExpression(), !16)
  %0 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %num, i32 %num), !dbg !17
  %_2.0 = extractvalue { i32, i1 } %0, 0, !dbg !17
  %_2.1 = extractvalue { i32, i1 } %0, 1, !dbg !17
  br i1 %_2.1, label %panic, label %bb1, !dbg !17

bb1:                                              ; preds = %start
  ret i32 %_2.0, !dbg !18

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @core::panicking::panic_const::panic_const_mul_overflow::h0c89a1ab8bb38613(ptr align 8 @alloc_da5cf958710295b96b156e93b9bd4d46) #3, !dbg !17
  unreachable, !dbg !17
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @core::panicking::panic_const::panic_const_mul_overflow::h0c89a1ab8bb38613(ptr align 8) unnamed_addr #2

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
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
!7 = distinct !DISubprogram(name: "square", scope: !9, file: !8, line: 10, type: !10, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !15, retainedNodes: !13)
!8 = !DIFile(filename: "example.rs", directory: "/app", checksumkind: CSK_MD5, checksum: "ceda14a2d889d95f49e3fe2ba48e9536")
!9 = !DINamespace(name: "example", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14}
!14 = !DILocalVariable(name: "num", arg: 1, scope: !7, file: !8, line: 10, type: !12)
!15 = !{}
!16 = !DILocation(line: 10, column: 15, scope: !7)
!17 = !DILocation(line: 11, column: 5, scope: !7)
!18 = !DILocation(line: 12, column: 2, scope: !7)
