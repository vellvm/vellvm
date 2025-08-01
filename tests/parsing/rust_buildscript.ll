; ModuleID = './enums/target/debug/build/enum-tests-e089ccba7d518cf6/build_script_build-e089ccba7d518cf6.bc'
source_filename = "50xxd17d9t8dq3o4"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"core::result::Result<alloc::string::String, std::env::VarError>" = type { i64, [3 x i64] }
%"core::fmt::Arguments" = type { { ptr, i64 }, { ptr, i64 }, { ptr, i64 } }
%"core::alloc::layout::LayoutError" = type {}
%"core::result::Result<core::convert::Infallible, core::alloc::layout::LayoutError>::Err" = type { %"core::alloc::layout::LayoutError" }
%"alloc::string::String" = type { %"alloc::vec::Vec<u8>" }
%"alloc::vec::Vec<u8>" = type { { ptr, i64 }, i64 }
%"std::env::VarError" = type { ptr, [2 x i64] }
%"core::result::Result<alloc::string::String, std::env::VarError>::Ok" = type { [1 x i64], %"alloc::string::String" }
%"core::result::Result<alloc::string::String, std::env::VarError>::Err" = type { [1 x i64], %"std::env::VarError" }
%"core::ptr::metadata::PtrComponents<u8>" = type { ptr, {} }
%"core::ptr::metadata::PtrRepr<u8>" = type { [1 x i64] }
%"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>" = type { [2 x i64], i64 }
%"core::ptr::metadata::PtrRepr<[u8]>" = type { [2 x i64] }

@vtable.0 = private unnamed_addr constant <{ ptr, [16 x i8], ptr, ptr, ptr }> <{ ptr @"_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h196226712f618a69E", [16 x i8] c"\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h66ac8c8cfdead3faE", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E" }>, align 8, !dbg !0
@alloc13 = private unnamed_addr constant <{ [12 x i8] }> <{ [12 x i8] c"invalid args" }>, align 1
@alloc14 = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc13, [8 x i8] c"\0C\00\00\00\00\00\00\00" }>, align 8
@alloc16 = private unnamed_addr constant <{}> zeroinitializer, align 8
@alloc108 = private unnamed_addr constant <{ [75 x i8] }> <{ [75 x i8] c"/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/fmt/mod.rs" }>, align 1
@alloc109 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc108, [16 x i8] c"K\00\00\00\00\00\00\00\88\01\00\00\0D\00\00\00" }>, align 8
@alloc110 = private unnamed_addr constant <{ [43 x i8] }> <{ [43 x i8] c"called `Result::unwrap()` on an `Err` value" }>, align 1
@vtable.1 = private unnamed_addr constant <{ ptr, [16 x i8], ptr }> <{ ptr @"_ZN4core3ptr39drop_in_place$LT$std..env..VarError$GT$17hbb9f1951a94d6b0bE", [16 x i8] c"\18\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN55_$LT$std..env..VarError$u20$as$u20$core..fmt..Debug$GT$3fmt17he46da4fdbd9f8b4bE" }>, align 8, !dbg !24
@alloc114 = private unnamed_addr constant <{ [18 x i8] }> <{ [18 x i8] c"CARGO_MANIFEST_DIR" }>, align 1
@alloc115 = private unnamed_addr constant <{ [8 x i8] }> <{ [8 x i8] c"build.rs" }>, align 1
@alloc116 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc115, [16 x i8] c"\08\00\00\00\00\00\00\00\04\00\00\007\00\00\00" }>, align 8
@alloc4 = private unnamed_addr constant <{ [31 x i8] }> <{ [31 x i8] c"cargo:rustc-link-search=native=" }>, align 1
@alloc6 = private unnamed_addr constant <{ [1 x i8] }> <{ [1 x i8] c"\0A" }>, align 1
@alloc5 = private unnamed_addr constant <{ ptr, [8 x i8], ptr, [8 x i8] }> <{ ptr @alloc4, [8 x i8] c"\1F\00\00\00\00\00\00\00", ptr @alloc6, [8 x i8] c"\01\00\00\00\00\00\00\00" }>, align 8
@__rustc_debug_gdb_scripts_section__ = linkonce_odr unnamed_addr constant [34 x i8] c"\01gdb_load_rust_pretty_printers.py\00", section ".debug_gdb_scripts", align 1

; Function Attrs: inlinehint nonlazybind uwtable
define internal ptr @"_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd6350e6730446559E"(ptr %unique) unnamed_addr #0 !dbg !175 {
start:
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill1 = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  %unique.dbg.spill = alloca ptr, align 8
  %0 = alloca ptr, align 8
  store ptr %unique, ptr %unique.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %unique.dbg.spill, metadata !181, metadata !DIExpression()), !dbg !182
  store ptr %unique, ptr %self.dbg.spill, align 8, !dbg !183
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !184, metadata !DIExpression()), !dbg !192
  store ptr %unique, ptr %self.dbg.spill1, align 8, !dbg !192
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill1, metadata !193, metadata !DIExpression()), !dbg !198
  store ptr %unique, ptr %ptr.dbg.spill, align 8, !dbg !198
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !200, metadata !DIExpression()), !dbg !205
  store ptr %unique, ptr %0, align 8, !dbg !205
  %1 = load ptr, ptr %0, align 8, !dbg !207, !nonnull !23, !noundef !23
  ret ptr %1, !dbg !207
}

; Function Attrs: noinline nonlazybind uwtable
define internal void @_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17hb7516deb05ead5dbE(ptr %f) unnamed_addr #1 personality ptr @rust_eh_personality !dbg !208 {
start:
  %0 = alloca { ptr, i32 }, align 8
  %dummy.dbg.spill = alloca {}, align 1
  %f.dbg.spill = alloca ptr, align 8
  %result.dbg.spill = alloca {}, align 1
  call void @llvm.dbg.declare(metadata ptr %result.dbg.spill, metadata !216, metadata !DIExpression()), !dbg !221
  store ptr %f, ptr %f.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %f.dbg.spill, metadata !215, metadata !DIExpression()), !dbg !222
  call void @llvm.dbg.declare(metadata ptr %dummy.dbg.spill, metadata !223, metadata !DIExpression()), !dbg !232
  call void @_ZN4core3ops8function6FnOnce9call_once17h6e624e4cb526ac89E(ptr %f), !dbg !234
  br label %bb1, !dbg !234

bb1:                                              ; preds = %start
  call void asm sideeffect "", "r,~{memory}"(ptr undef), !dbg !232, !srcloc !235
  br label %bb4, !dbg !232

bb4:                                              ; preds = %bb1
  ret void, !dbg !236

bb2:                                              ; No predecessors!
  br label %bb3, !dbg !237

bb3:                                              ; preds = %bb2
  %1 = bitcast ptr %0 to ptr, !dbg !238
  %2 = load ptr, ptr %1, align 8, !dbg !238
  %3 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 1, !dbg !238
  %4 = load i32, ptr %3, align 8, !dbg !238
  %5 = insertvalue { ptr, i32 } undef, ptr %2, 0, !dbg !238
  %6 = insertvalue { ptr, i32 } %5, i32 %4, 1, !dbg !238
  resume { ptr, i32 } %6, !dbg !238
}

; Function Attrs: nonlazybind uwtable
define hidden i64 @_ZN3std2rt10lang_start17he4b4cd36ba5e3c57E(ptr %main, i64 %argc, ptr %argv) unnamed_addr #2 !dbg !239 {
start:
  %v.dbg.spill = alloca i64, align 8
  %argv.dbg.spill = alloca ptr, align 8
  %argc.dbg.spill = alloca i64, align 8
  %main.dbg.spill = alloca ptr, align 8
  %_8 = alloca ptr, align 8
  %_4 = alloca i64, align 8
  store ptr %main, ptr %main.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %main.dbg.spill, metadata !246, metadata !DIExpression()), !dbg !251
  store i64 %argc, ptr %argc.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %argc.dbg.spill, metadata !247, metadata !DIExpression()), !dbg !252
  store ptr %argv, ptr %argv.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %argv.dbg.spill, metadata !248, metadata !DIExpression()), !dbg !253
  %0 = bitcast ptr %_8 to ptr, !dbg !254
  store ptr %main, ptr %0, align 8, !dbg !254
  %_5.0 = bitcast ptr %_8 to ptr, !dbg !255
  %1 = call i64 @_ZN3std2rt19lang_start_internal17h498f9556b87c8e5fE(ptr align 1 %_5.0, ptr align 8 @vtable.0, i64 %argc, ptr %argv), !dbg !256
  store i64 %1, ptr %_4, align 8, !dbg !256
  br label %bb1, !dbg !256

bb1:                                              ; preds = %start
  %v = load i64, ptr %_4, align 8, !dbg !257
  store i64 %v, ptr %v.dbg.spill, align 8, !dbg !257
  call void @llvm.dbg.declare(metadata ptr %v.dbg.spill, metadata !249, metadata !DIExpression()), !dbg !258
  ret i64 %v, !dbg !259
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E"(ptr align 8 %_1) unnamed_addr #0 !dbg !260 {
start:
  %self.dbg.spill = alloca ptr, align 8
  %_1.dbg.spill = alloca ptr, align 8
  %self = alloca i8, align 1
  store ptr %_1, ptr %_1.dbg.spill, align 8
  %0 = load ptr, ptr %_1.dbg.spill, align 8, !nonnull !23, !align !267, !noundef !23
  %1 = bitcast ptr %0 to ptr
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !266, metadata !DIExpression(DW_OP_deref)), !dbg !268
  call void @llvm.dbg.declare(metadata ptr %self, metadata !269, metadata !DIExpression()), !dbg !285
  %2 = bitcast ptr %_1 to ptr, !dbg !287
  %_4 = load ptr, ptr %2, align 8, !dbg !287, !nonnull !23, !noundef !23
  call void @_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17hb7516deb05ead5dbE(ptr %_4), !dbg !286
  br label %bb1, !dbg !286

bb1:                                              ; preds = %start
  %3 = call i8 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h8a2d015129d5babaE"(), !dbg !286
  store i8 %3, ptr %self, align 1, !dbg !286
  br label %bb2, !dbg !286

bb2:                                              ; preds = %bb1
  store ptr %self, ptr %self.dbg.spill, align 8, !dbg !285
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !288, metadata !DIExpression()), !dbg !296
  %_6 = load i8, ptr %self, align 1, !dbg !296
  %4 = zext i8 %_6 to i32, !dbg !296
  ret i32 %4, !dbg !298
}

; Function Attrs: nonlazybind uwtable
define internal void @_ZN3std3env3var17h1ab2aebfffbd5e57E(ptr sret(%"core::result::Result<alloc::string::String, std::env::VarError>") %0, ptr align 1 %1, i64 %2) unnamed_addr #2 personality ptr @rust_eh_personality !dbg !299 {
start:
  %3 = alloca { ptr, i32 }, align 8
  %key = alloca { ptr, i64 }, align 8
  %4 = getelementptr inbounds { ptr, i64 }, ptr %key, i32 0, i32 0
  store ptr %1, ptr %4, align 8
  %5 = getelementptr inbounds { ptr, i64 }, ptr %key, i32 0, i32 1
  store i64 %2, ptr %5, align 8
  call void @llvm.dbg.declare(metadata ptr %key, metadata !330, metadata !DIExpression()), !dbg !333
  %6 = invoke { ptr, i64 } @"_ZN55_$LT$$RF$T$u20$as$u20$core..convert..AsRef$LT$U$GT$$GT$6as_ref17h8db5e479bfb5017aE"(ptr align 8 %key)
          to label %bb1 unwind label %cleanup, !dbg !334

bb4:                                              ; preds = %cleanup
  br label %bb5, !dbg !335

cleanup:                                          ; preds = %bb1, %start
  %7 = landingpad { ptr, i32 }
          cleanup
  %8 = extractvalue { ptr, i32 } %7, 0
  %9 = extractvalue { ptr, i32 } %7, 1
  %10 = getelementptr inbounds { ptr, i32 }, ptr %3, i32 0, i32 0
  store ptr %8, ptr %10, align 8
  %11 = getelementptr inbounds { ptr, i32 }, ptr %3, i32 0, i32 1
  store i32 %9, ptr %11, align 8
  br label %bb4

bb1:                                              ; preds = %start
  %_3.0 = extractvalue { ptr, i64 } %6, 0, !dbg !334
  %_3.1 = extractvalue { ptr, i64 } %6, 1, !dbg !334
  invoke void @_ZN3std3env4_var17h48effbaa8b2613b5E(ptr sret(%"core::result::Result<alloc::string::String, std::env::VarError>") %0, ptr align 1 %_3.0, i64 %_3.1)
          to label %bb2 unwind label %cleanup, !dbg !336

bb2:                                              ; preds = %bb1
  br label %bb3, !dbg !335

bb5:                                              ; preds = %bb4
  %12 = bitcast ptr %3 to ptr, !dbg !337
  %13 = load ptr, ptr %12, align 8, !dbg !337
  %14 = getelementptr inbounds { ptr, i32 }, ptr %3, i32 0, i32 1, !dbg !337
  %15 = load i32, ptr %14, align 8, !dbg !337
  %16 = insertvalue { ptr, i32 } undef, ptr %13, 0, !dbg !337
  %17 = insertvalue { ptr, i32 } %16, i32 %15, 1, !dbg !337
  resume { ptr, i32 } %17, !dbg !337

bb3:                                              ; preds = %bb2
  ret void, !dbg !338
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, i64 } @"_ZN3std3ffi6os_str85_$LT$impl$u20$core..convert..AsRef$LT$std..ffi..os_str..OsStr$GT$$u20$for$u20$str$GT$6as_ref17h6f335272d1955c69E"(ptr align 1 %self.0, i64 %self.1) unnamed_addr #0 !dbg !339 {
start:
  %inner.dbg.spill = alloca { ptr, i64 }, align 8
  %0 = alloca { ptr, i64 }, align 8
  %s.dbg.spill2 = alloca { ptr, i64 }, align 8
  %1 = alloca { ptr, i64 }, align 8
  %self.dbg.spill1 = alloca { ptr, i64 }, align 8
  %s.dbg.spill = alloca { ptr, i64 }, align 8
  %self.dbg.spill = alloca { ptr, i64 }, align 8
  %2 = getelementptr inbounds { ptr, i64 }, ptr %self.dbg.spill, i32 0, i32 0
  store ptr %self.0, ptr %2, align 8
  %3 = getelementptr inbounds { ptr, i64 }, ptr %self.dbg.spill, i32 0, i32 1
  store i64 %self.1, ptr %3, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !356, metadata !DIExpression()), !dbg !357
  %4 = getelementptr inbounds { ptr, i64 }, ptr %s.dbg.spill, i32 0, i32 0, !dbg !358
  store ptr %self.0, ptr %4, align 8, !dbg !358
  %5 = getelementptr inbounds { ptr, i64 }, ptr %s.dbg.spill, i32 0, i32 1, !dbg !358
  store i64 %self.1, ptr %5, align 8, !dbg !358
  call void @llvm.dbg.declare(metadata ptr %s.dbg.spill, metadata !359, metadata !DIExpression()), !dbg !371
  %6 = getelementptr inbounds { ptr, i64 }, ptr %self.dbg.spill1, i32 0, i32 0, !dbg !371
  store ptr %self.0, ptr %6, align 8, !dbg !371
  %7 = getelementptr inbounds { ptr, i64 }, ptr %self.dbg.spill1, i32 0, i32 1, !dbg !371
  store i64 %self.1, ptr %7, align 8, !dbg !371
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill1, metadata !373, metadata !DIExpression()), !dbg !386
  %8 = getelementptr inbounds { ptr, i64 }, ptr %1, i32 0, i32 0, !dbg !386
  store ptr %self.0, ptr %8, align 8, !dbg !386
  %9 = getelementptr inbounds { ptr, i64 }, ptr %1, i32 0, i32 1, !dbg !386
  store i64 %self.1, ptr %9, align 8, !dbg !386
  %10 = getelementptr inbounds { ptr, i64 }, ptr %1, i32 0, i32 0, !dbg !386
  %_6.0 = load ptr, ptr %10, align 8, !dbg !386, !nonnull !23, !align !388, !noundef !23
  %11 = getelementptr inbounds { ptr, i64 }, ptr %1, i32 0, i32 1, !dbg !386
  %_6.1 = load i64, ptr %11, align 8, !dbg !386
  br label %bb1, !dbg !386

bb1:                                              ; preds = %start
  %12 = getelementptr inbounds { ptr, i64 }, ptr %s.dbg.spill2, i32 0, i32 0, !dbg !371
  store ptr %_6.0, ptr %12, align 8, !dbg !371
  %13 = getelementptr inbounds { ptr, i64 }, ptr %s.dbg.spill2, i32 0, i32 1, !dbg !371
  store i64 %_6.1, ptr %13, align 8, !dbg !371
  call void @llvm.dbg.declare(metadata ptr %s.dbg.spill2, metadata !389, metadata !DIExpression()), !dbg !395
  %14 = bitcast ptr %0 to ptr, !dbg !395
  %15 = getelementptr inbounds { ptr, i64 }, ptr %14, i32 0, i32 0, !dbg !395
  store ptr %_6.0, ptr %15, align 8, !dbg !395
  %16 = getelementptr inbounds { ptr, i64 }, ptr %14, i32 0, i32 1, !dbg !395
  store i64 %_6.1, ptr %16, align 8, !dbg !395
  %17 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 0, !dbg !395
  %_3.0 = load ptr, ptr %17, align 8, !dbg !395, !nonnull !23, !align !388, !noundef !23
  %18 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 1, !dbg !395
  %_3.1 = load i64, ptr %18, align 8, !dbg !395
  br label %bb2, !dbg !395

bb2:                                              ; preds = %bb1
  %19 = getelementptr inbounds { ptr, i64 }, ptr %inner.dbg.spill, i32 0, i32 0, !dbg !372
  store ptr %_3.0, ptr %19, align 8, !dbg !372
  %20 = getelementptr inbounds { ptr, i64 }, ptr %inner.dbg.spill, i32 0, i32 1, !dbg !372
  store i64 %_3.1, ptr %20, align 8, !dbg !372
  call void @llvm.dbg.declare(metadata ptr %inner.dbg.spill, metadata !397, metadata !DIExpression()), !dbg !402
  %_10.0 = bitcast ptr %_3.0 to ptr, !dbg !402
  %21 = insertvalue { ptr, i64 } undef, ptr %_10.0, 0, !dbg !404
  %22 = insertvalue { ptr, i64 } %21, i64 %_3.1, 1, !dbg !404
  ret { ptr, i64 } %22, !dbg !404
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, ptr } @_ZN4core3fmt10ArgumentV111new_display17h8e936bdad87877f0E(ptr align 8 %x) unnamed_addr #0 !dbg !405 {
start:
  %0 = alloca ptr, align 8
  %1 = alloca ptr, align 8
  %f.dbg.spill = alloca ptr, align 8
  %x.dbg.spill1 = alloca ptr, align 8
  %x.dbg.spill = alloca ptr, align 8
  %2 = alloca { ptr, ptr }, align 8
  store ptr %x, ptr %x.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !472, metadata !DIExpression()), !dbg !474
  store ptr %x, ptr %x.dbg.spill1, align 8, !dbg !475
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill1, metadata !476, metadata !DIExpression()), !dbg !485
  store ptr @"_ZN60_$LT$alloc..string..String$u20$as$u20$core..fmt..Display$GT$3fmt17hf3eccfebf7e287d9E", ptr %f.dbg.spill, align 8, !dbg !487
  call void @llvm.dbg.declare(metadata ptr %f.dbg.spill, metadata !484, metadata !DIExpression()), !dbg !485
  store ptr @"_ZN60_$LT$alloc..string..String$u20$as$u20$core..fmt..Display$GT$3fmt17hf3eccfebf7e287d9E", ptr %1, align 8, !dbg !485
  %_4 = load ptr, ptr %1, align 8, !dbg !485, !nonnull !23, !noundef !23
  br label %bb1, !dbg !485

bb1:                                              ; preds = %start
  %3 = bitcast ptr %x to ptr, !dbg !485
  store ptr %3, ptr %0, align 8, !dbg !485
  %_6 = load ptr, ptr %0, align 8, !dbg !485, !nonnull !23, !align !388, !noundef !23
  br label %bb2, !dbg !485

bb2:                                              ; preds = %bb1
  %4 = bitcast ptr %2 to ptr, !dbg !485
  store ptr %_6, ptr %4, align 8, !dbg !485
  %5 = getelementptr inbounds { ptr, ptr }, ptr %2, i32 0, i32 1, !dbg !485
  %6 = bitcast ptr %5 to ptr, !dbg !485
  store ptr %_4, ptr %6, align 8, !dbg !485
  %7 = getelementptr inbounds { ptr, ptr }, ptr %2, i32 0, i32 0, !dbg !488
  %8 = load ptr, ptr %7, align 8, !dbg !488, !nonnull !23, !align !388, !noundef !23
  %9 = getelementptr inbounds { ptr, ptr }, ptr %2, i32 0, i32 1, !dbg !488
  %10 = load ptr, ptr %9, align 8, !dbg !488, !nonnull !23, !noundef !23
  %11 = insertvalue { ptr, ptr } undef, ptr %8, 0, !dbg !488
  %12 = insertvalue { ptr, ptr } %11, ptr %10, 1, !dbg !488
  ret { ptr, ptr } %12, !dbg !488
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal void @_ZN4core3fmt9Arguments6new_v117h4b70dcc115ea8332E(ptr sret(%"core::fmt::Arguments") %0, ptr align 8 %pieces.0, i64 %pieces.1, ptr align 8 %args.0, i64 %args.1) unnamed_addr #0 !dbg !489 {
start:
  %args.dbg.spill = alloca { ptr, i64 }, align 8
  %pieces.dbg.spill = alloca { ptr, i64 }, align 8
  %_24 = alloca { ptr, i64 }, align 8
  %_16 = alloca %"core::fmt::Arguments", align 8
  %_3 = alloca i8, align 1
  %1 = getelementptr inbounds { ptr, i64 }, ptr %pieces.dbg.spill, i32 0, i32 0
  store ptr %pieces.0, ptr %1, align 8
  %2 = getelementptr inbounds { ptr, i64 }, ptr %pieces.dbg.spill, i32 0, i32 1
  store i64 %pieces.1, ptr %2, align 8
  call void @llvm.dbg.declare(metadata ptr %pieces.dbg.spill, metadata !552, metadata !DIExpression()), !dbg !554
  %3 = getelementptr inbounds { ptr, i64 }, ptr %args.dbg.spill, i32 0, i32 0
  store ptr %args.0, ptr %3, align 8
  %4 = getelementptr inbounds { ptr, i64 }, ptr %args.dbg.spill, i32 0, i32 1
  store i64 %args.1, ptr %4, align 8
  call void @llvm.dbg.declare(metadata ptr %args.dbg.spill, metadata !553, metadata !DIExpression()), !dbg !555
  %_4 = icmp ult i64 %pieces.1, %args.1, !dbg !556
  br i1 %_4, label %bb1, label %bb2, !dbg !556

bb2:                                              ; preds = %start
  %_12 = add i64 %args.1, 1, !dbg !557
  %_9 = icmp ugt i64 %pieces.1, %_12, !dbg !558
  %5 = zext i1 %_9 to i8, !dbg !556
  store i8 %5, ptr %_3, align 1, !dbg !556
  br label %bb3, !dbg !556

bb1:                                              ; preds = %start
  store i8 1, ptr %_3, align 1, !dbg !556
  br label %bb3, !dbg !556

bb3:                                              ; preds = %bb1, %bb2
  %6 = load i8, ptr %_3, align 1, !dbg !556, !range !559, !noundef !23
  %7 = trunc i8 %6 to i1, !dbg !556
  br i1 %7, label %bb4, label %bb6, !dbg !556

bb6:                                              ; preds = %bb3
  %8 = bitcast ptr %_24 to ptr, !dbg !560
  store ptr null, ptr %8, align 8, !dbg !560
  %9 = bitcast ptr %0 to ptr, !dbg !561
  %10 = getelementptr inbounds { ptr, i64 }, ptr %9, i32 0, i32 0, !dbg !561
  store ptr %pieces.0, ptr %10, align 8, !dbg !561
  %11 = getelementptr inbounds { ptr, i64 }, ptr %9, i32 0, i32 1, !dbg !561
  store i64 %pieces.1, ptr %11, align 8, !dbg !561
  %12 = getelementptr inbounds %"core::fmt::Arguments", ptr %0, i32 0, i32 1, !dbg !561
  %13 = getelementptr inbounds { ptr, i64 }, ptr %_24, i32 0, i32 0, !dbg !561
  %14 = load ptr, ptr %13, align 8, !dbg !561, !align !267
  %15 = getelementptr inbounds { ptr, i64 }, ptr %_24, i32 0, i32 1, !dbg !561
  %16 = load i64, ptr %15, align 8, !dbg !561
  %17 = getelementptr inbounds { ptr, i64 }, ptr %12, i32 0, i32 0, !dbg !561
  store ptr %14, ptr %17, align 8, !dbg !561
  %18 = getelementptr inbounds { ptr, i64 }, ptr %12, i32 0, i32 1, !dbg !561
  store i64 %16, ptr %18, align 8, !dbg !561
  %19 = getelementptr inbounds %"core::fmt::Arguments", ptr %0, i32 0, i32 2, !dbg !561
  %20 = getelementptr inbounds { ptr, i64 }, ptr %19, i32 0, i32 0, !dbg !561
  store ptr %args.0, ptr %20, align 8, !dbg !561
  %21 = getelementptr inbounds { ptr, i64 }, ptr %19, i32 0, i32 1, !dbg !561
  store i64 %args.1, ptr %21, align 8, !dbg !561
  ret void, !dbg !562

bb4:                                              ; preds = %bb3
  call void @_ZN4core3fmt9Arguments6new_v117h4b70dcc115ea8332E(ptr sret(%"core::fmt::Arguments") %_16, ptr align 8 @alloc14, i64 1, ptr align 8 @alloc16, i64 0), !dbg !563
  br label %bb5, !dbg !563

bb5:                                              ; preds = %bb4
  call void @_ZN4core9panicking9panic_fmt17h62ccf03c8a8a51b5E(ptr %_16, ptr align 8 @alloc109) #11, !dbg !563
  unreachable, !dbg !563
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17hb90a4357ac0c70a7E"(i64 %self, i64 %rhs) unnamed_addr #0 !dbg !564 {
start:
  %0 = alloca i8, align 1
  %b.dbg.spill4 = alloca i8, align 1
  %a.dbg.spill3 = alloca i64, align 8
  %b.dbg.spill = alloca i8, align 1
  %a.dbg.spill = alloca i64, align 8
  %1 = alloca { i64, i8 }, align 8
  %rhs.dbg.spill2 = alloca i64, align 8
  %self.dbg.spill1 = alloca i64, align 8
  %rhs.dbg.spill = alloca i64, align 8
  %self.dbg.spill = alloca i64, align 8
  %_5 = alloca { i64, i8 }, align 8
  %2 = alloca { i64, i64 }, align 8
  store i64 %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !571, metadata !DIExpression()), !dbg !577
  store i64 %rhs, ptr %rhs.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %rhs.dbg.spill, metadata !572, metadata !DIExpression()), !dbg !578
  store i64 %self, ptr %self.dbg.spill1, align 8, !dbg !579
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill1, metadata !580, metadata !DIExpression()), !dbg !593
  store i64 %rhs, ptr %rhs.dbg.spill2, align 8, !dbg !594
  call void @llvm.dbg.declare(metadata ptr %rhs.dbg.spill2, metadata !589, metadata !DIExpression()), !dbg !593
  %3 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %self, i64 %rhs), !dbg !593
  %4 = extractvalue { i64, i1 } %3, 0, !dbg !593
  %5 = extractvalue { i64, i1 } %3, 1, !dbg !593
  %6 = zext i1 %5 to i8, !dbg !593
  %7 = bitcast ptr %1 to ptr, !dbg !593
  store i64 %4, ptr %7, align 8, !dbg !593
  %8 = getelementptr inbounds { i64, i8 }, ptr %1, i32 0, i32 1, !dbg !593
  store i8 %6, ptr %8, align 8, !dbg !593
  %9 = getelementptr inbounds { i64, i8 }, ptr %1, i32 0, i32 0, !dbg !593
  %_13.0 = load i64, ptr %9, align 8, !dbg !593
  %10 = getelementptr inbounds { i64, i8 }, ptr %1, i32 0, i32 1, !dbg !593
  %11 = load i8, ptr %10, align 8, !dbg !593, !range !559, !noundef !23
  %_13.1 = trunc i8 %11 to i1, !dbg !593
  br label %bb5, !dbg !593

bb5:                                              ; preds = %start
  store i64 %_13.0, ptr %a.dbg.spill, align 8, !dbg !593
  call void @llvm.dbg.declare(metadata ptr %a.dbg.spill, metadata !590, metadata !DIExpression()), !dbg !595
  %12 = zext i1 %_13.1 to i8, !dbg !593
  store i8 %12, ptr %b.dbg.spill, align 1, !dbg !593
  call void @llvm.dbg.declare(metadata ptr %b.dbg.spill, metadata !592, metadata !DIExpression()), !dbg !595
  %13 = bitcast ptr %_5 to ptr, !dbg !595
  store i64 %_13.0, ptr %13, align 8, !dbg !595
  %14 = getelementptr inbounds { i64, i8 }, ptr %_5, i32 0, i32 1, !dbg !595
  %15 = zext i1 %_13.1 to i8, !dbg !595
  store i8 %15, ptr %14, align 8, !dbg !595
  %16 = bitcast ptr %_5 to ptr, !dbg !596
  %a = load i64, ptr %16, align 8, !dbg !596
  store i64 %a, ptr %a.dbg.spill3, align 8, !dbg !596
  call void @llvm.dbg.declare(metadata ptr %a.dbg.spill3, metadata !573, metadata !DIExpression()), !dbg !597
  %17 = getelementptr inbounds { i64, i8 }, ptr %_5, i32 0, i32 1, !dbg !598
  %18 = load i8, ptr %17, align 8, !dbg !598, !range !559, !noundef !23
  %b = trunc i8 %18 to i1, !dbg !598
  %19 = zext i1 %b to i8, !dbg !598
  store i8 %19, ptr %b.dbg.spill4, align 1, !dbg !598
  call void @llvm.dbg.declare(metadata ptr %b.dbg.spill4, metadata !575, metadata !DIExpression()), !dbg !599
  %20 = call i1 @llvm.expect.i1(i1 %b, i1 false), !dbg !600
  %21 = zext i1 %20 to i8, !dbg !600
  store i8 %21, ptr %0, align 1, !dbg !600
  %22 = load i8, ptr %0, align 1, !dbg !600, !range !559, !noundef !23
  %_8 = trunc i8 %22 to i1, !dbg !600
  br label %bb1, !dbg !600

bb1:                                              ; preds = %bb5
  br i1 %_8, label %bb2, label %bb3, !dbg !600

bb3:                                              ; preds = %bb1
  %23 = getelementptr inbounds { i64, i64 }, ptr %2, i32 0, i32 1, !dbg !601
  store i64 %a, ptr %23, align 8, !dbg !601
  %24 = bitcast ptr %2 to ptr, !dbg !601
  store i64 1, ptr %24, align 8, !dbg !601
  br label %bb4, !dbg !602

bb2:                                              ; preds = %bb1
  %25 = bitcast ptr %2 to ptr, !dbg !603
  store i64 0, ptr %25, align 8, !dbg !603
  br label %bb4, !dbg !602

bb4:                                              ; preds = %bb2, %bb3
  %26 = getelementptr inbounds { i64, i64 }, ptr %2, i32 0, i32 0, !dbg !604
  %27 = load i64, ptr %26, align 8, !dbg !604, !range !605, !noundef !23
  %28 = getelementptr inbounds { i64, i64 }, ptr %2, i32 0, i32 1, !dbg !604
  %29 = load i64, ptr %28, align 8, !dbg !604
  %30 = insertvalue { i64, i64 } undef, i64 %27, 0, !dbg !604
  %31 = insertvalue { i64, i64 } %30, i64 %29, 1, !dbg !604
  ret { i64, i64 } %31, !dbg !604
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @"_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h66ac8c8cfdead3faE"(ptr %_1) unnamed_addr #0 !dbg !606 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  %_2 = alloca {}, align 1
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !615, metadata !DIExpression()), !dbg !620
  call void @llvm.dbg.declare(metadata ptr %_2, metadata !616, metadata !DIExpression()), !dbg !620
  %0 = load ptr, ptr %_1, align 8, !dbg !620, !nonnull !23, !noundef !23
  %1 = call i32 @_ZN4core3ops8function6FnOnce9call_once17h5767b38317950c8bE(ptr %0), !dbg !620
  br label %bb1, !dbg !620

bb1:                                              ; preds = %start
  ret i32 %1, !dbg !620
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @_ZN4core3ops8function6FnOnce9call_once17h5767b38317950c8bE(ptr %0) unnamed_addr #0 personality ptr @rust_eh_personality !dbg !621 {
start:
  %1 = alloca { ptr, i32 }, align 8
  %_2 = alloca {}, align 1
  %_1 = alloca ptr, align 8
  store ptr %0, ptr %_1, align 8
  call void @llvm.dbg.declare(metadata ptr %_1, metadata !625, metadata !DIExpression()), !dbg !627
  call void @llvm.dbg.declare(metadata ptr %_2, metadata !626, metadata !DIExpression()), !dbg !627
  %2 = invoke i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E"(ptr align 8 %_1)
          to label %bb1 unwind label %cleanup, !dbg !627

bb3:                                              ; preds = %cleanup
  br label %bb4, !dbg !627

cleanup:                                          ; preds = %start
  %3 = landingpad { ptr, i32 }
          cleanup
  %4 = extractvalue { ptr, i32 } %3, 0
  %5 = extractvalue { ptr, i32 } %3, 1
  %6 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 0
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 1
  store i32 %5, ptr %7, align 8
  br label %bb3

bb1:                                              ; preds = %start
  br label %bb2, !dbg !627

bb4:                                              ; preds = %bb3
  %8 = bitcast ptr %1 to ptr, !dbg !627
  %9 = load ptr, ptr %8, align 8, !dbg !627
  %10 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 1, !dbg !627
  %11 = load i32, ptr %10, align 8, !dbg !627
  %12 = insertvalue { ptr, i32 } undef, ptr %9, 0, !dbg !627
  %13 = insertvalue { ptr, i32 } %12, i32 %11, 1, !dbg !627
  resume { ptr, i32 } %13, !dbg !627

bb2:                                              ; preds = %bb1
  ret i32 %2, !dbg !627
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal void @_ZN4core3ops8function6FnOnce9call_once17h6e624e4cb526ac89E(ptr %_1) unnamed_addr #0 !dbg !628 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  %_2 = alloca {}, align 1
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !630, metadata !DIExpression()), !dbg !634
  call void @llvm.dbg.declare(metadata ptr %_2, metadata !631, metadata !DIExpression()), !dbg !634
  call void %_1(), !dbg !634
  br label %bb1, !dbg !634

bb1:                                              ; preds = %start
  ret void, !dbg !634
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr39drop_in_place$LT$std..env..VarError$GT$17hbb9f1951a94d6b0bE"(ptr %_1) unnamed_addr #2 !dbg !635 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !641, metadata !DIExpression()), !dbg !644
  %0 = bitcast ptr %_1 to ptr, !dbg !644
  %1 = load ptr, ptr %0, align 8, !dbg !644
  %2 = icmp eq ptr %1, null, !dbg !644
  %_2 = select i1 %2, i64 0, i64 1, !dbg !644
  %3 = icmp eq i64 %_2, 0, !dbg !644
  br i1 %3, label %bb1, label %bb2, !dbg !644

bb1:                                              ; preds = %bb2, %start
  ret void, !dbg !644

bb2:                                              ; preds = %start
  %4 = bitcast ptr %_1 to ptr, !dbg !644
  %5 = bitcast ptr %4 to ptr, !dbg !644
  call void @"_ZN4core3ptr47drop_in_place$LT$std..ffi..os_str..OsString$GT$17h421f40303d5a8656E"(ptr %5), !dbg !644
  br label %bb1, !dbg !644
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h017085301cfa8a38E"(ptr %_1) unnamed_addr #2 !dbg !645 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !650, metadata !DIExpression()), !dbg !651
  %0 = bitcast ptr %_1 to ptr, !dbg !651
  call void @"_ZN4core3ptr46drop_in_place$LT$alloc..vec..Vec$LT$u8$GT$$GT$17h0a98817a91215818E"(ptr %0), !dbg !651
  br label %bb1, !dbg !651

bb1:                                              ; preds = %start
  ret void, !dbg !651
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr46drop_in_place$LT$alloc..vec..Vec$LT$u8$GT$$GT$17h0a98817a91215818E"(ptr %_1) unnamed_addr #2 personality ptr @rust_eh_personality !dbg !652 {
start:
  %0 = alloca { ptr, i32 }, align 8
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !657, metadata !DIExpression()), !dbg !660
  invoke void @"_ZN70_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h80e90bd87493e4d3E"(ptr align 8 %_1)
          to label %bb4 unwind label %cleanup, !dbg !660

bb3:                                              ; preds = %cleanup
  %1 = bitcast ptr %_1 to ptr, !dbg !660
  invoke void @"_ZN4core3ptr53drop_in_place$LT$alloc..raw_vec..RawVec$LT$u8$GT$$GT$17h63264ea4812108b9E"(ptr %1) #12
          to label %bb1 unwind label %abort, !dbg !660

cleanup:                                          ; preds = %start
  %2 = landingpad { ptr, i32 }
          cleanup
  %3 = extractvalue { ptr, i32 } %2, 0
  %4 = extractvalue { ptr, i32 } %2, 1
  %5 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 0
  store ptr %3, ptr %5, align 8
  %6 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 1
  store i32 %4, ptr %6, align 8
  br label %bb3

bb4:                                              ; preds = %start
  %7 = bitcast ptr %_1 to ptr, !dbg !660
  call void @"_ZN4core3ptr53drop_in_place$LT$alloc..raw_vec..RawVec$LT$u8$GT$$GT$17h63264ea4812108b9E"(ptr %7), !dbg !660
  br label %bb2, !dbg !660

abort:                                            ; preds = %bb3
  %8 = landingpad { ptr, i32 }
          cleanup, !dbg !660
  call void @_ZN4core9panicking15panic_no_unwind17h62f8113f44cbfcbfE() #13, !dbg !660
  unreachable, !dbg !660

bb1:                                              ; preds = %bb3
  %9 = bitcast ptr %0 to ptr, !dbg !660
  %10 = load ptr, ptr %9, align 8, !dbg !660
  %11 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 1, !dbg !660
  %12 = load i32, ptr %11, align 8, !dbg !660
  %13 = insertvalue { ptr, i32 } undef, ptr %10, 0, !dbg !660
  %14 = insertvalue { ptr, i32 } %13, i32 %12, 1, !dbg !660
  resume { ptr, i32 } %14, !dbg !660

bb2:                                              ; preds = %bb4
  ret void, !dbg !660
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr47drop_in_place$LT$std..ffi..os_str..OsString$GT$17h421f40303d5a8656E"(ptr %_1) unnamed_addr #2 !dbg !661 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !666, metadata !DIExpression()), !dbg !669
  %0 = bitcast ptr %_1 to ptr, !dbg !669
  call void @"_ZN4core3ptr48drop_in_place$LT$std..sys..unix..os_str..Buf$GT$17he26a14dc108ef330E"(ptr %0), !dbg !669
  br label %bb1, !dbg !669

bb1:                                              ; preds = %start
  ret void, !dbg !669
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr48drop_in_place$LT$std..sys..unix..os_str..Buf$GT$17he26a14dc108ef330E"(ptr %_1) unnamed_addr #2 !dbg !670 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !675, metadata !DIExpression()), !dbg !678
  %0 = bitcast ptr %_1 to ptr, !dbg !678
  call void @"_ZN4core3ptr46drop_in_place$LT$alloc..vec..Vec$LT$u8$GT$$GT$17h0a98817a91215818E"(ptr %0), !dbg !678
  br label %bb1, !dbg !678

bb1:                                              ; preds = %start
  ret void, !dbg !678
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN4core3ptr53drop_in_place$LT$alloc..raw_vec..RawVec$LT$u8$GT$$GT$17h63264ea4812108b9E"(ptr %_1) unnamed_addr #2 !dbg !679 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !684, metadata !DIExpression()), !dbg !687
  call void @"_ZN77_$LT$alloc..raw_vec..RawVec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hf626a1dd0a70221dE"(ptr align 8 %_1), !dbg !687
  br label %bb1, !dbg !687

bb1:                                              ; preds = %start
  ret void, !dbg !687
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal void @"_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h196226712f618a69E"(ptr %_1) unnamed_addr #0 !dbg !688 {
start:
  %_1.dbg.spill = alloca ptr, align 8
  store ptr %_1, ptr %_1.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %_1.dbg.spill, metadata !692, metadata !DIExpression()), !dbg !695
  ret void, !dbg !695
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { i64, i64 } @_ZN4core5alloc6layout6Layout21from_size_valid_align17h362893bcbac9d0a1E(i64 %size, i64 %align) unnamed_addr #0 !dbg !696 {
start:
  %n.dbg.spill = alloca i64, align 8
  %align.dbg.spill = alloca i64, align 8
  %size.dbg.spill = alloca i64, align 8
  %_11 = alloca { i64, i64 }, align 8
  %self1 = alloca i64, align 8
  %self = alloca i64, align 8
  %0 = alloca { i64, i64 }, align 8
  store i64 %size, ptr %size.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %size.dbg.spill, metadata !727, metadata !DIExpression()), !dbg !729
  store i64 %align, ptr %align.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %align.dbg.spill, metadata !728, metadata !DIExpression()), !dbg !730
  call void @llvm.dbg.declare(metadata ptr %self, metadata !731, metadata !DIExpression()), !dbg !742
  call void @llvm.dbg.declare(metadata ptr %self1, metadata !744, metadata !DIExpression()), !dbg !751
  store i64 %align, ptr %self1, align 8, !dbg !743
  %_15 = load i64, ptr %self1, align 8, !dbg !751, !range !752, !noundef !23
  store i64 %_15, ptr %n.dbg.spill, align 8, !dbg !751
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !753, metadata !DIExpression()), !dbg !769
  store i64 %_15, ptr %self, align 8, !dbg !769
  %_8 = load i64, ptr %self, align 8, !dbg !742
  %_7 = sub i64 %_8, 1, !dbg !771
  %_5 = sub i64 9223372036854775807, %_7, !dbg !772
  %_3 = icmp ugt i64 %size, %_5, !dbg !773
  br i1 %_3, label %bb1, label %bb2, !dbg !773

bb2:                                              ; preds = %start
  %1 = bitcast ptr %_11 to ptr, !dbg !774
  store i64 %size, ptr %1, align 8, !dbg !774
  %2 = getelementptr inbounds { i64, i64 }, ptr %_11, i32 0, i32 1, !dbg !774
  store i64 %align, ptr %2, align 8, !dbg !774
  %3 = getelementptr inbounds { i64, i64 }, ptr %_11, i32 0, i32 0, !dbg !775
  %4 = load i64, ptr %3, align 8, !dbg !775
  %5 = getelementptr inbounds { i64, i64 }, ptr %_11, i32 0, i32 1, !dbg !775
  %6 = load i64, ptr %5, align 8, !dbg !775, !range !752, !noundef !23
  %7 = getelementptr inbounds { i64, i64 }, ptr %0, i32 0, i32 0, !dbg !775
  store i64 %4, ptr %7, align 8, !dbg !775
  %8 = getelementptr inbounds { i64, i64 }, ptr %0, i32 0, i32 1, !dbg !775
  store i64 %6, ptr %8, align 8, !dbg !775
  br label %bb3, !dbg !776

bb1:                                              ; preds = %start
  %9 = getelementptr inbounds { i64, i64 }, ptr %0, i32 0, i32 1, !dbg !777
  store i64 0, ptr %9, align 8, !dbg !777
  br label %bb3, !dbg !776

bb3:                                              ; preds = %bb1, %bb2
  %10 = getelementptr inbounds { i64, i64 }, ptr %0, i32 0, i32 0, !dbg !776
  %11 = load i64, ptr %10, align 8, !dbg !776
  %12 = getelementptr inbounds { i64, i64 }, ptr %0, i32 0, i32 1, !dbg !776
  %13 = load i64, ptr %12, align 8, !dbg !776, !range !778, !noundef !23
  %14 = insertvalue { i64, i64 } undef, i64 %11, 0, !dbg !776
  %15 = insertvalue { i64, i64 } %14, i64 %13, 1, !dbg !776
  ret { i64, i64 } %15, !dbg !776
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { i64, i64 } @_ZN4core5alloc6layout6Layout5array17h041a339ec38f7fddE(i64 %n) unnamed_addr #0 !dbg !779 {
start:
  %0 = alloca i64, align 8
  %align.dbg.spill = alloca i64, align 8
  %array_size.dbg.spill = alloca i64, align 8
  %val.dbg.spill = alloca i64, align 8
  %v.dbg.spill5 = alloca i64, align 8
  %v.dbg.spill = alloca i64, align 8
  %e.dbg.spill3 = alloca %"core::alloc::layout::LayoutError", align 1
  %e.dbg.spill = alloca %"core::alloc::layout::LayoutError", align 1
  %residual.dbg.spill2 = alloca %"core::result::Result<core::convert::Infallible, core::alloc::layout::LayoutError>::Err", align 1
  %residual.dbg.spill = alloca %"core::result::Result<core::convert::Infallible, core::alloc::layout::LayoutError>::Err", align 1
  %err.dbg.spill = alloca %"core::alloc::layout::LayoutError", align 1
  %n.dbg.spill = alloca i64, align 8
  %self1 = alloca { i64, i64 }, align 8
  %self = alloca { i64, i64 }, align 8
  %_3 = alloca { i64, i64 }, align 8
  %1 = alloca { i64, i64 }, align 8
  store i64 %n, ptr %n.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !783, metadata !DIExpression()), !dbg !808
  call void @llvm.dbg.declare(metadata ptr %self, metadata !809, metadata !DIExpression()), !dbg !854
  call void @llvm.dbg.declare(metadata ptr %self1, metadata !856, metadata !DIExpression()), !dbg !867
  call void @llvm.dbg.declare(metadata ptr %err.dbg.spill, metadata !863, metadata !DIExpression()), !dbg !867
  call void @llvm.dbg.declare(metadata ptr %residual.dbg.spill, metadata !786, metadata !DIExpression()), !dbg !868
  call void @llvm.dbg.declare(metadata ptr %residual.dbg.spill2, metadata !869, metadata !DIExpression()), !dbg !889
  call void @llvm.dbg.declare(metadata ptr %e.dbg.spill, metadata !851, metadata !DIExpression()), !dbg !891
  call void @llvm.dbg.declare(metadata ptr %e.dbg.spill3, metadata !884, metadata !DIExpression()), !dbg !892
  %2 = call { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17hb90a4357ac0c70a7E"(i64 1, i64 %n), !dbg !855
  store { i64, i64 } %2, ptr %self1, align 8, !dbg !855
  br label %bb1, !dbg !855

bb1:                                              ; preds = %start
  %3 = bitcast ptr %self1 to ptr, !dbg !867
  %_15 = load i64, ptr %3, align 8, !dbg !867, !range !605, !noundef !23
  switch i64 %_15, label %bb9 [
    i64 0, label %bb8
    i64 1, label %bb10
  ], !dbg !867

bb9:                                              ; preds = %bb1
  unreachable, !dbg !867

bb8:                                              ; preds = %bb1
  %4 = bitcast ptr %self to ptr, !dbg !867
  store i64 1, ptr %4, align 8, !dbg !867
  br label %bb11, !dbg !867

bb10:                                             ; preds = %bb1
  %5 = getelementptr inbounds { i64, i64 }, ptr %self1, i32 0, i32 1, !dbg !867
  %v = load i64, ptr %5, align 8, !dbg !867
  store i64 %v, ptr %v.dbg.spill, align 8, !dbg !867
  call void @llvm.dbg.declare(metadata ptr %v.dbg.spill, metadata !864, metadata !DIExpression()), !dbg !893
  %6 = getelementptr inbounds { i64, i64 }, ptr %self, i32 0, i32 1, !dbg !893
  store i64 %v, ptr %6, align 8, !dbg !893
  %7 = bitcast ptr %self to ptr, !dbg !893
  store i64 0, ptr %7, align 8, !dbg !893
  br label %bb11, !dbg !867

bb11:                                             ; preds = %bb10, %bb8
  %8 = bitcast ptr %self to ptr, !dbg !854
  %_18 = load i64, ptr %8, align 8, !dbg !854, !range !605, !noundef !23
  switch i64 %_18, label %bb13 [
    i64 0, label %bb14
    i64 1, label %bb12
  ], !dbg !854

bb13:                                             ; preds = %bb11
  unreachable, !dbg !854

bb14:                                             ; preds = %bb11
  %9 = getelementptr inbounds { i64, i64 }, ptr %self, i32 0, i32 1, !dbg !854
  %v4 = load i64, ptr %9, align 8, !dbg !854
  store i64 %v4, ptr %v.dbg.spill5, align 8, !dbg !854
  call void @llvm.dbg.declare(metadata ptr %v.dbg.spill5, metadata !848, metadata !DIExpression()), !dbg !894
  %10 = getelementptr inbounds { i64, i64 }, ptr %_3, i32 0, i32 1, !dbg !894
  store i64 %v4, ptr %10, align 8, !dbg !894
  %11 = bitcast ptr %_3 to ptr, !dbg !894
  store i64 0, ptr %11, align 8, !dbg !894
  br label %bb2, !dbg !854

bb12:                                             ; preds = %bb11
  %12 = bitcast ptr %_3 to ptr, !dbg !891
  store i64 1, ptr %12, align 8, !dbg !891
  br label %bb2, !dbg !854

bb2:                                              ; preds = %bb12, %bb14
  %13 = bitcast ptr %_3 to ptr, !dbg !855
  %_9 = load i64, ptr %13, align 8, !dbg !855, !range !605, !noundef !23
  switch i64 %_9, label %bb4 [
    i64 0, label %bb3
    i64 1, label %bb5
  ], !dbg !855

bb4:                                              ; preds = %bb2
  unreachable, !dbg !855

bb3:                                              ; preds = %bb2
  %14 = getelementptr inbounds { i64, i64 }, ptr %_3, i32 0, i32 1, !dbg !855
  %val = load i64, ptr %14, align 8, !dbg !855
  store i64 %val, ptr %val.dbg.spill, align 8, !dbg !855
  call void @llvm.dbg.declare(metadata ptr %val.dbg.spill, metadata !806, metadata !DIExpression()), !dbg !895
  store i64 %val, ptr %array_size.dbg.spill, align 8, !dbg !895
  call void @llvm.dbg.declare(metadata ptr %array_size.dbg.spill, metadata !784, metadata !DIExpression()), !dbg !896
  store i64 1, ptr %align.dbg.spill, align 8, !dbg !897
  call void @llvm.dbg.declare(metadata ptr %align.dbg.spill, metadata !908, metadata !DIExpression()), !dbg !922
  store i64 1, ptr %0, align 8, !dbg !922
  %_14 = load i64, ptr %0, align 8, !dbg !922, !range !752, !noundef !23
  br label %bb15, !dbg !922

bb5:                                              ; preds = %bb2
  call void @"_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h3d20e1e9b1fe581cE"(), !dbg !892
  br label %bb16, !dbg !892

bb16:                                             ; preds = %bb5
  %15 = getelementptr inbounds { i64, i64 }, ptr %1, i32 0, i32 1, !dbg !892
  store i64 0, ptr %15, align 8, !dbg !892
  br label %bb7, !dbg !924

bb7:                                              ; preds = %bb6, %bb16
  %16 = getelementptr inbounds { i64, i64 }, ptr %1, i32 0, i32 0, !dbg !924
  %17 = load i64, ptr %16, align 8, !dbg !924
  %18 = getelementptr inbounds { i64, i64 }, ptr %1, i32 0, i32 1, !dbg !924
  %19 = load i64, ptr %18, align 8, !dbg !924, !range !778, !noundef !23
  %20 = insertvalue { i64, i64 } undef, i64 %17, 0, !dbg !924
  %21 = insertvalue { i64, i64 } %20, i64 %19, 1, !dbg !924
  ret { i64, i64 } %21, !dbg !924

bb15:                                             ; preds = %bb3
  %22 = call { i64, i64 } @_ZN4core5alloc6layout6Layout21from_size_valid_align17h362893bcbac9d0a1E(i64 %val, i64 %_14), !dbg !925
  store { i64, i64 } %22, ptr %1, align 8, !dbg !925
  br label %bb6, !dbg !925

bb6:                                              ; preds = %bb15
  br label %bb7, !dbg !924
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17hc8210bfc41415118E"(ptr sret(%"alloc::string::String") %t, ptr %self, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality !dbg !926 {
start:
  %1 = alloca { ptr, i32 }, align 8
  %e = alloca %"std::env::VarError", align 8
  call void @llvm.dbg.declare(metadata ptr %t, metadata !931, metadata !DIExpression()), !dbg !935
  call void @llvm.dbg.declare(metadata ptr %self, metadata !930, metadata !DIExpression()), !dbg !936
  call void @llvm.dbg.declare(metadata ptr %e, metadata !933, metadata !DIExpression()), !dbg !937
  %2 = bitcast ptr %self to ptr, !dbg !938
  %_2 = load i64, ptr %2, align 8, !dbg !938, !range !605, !noundef !23
  switch i64 %_2, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !939

bb2:                                              ; preds = %start
  unreachable, !dbg !938

bb3:                                              ; preds = %start
  %3 = bitcast ptr %self to ptr, !dbg !940
  %4 = getelementptr inbounds %"core::result::Result<alloc::string::String, std::env::VarError>::Ok", ptr %3, i32 0, i32 1, !dbg !940
  %5 = bitcast ptr %t to ptr, !dbg !940
  %6 = bitcast ptr %4 to ptr, !dbg !940
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %5, ptr align 8 %6, i64 24, i1 false), !dbg !940
  ret void, !dbg !941

bb1:                                              ; preds = %start
  %7 = bitcast ptr %self to ptr, !dbg !942
  %8 = getelementptr inbounds %"core::result::Result<alloc::string::String, std::env::VarError>::Err", ptr %7, i32 0, i32 1, !dbg !942
  %9 = bitcast ptr %e to ptr, !dbg !942
  %10 = bitcast ptr %8 to ptr, !dbg !942
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %9, ptr align 8 %10, i64 24, i1 false), !dbg !942
  %_7.0 = bitcast ptr %e to ptr, !dbg !943
  invoke void @_ZN4core6result13unwrap_failed17hff48f82f03d418aeE(ptr align 1 @alloc110, i64 43, ptr align 1 %_7.0, ptr align 8 @vtable.1, ptr align 8 %0) #11
          to label %unreachable unwind label %cleanup, !dbg !944

bb4:                                              ; preds = %cleanup
  invoke void @"_ZN4core3ptr39drop_in_place$LT$std..env..VarError$GT$17hbb9f1951a94d6b0bE"(ptr %e) #12
          to label %bb5 unwind label %abort, !dbg !945

cleanup:                                          ; preds = %bb1
  %11 = landingpad { ptr, i32 }
          cleanup
  %12 = extractvalue { ptr, i32 } %11, 0
  %13 = extractvalue { ptr, i32 } %11, 1
  %14 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 0
  store ptr %12, ptr %14, align 8
  %15 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 1
  store i32 %13, ptr %15, align 8
  br label %bb4

unreachable:                                      ; preds = %bb1
  unreachable

abort:                                            ; preds = %bb4
  %16 = landingpad { ptr, i32 }
          cleanup, !dbg !946
  call void @_ZN4core9panicking15panic_no_unwind17h62f8113f44cbfcbfE() #13, !dbg !946
  unreachable, !dbg !946

bb5:                                              ; preds = %bb4
  %17 = bitcast ptr %1 to ptr, !dbg !946
  %18 = load ptr, ptr %17, align 8, !dbg !946
  %19 = getelementptr inbounds { ptr, i32 }, ptr %1, i32 0, i32 1, !dbg !946
  %20 = load i32, ptr %19, align 8, !dbg !946
  %21 = insertvalue { ptr, i32 } undef, ptr %18, 0, !dbg !946
  %22 = insertvalue { ptr, i32 } %21, i32 %20, 1, !dbg !946
  resume { ptr, i32 } %22, !dbg !946
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h3d20e1e9b1fe581cE"() unnamed_addr #2 !dbg !947 {
start:
  %t.dbg.spill = alloca %"core::alloc::layout::LayoutError", align 1
  call void @llvm.dbg.declare(metadata ptr %t.dbg.spill, metadata !953, metadata !DIExpression()), !dbg !956
  ret void, !dbg !957
}

; Function Attrs: nonlazybind uwtable
define internal ptr @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h093103a2bfe88da2E"(ptr %self) unnamed_addr #2 !dbg !958 {
start:
  %self.dbg.spill = alloca ptr, align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !961, metadata !DIExpression()), !dbg !965
  %0 = call ptr @"_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd6350e6730446559E"(ptr %self), !dbg !966
  br label %bb1, !dbg !966

bb1:                                              ; preds = %start
  ret ptr %0, !dbg !967
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal i8 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h8a2d015129d5babaE"() unnamed_addr #0 !dbg !968 {
start:
  %self.dbg.spill = alloca {}, align 1
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !973, metadata !DIExpression()), !dbg !974
  ret i8 0, !dbg !975
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, i64 } @"_ZN55_$LT$$RF$T$u20$as$u20$core..convert..AsRef$LT$U$GT$$GT$6as_ref17h8db5e479bfb5017aE"(ptr align 8 %self) unnamed_addr #0 !dbg !976 {
start:
  %self.dbg.spill = alloca ptr, align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !982, metadata !DIExpression()), !dbg !985
  %0 = getelementptr inbounds { ptr, i64 }, ptr %self, i32 0, i32 0, !dbg !986
  %_3.0 = load ptr, ptr %0, align 8, !dbg !986, !nonnull !23, !align !388, !noundef !23
  %1 = getelementptr inbounds { ptr, i64 }, ptr %self, i32 0, i32 1, !dbg !986
  %_3.1 = load i64, ptr %1, align 8, !dbg !986
  %2 = call { ptr, i64 } @"_ZN3std3ffi6os_str85_$LT$impl$u20$core..convert..AsRef$LT$std..ffi..os_str..OsStr$GT$$u20$for$u20$str$GT$6as_ref17h6f335272d1955c69E"(ptr align 1 %_3.0, i64 %_3.1), !dbg !987
  %3 = extractvalue { ptr, i64 } %2, 0, !dbg !987
  %4 = extractvalue { ptr, i64 } %2, 1, !dbg !987
  br label %bb1, !dbg !987

bb1:                                              ; preds = %start
  %5 = insertvalue { ptr, i64 } undef, ptr %3, 0, !dbg !988
  %6 = insertvalue { ptr, i64 } %5, i64 %4, 1, !dbg !988
  ret { ptr, i64 } %6, !dbg !988
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal ptr @"_ZN5alloc3vec16Vec$LT$T$C$A$GT$10as_mut_ptr17hf0ab5348698999aeE"(ptr align 8 %self) unnamed_addr #0 !dbg !989 {
start:
  %0 = alloca i8, align 1
  %other.dbg.spill = alloca ptr, align 8
  %data_address.dbg.spill = alloca ptr, align 8
  %1 = alloca ptr, align 8
  %self.dbg.spill7 = alloca ptr, align 8
  %self.dbg.spill6 = alloca ptr, align 8
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill5 = alloca ptr, align 8
  %self.dbg.spill4 = alloca ptr, align 8
  %self.dbg.spill2 = alloca ptr, align 8
  %metadata.dbg.spill = alloca {}, align 1
  %self.dbg.spill = alloca ptr, align 8
  %_18 = alloca %"core::ptr::metadata::PtrComponents<u8>", align 8
  %_17 = alloca %"core::ptr::metadata::PtrRepr<u8>", align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !995, metadata !DIExpression()), !dbg !998
  call void @llvm.dbg.declare(metadata ptr %metadata.dbg.spill, metadata !999, metadata !DIExpression()), !dbg !1009
  %self1 = bitcast ptr %self to ptr, !dbg !1025
  store ptr %self1, ptr %self.dbg.spill2, align 8, !dbg !1025
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill2, metadata !1026, metadata !DIExpression()), !dbg !1034
  %2 = bitcast ptr %self1 to ptr, !dbg !1034
  %self3 = load ptr, ptr %2, align 8, !dbg !1034, !nonnull !23, !noundef !23
  store ptr %self3, ptr %self.dbg.spill4, align 8, !dbg !1034
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill4, metadata !1035, metadata !DIExpression()), !dbg !1039
  store ptr %self3, ptr %self.dbg.spill5, align 8, !dbg !1039
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill5, metadata !1041, metadata !DIExpression()), !dbg !1045
  store ptr %self3, ptr %ptr.dbg.spill, align 8, !dbg !1045
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !996, metadata !DIExpression()), !dbg !1047
  store ptr %self3, ptr %self.dbg.spill6, align 8, !dbg !1024
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill6, metadata !1022, metadata !DIExpression()), !dbg !1048
  store ptr %self3, ptr %self.dbg.spill7, align 8, !dbg !1048
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill7, metadata !1049, metadata !DIExpression()), !dbg !1056
  %3 = bitcast ptr %1 to ptr, !dbg !1058
  store i64 0, ptr %3, align 8, !dbg !1058
  %data_address = load ptr, ptr %1, align 8, !dbg !1058
  store ptr %data_address, ptr %data_address.dbg.spill, align 8, !dbg !1058
  call void @llvm.dbg.declare(metadata ptr %data_address.dbg.spill, metadata !1008, metadata !DIExpression()), !dbg !1009
  br label %bb2, !dbg !1058

bb2:                                              ; preds = %start
  %4 = bitcast ptr %_18 to ptr, !dbg !1009
  store ptr %data_address, ptr %4, align 8, !dbg !1009
  %5 = bitcast ptr %_17 to ptr, !dbg !1009
  %6 = bitcast ptr %5 to ptr, !dbg !1009
  %7 = bitcast ptr %_18 to ptr, !dbg !1009
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %6, ptr align 8 %7, i64 8, i1 false), !dbg !1009
  %8 = bitcast ptr %_17 to ptr, !dbg !1009
  %other = load ptr, ptr %8, align 8, !dbg !1009
  store ptr %other, ptr %other.dbg.spill, align 8, !dbg !1009
  call void @llvm.dbg.declare(metadata ptr %other.dbg.spill, metadata !1055, metadata !DIExpression()), !dbg !1056
  %9 = icmp eq ptr %self3, %other, !dbg !1056
  %10 = zext i1 %9 to i8, !dbg !1056
  store i8 %10, ptr %0, align 1, !dbg !1056
  %11 = load i8, ptr %0, align 1, !dbg !1056, !range !559, !noundef !23
  %_5 = trunc i8 %11 to i1, !dbg !1056
  br label %bb3, !dbg !1056

bb3:                                              ; preds = %bb2
  %_4 = xor i1 %_5, true, !dbg !1066
  call void @llvm.assume(i1 %_4), !dbg !1067
  br label %bb1, !dbg !1067

bb1:                                              ; preds = %bb3
  ret ptr %self3, !dbg !1068
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal ptr @"_ZN5alloc3vec16Vec$LT$T$C$A$GT$6as_ptr17h107a2e3cbc7884cfE"(ptr align 8 %self) unnamed_addr #0 !dbg !1069 {
start:
  %0 = alloca i8, align 1
  %other.dbg.spill = alloca ptr, align 8
  %data_address.dbg.spill = alloca ptr, align 8
  %1 = alloca ptr, align 8
  %self.dbg.spill7 = alloca ptr, align 8
  %self.dbg.spill6 = alloca ptr, align 8
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill5 = alloca ptr, align 8
  %self.dbg.spill4 = alloca ptr, align 8
  %self.dbg.spill2 = alloca ptr, align 8
  %metadata.dbg.spill = alloca {}, align 1
  %self.dbg.spill = alloca ptr, align 8
  %_20 = alloca %"core::ptr::metadata::PtrComponents<u8>", align 8
  %_19 = alloca %"core::ptr::metadata::PtrRepr<u8>", align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1074, metadata !DIExpression()), !dbg !1077
  call void @llvm.dbg.declare(metadata ptr %metadata.dbg.spill, metadata !1078, metadata !DIExpression()), !dbg !1083
  %self1 = bitcast ptr %self to ptr, !dbg !1092
  store ptr %self1, ptr %self.dbg.spill2, align 8, !dbg !1092
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill2, metadata !1093, metadata !DIExpression()), !dbg !1097
  %2 = bitcast ptr %self1 to ptr, !dbg !1097
  %self3 = load ptr, ptr %2, align 8, !dbg !1097, !nonnull !23, !noundef !23
  store ptr %self3, ptr %self.dbg.spill4, align 8, !dbg !1097
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill4, metadata !1098, metadata !DIExpression()), !dbg !1102
  store ptr %self3, ptr %self.dbg.spill5, align 8, !dbg !1102
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill5, metadata !1104, metadata !DIExpression()), !dbg !1108
  store ptr %self3, ptr %ptr.dbg.spill, align 8, !dbg !1108
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !1075, metadata !DIExpression()), !dbg !1110
  store ptr %self3, ptr %self.dbg.spill6, align 8, !dbg !1091
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill6, metadata !1089, metadata !DIExpression()), !dbg !1111
  store ptr %self3, ptr %self.dbg.spill7, align 8, !dbg !1111
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill7, metadata !1112, metadata !DIExpression()), !dbg !1117
  %3 = bitcast ptr %1 to ptr, !dbg !1119
  store i64 0, ptr %3, align 8, !dbg !1119
  %data_address = load ptr, ptr %1, align 8, !dbg !1119
  store ptr %data_address, ptr %data_address.dbg.spill, align 8, !dbg !1119
  call void @llvm.dbg.declare(metadata ptr %data_address.dbg.spill, metadata !1082, metadata !DIExpression()), !dbg !1083
  br label %bb2, !dbg !1119

bb2:                                              ; preds = %start
  %4 = bitcast ptr %_20 to ptr, !dbg !1083
  store ptr %data_address, ptr %4, align 8, !dbg !1083
  %5 = bitcast ptr %_19 to ptr, !dbg !1083
  %6 = bitcast ptr %5 to ptr, !dbg !1083
  %7 = bitcast ptr %_20 to ptr, !dbg !1083
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %6, ptr align 8 %7, i64 8, i1 false), !dbg !1083
  %8 = bitcast ptr %_19 to ptr, !dbg !1083
  %other = load ptr, ptr %8, align 8, !dbg !1083
  store ptr %other, ptr %other.dbg.spill, align 8, !dbg !1083
  call void @llvm.dbg.declare(metadata ptr %other.dbg.spill, metadata !1116, metadata !DIExpression()), !dbg !1117
  %9 = icmp eq ptr %self3, %other, !dbg !1117
  %10 = zext i1 %9 to i8, !dbg !1117
  store i8 %10, ptr %0, align 1, !dbg !1117
  %11 = load i8, ptr %0, align 1, !dbg !1117, !range !559, !noundef !23
  %_6 = trunc i8 %11 to i1, !dbg !1117
  br label %bb3, !dbg !1117

bb3:                                              ; preds = %bb2
  %_5 = xor i1 %_6, true, !dbg !1125
  call void @llvm.assume(i1 %_5), !dbg !1126
  br label %bb1, !dbg !1126

bb1:                                              ; preds = %bb3
  ret ptr %self3, !dbg !1127
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$14current_memory17hea955b31486f6310E"(ptr sret(%"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>") %0, ptr align 8 %self) unnamed_addr #2 !dbg !1128 {
start:
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill5 = alloca ptr, align 8
  %self.dbg.spill4 = alloca ptr, align 8
  %self.dbg.spill3 = alloca ptr, align 8
  %layout.dbg.spill = alloca { i64, i64 }, align 8
  %t.dbg.spill = alloca { i64, i64 }, align 8
  %self.dbg.spill = alloca ptr, align 8
  %pointer = alloca ptr, align 8
  %_11 = alloca ptr, align 8
  %_9 = alloca { ptr, { i64, i64 } }, align 8
  %self1 = alloca { i64, i64 }, align 8
  %_2 = alloca i8, align 1
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1149, metadata !DIExpression()), !dbg !1152
  call void @llvm.dbg.declare(metadata ptr %self1, metadata !1153, metadata !DIExpression()), !dbg !1162
  call void @llvm.dbg.declare(metadata ptr %pointer, metadata !1164, metadata !DIExpression()), !dbg !1171
  br i1 false, label %bb1, label %bb2, !dbg !1182

bb1:                                              ; preds = %start
  store i8 1, ptr %_2, align 1, !dbg !1182
  br label %bb3, !dbg !1182

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds { ptr, i64 }, ptr %self, i32 0, i32 1, !dbg !1183
  %_5 = load i64, ptr %1, align 8, !dbg !1183
  %_4 = icmp eq i64 %_5, 0, !dbg !1183
  %2 = zext i1 %_4 to i8, !dbg !1182
  store i8 %2, ptr %_2, align 1, !dbg !1182
  br label %bb3, !dbg !1182

bb3:                                              ; preds = %bb2, %bb1
  %3 = load i8, ptr %_2, align 1, !dbg !1182, !range !559, !noundef !23
  %4 = trunc i8 %3 to i1, !dbg !1182
  br i1 %4, label %bb4, label %bb5, !dbg !1182

bb5:                                              ; preds = %bb3
  %5 = getelementptr inbounds { ptr, i64 }, ptr %self, i32 0, i32 1, !dbg !1184
  %_8 = load i64, ptr %5, align 8, !dbg !1184
  %6 = call { i64, i64 } @_ZN4core5alloc6layout6Layout5array17h041a339ec38f7fddE(i64 %_8), !dbg !1163
  store { i64, i64 } %6, ptr %self1, align 8, !dbg !1163
  br label %bb6, !dbg !1163

bb4:                                              ; preds = %bb3
  %7 = getelementptr inbounds %"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>", ptr %0, i32 0, i32 1, !dbg !1185
  store i64 0, ptr %7, align 8, !dbg !1185
  br label %bb8, !dbg !1186

bb8:                                              ; preds = %bb7, %bb4
  ret void, !dbg !1187

bb6:                                              ; preds = %bb5
  %8 = getelementptr inbounds { i64, i64 }, ptr %self1, i32 0, i32 1, !dbg !1162
  %9 = load i64, ptr %8, align 8, !dbg !1162, !range !778, !noundef !23
  %10 = icmp eq i64 %9, 0, !dbg !1162
  %_15 = select i1 %10, i64 1, i64 0, !dbg !1162
  switch i64 %_15, label %bb10 [
    i64 0, label %bb11
    i64 1, label %bb9
  ], !dbg !1162

bb10:                                             ; preds = %bb6
  unreachable, !dbg !1162

bb11:                                             ; preds = %bb6
  %11 = getelementptr inbounds { i64, i64 }, ptr %self1, i32 0, i32 0, !dbg !1162
  %t.0 = load i64, ptr %11, align 8, !dbg !1162
  %12 = getelementptr inbounds { i64, i64 }, ptr %self1, i32 0, i32 1, !dbg !1162
  %t.1 = load i64, ptr %12, align 8, !dbg !1162, !range !752, !noundef !23
  %13 = getelementptr inbounds { i64, i64 }, ptr %t.dbg.spill, i32 0, i32 0, !dbg !1162
  store i64 %t.0, ptr %13, align 8, !dbg !1162
  %14 = getelementptr inbounds { i64, i64 }, ptr %t.dbg.spill, i32 0, i32 1, !dbg !1162
  store i64 %t.1, ptr %14, align 8, !dbg !1162
  call void @llvm.dbg.declare(metadata ptr %t.dbg.spill, metadata !1159, metadata !DIExpression()), !dbg !1188
  %15 = getelementptr inbounds { i64, i64 }, ptr %layout.dbg.spill, i32 0, i32 0, !dbg !1188
  store i64 %t.0, ptr %15, align 8, !dbg !1188
  %16 = getelementptr inbounds { i64, i64 }, ptr %layout.dbg.spill, i32 0, i32 1, !dbg !1188
  store i64 %t.1, ptr %16, align 8, !dbg !1188
  call void @llvm.dbg.declare(metadata ptr %layout.dbg.spill, metadata !1150, metadata !DIExpression()), !dbg !1189
  %17 = bitcast ptr %self to ptr, !dbg !1181
  %self2 = load ptr, ptr %17, align 8, !dbg !1181, !nonnull !23, !noundef !23
  store ptr %self2, ptr %self.dbg.spill3, align 8, !dbg !1181
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill3, metadata !1177, metadata !DIExpression()), !dbg !1190
  store ptr %self2, ptr %self.dbg.spill4, align 8, !dbg !1190
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill4, metadata !1191, metadata !DIExpression()), !dbg !1197
  store ptr %self2, ptr %self.dbg.spill5, align 8, !dbg !1197
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill5, metadata !1199, metadata !DIExpression()), !dbg !1203
  store ptr %self2, ptr %ptr.dbg.spill, align 8, !dbg !1197
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !1205, metadata !DIExpression()), !dbg !1209
  store ptr %self2, ptr %pointer, align 8, !dbg !1209
  %_26 = load ptr, ptr %pointer, align 8, !dbg !1171, !nonnull !23, !noundef !23
  store ptr %_26, ptr %_11, align 8, !dbg !1171
  %18 = load ptr, ptr %_11, align 8, !dbg !1181, !nonnull !23, !noundef !23
  %_10 = call ptr @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h093103a2bfe88da2E"(ptr %18), !dbg !1181
  br label %bb7, !dbg !1181

bb9:                                              ; preds = %bb6
  unreachable, !dbg !1211

bb7:                                              ; preds = %bb11
  %19 = bitcast ptr %_9 to ptr, !dbg !1215
  store ptr %_10, ptr %19, align 8, !dbg !1215
  %20 = getelementptr inbounds { ptr, { i64, i64 } }, ptr %_9, i32 0, i32 1, !dbg !1215
  %21 = getelementptr inbounds { i64, i64 }, ptr %20, i32 0, i32 0, !dbg !1215
  store i64 %t.0, ptr %21, align 8, !dbg !1215
  %22 = getelementptr inbounds { i64, i64 }, ptr %20, i32 0, i32 1, !dbg !1215
  store i64 %t.1, ptr %22, align 8, !dbg !1215
  %23 = bitcast ptr %0 to ptr, !dbg !1216
  %24 = bitcast ptr %23 to ptr, !dbg !1216
  %25 = bitcast ptr %24 to ptr, !dbg !1216
  %26 = bitcast ptr %_9 to ptr, !dbg !1216
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %25, ptr align 8 %26, i64 24, i1 false), !dbg !1216
  br label %bb8, !dbg !1186
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal zeroext i1 @"_ZN60_$LT$alloc..string..String$u20$as$u20$core..fmt..Display$GT$3fmt17hf3eccfebf7e287d9E"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 !dbg !1217 {
start:
  %f.dbg.spill = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1221, metadata !DIExpression()), !dbg !1223
  store ptr %f, ptr %f.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %f.dbg.spill, metadata !1222, metadata !DIExpression()), !dbg !1224
  %0 = call { ptr, i64 } @"_ZN65_$LT$alloc..string..String$u20$as$u20$core..ops..deref..Deref$GT$5deref17hb4bb5046c19f2651E"(ptr align 8 %self), !dbg !1225
  %_5.0 = extractvalue { ptr, i64 } %0, 0, !dbg !1225
  %_5.1 = extractvalue { ptr, i64 } %0, 1, !dbg !1225
  br label %bb1, !dbg !1225

bb1:                                              ; preds = %start
  %1 = call zeroext i1 @"_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17hde81f4d22eef4d42E"(ptr align 1 %_5.0, i64 %_5.1, ptr align 8 %f), !dbg !1226
  br label %bb2, !dbg !1226

bb2:                                              ; preds = %bb1
  ret i1 %1, !dbg !1227
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hc195185e441b0100E"(ptr align 1 %self, ptr %ptr, i64 %0, i64 %1) unnamed_addr #0 !dbg !1228 {
start:
  %n.dbg.spill = alloca i64, align 8
  %self.dbg.spill8 = alloca ptr, align 8
  %self.dbg.spill7 = alloca ptr, align 8
  %ptr.dbg.spill6 = alloca ptr, align 8
  %self.dbg.spill5 = alloca ptr, align 8
  %self.dbg.spill4 = alloca ptr, align 8
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  %self3 = alloca i64, align 8
  %self2 = alloca i64, align 8
  %layout1 = alloca { i64, i64 }, align 8
  %layout = alloca { i64, i64 }, align 8
  %2 = getelementptr inbounds { i64, i64 }, ptr %layout, i32 0, i32 0
  store i64 %0, ptr %2, align 8
  %3 = getelementptr inbounds { i64, i64 }, ptr %layout, i32 0, i32 1
  store i64 %1, ptr %3, align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1235, metadata !DIExpression()), !dbg !1238
  store ptr %ptr, ptr %ptr.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !1236, metadata !DIExpression()), !dbg !1239
  call void @llvm.dbg.declare(metadata ptr %layout, metadata !1237, metadata !DIExpression()), !dbg !1240
  call void @llvm.dbg.declare(metadata ptr %layout1, metadata !1241, metadata !DIExpression()), !dbg !1247
  call void @llvm.dbg.declare(metadata ptr %self2, metadata !1249, metadata !DIExpression()), !dbg !1253
  call void @llvm.dbg.declare(metadata ptr %self3, metadata !1263, metadata !DIExpression()), !dbg !1267
  store ptr %layout, ptr %self.dbg.spill4, align 8, !dbg !1268
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill4, metadata !1269, metadata !DIExpression()), !dbg !1273
  %4 = bitcast ptr %layout to ptr, !dbg !1273
  %_4 = load i64, ptr %4, align 8, !dbg !1273
  %5 = icmp eq i64 %_4, 0, !dbg !1268
  br i1 %5, label %bb2, label %bb1, !dbg !1268

bb2:                                              ; preds = %start
  br label %bb3, !dbg !1274

bb1:                                              ; preds = %start
  store ptr %ptr, ptr %self.dbg.spill5, align 8, !dbg !1275
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill5, metadata !1276, metadata !DIExpression()), !dbg !1280
  store ptr %ptr, ptr %ptr.dbg.spill6, align 8, !dbg !1280
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill6, metadata !1246, metadata !DIExpression()), !dbg !1247
  %6 = getelementptr inbounds { i64, i64 }, ptr %layout, i32 0, i32 0, !dbg !1281
  %7 = load i64, ptr %6, align 8, !dbg !1281
  %8 = getelementptr inbounds { i64, i64 }, ptr %layout, i32 0, i32 1, !dbg !1281
  %9 = load i64, ptr %8, align 8, !dbg !1281, !range !752, !noundef !23
  %10 = getelementptr inbounds { i64, i64 }, ptr %layout1, i32 0, i32 0, !dbg !1281
  store i64 %7, ptr %10, align 8, !dbg !1281
  %11 = getelementptr inbounds { i64, i64 }, ptr %layout1, i32 0, i32 1, !dbg !1281
  store i64 %9, ptr %11, align 8, !dbg !1281
  store ptr %layout1, ptr %self.dbg.spill7, align 8, !dbg !1247
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill7, metadata !1282, metadata !DIExpression()), !dbg !1286
  %12 = bitcast ptr %layout1 to ptr, !dbg !1286
  %_11 = load i64, ptr %12, align 8, !dbg !1286
  store ptr %layout1, ptr %self.dbg.spill8, align 8, !dbg !1247
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill8, metadata !1260, metadata !DIExpression()), !dbg !1288
  %13 = getelementptr inbounds { i64, i64 }, ptr %layout1, i32 0, i32 1, !dbg !1288
  %14 = load i64, ptr %13, align 8, !dbg !1288, !range !752, !noundef !23
  store i64 %14, ptr %self3, align 8, !dbg !1288
  %_18 = load i64, ptr %self3, align 8, !dbg !1267, !range !752, !noundef !23
  store i64 %_18, ptr %n.dbg.spill, align 8, !dbg !1267
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !1289, metadata !DIExpression()), !dbg !1296
  store i64 %_18, ptr %self2, align 8, !dbg !1296
  %_13 = load i64, ptr %self2, align 8, !dbg !1253
  call void @__rust_dealloc(ptr %ptr, i64 %_11, i64 %_13) #14, !dbg !1247
  br label %bb4, !dbg !1247

bb4:                                              ; preds = %bb1
  br label %bb3, !dbg !1274

bb3:                                              ; preds = %bb4, %bb2
  ret void, !dbg !1298
}

; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, i64 } @"_ZN65_$LT$alloc..string..String$u20$as$u20$core..ops..deref..Deref$GT$5deref17hb4bb5046c19f2651E"(ptr align 8 %self) unnamed_addr #0 !dbg !1299 {
start:
  %0 = alloca { ptr, i64 }, align 8
  %v.dbg.spill = alloca { ptr, i64 }, align 8
  %metadata.dbg.spill = alloca i64, align 8
  %data_address.dbg.spill = alloca ptr, align 8
  %self.dbg.spill4 = alloca ptr, align 8
  %len.dbg.spill3 = alloca i64, align 8
  %data.dbg.spill2 = alloca ptr, align 8
  %len.dbg.spill = alloca i64, align 8
  %data.dbg.spill = alloca ptr, align 8
  %self.dbg.spill1 = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  %_18 = alloca { ptr, i64 }, align 8
  %_17 = alloca %"core::ptr::metadata::PtrRepr<[u8]>", align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1304, metadata !DIExpression()), !dbg !1305
  %_5 = bitcast ptr %self to ptr, !dbg !1306
  store ptr %_5, ptr %self.dbg.spill1, align 8, !dbg !1306
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill1, metadata !1307, metadata !DIExpression()), !dbg !1314
  %data = call ptr @"_ZN5alloc3vec16Vec$LT$T$C$A$GT$6as_ptr17h107a2e3cbc7884cfE"(ptr align 8 %_5), !dbg !1314
  store ptr %data, ptr %data.dbg.spill, align 8, !dbg !1314
  call void @llvm.dbg.declare(metadata ptr %data.dbg.spill, metadata !1315, metadata !DIExpression()), !dbg !1334
  br label %bb1, !dbg !1314

bb1:                                              ; preds = %start
  %1 = getelementptr inbounds %"alloc::vec::Vec<u8>", ptr %_5, i32 0, i32 1, !dbg !1314
  %len = load i64, ptr %1, align 8, !dbg !1314
  store i64 %len, ptr %len.dbg.spill, align 8, !dbg !1314
  call void @llvm.dbg.declare(metadata ptr %len.dbg.spill, metadata !1324, metadata !DIExpression()), !dbg !1334
  store ptr %data, ptr %data.dbg.spill2, align 8, !dbg !1334
  call void @llvm.dbg.declare(metadata ptr %data.dbg.spill2, metadata !1336, metadata !DIExpression()), !dbg !1347
  store i64 %len, ptr %len.dbg.spill3, align 8, !dbg !1334
  call void @llvm.dbg.declare(metadata ptr %len.dbg.spill3, metadata !1346, metadata !DIExpression()), !dbg !1347
  store ptr %data, ptr %self.dbg.spill4, align 8, !dbg !1347
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill4, metadata !1349, metadata !DIExpression()), !dbg !1360
  %data_address = bitcast ptr %data to ptr, !dbg !1360
  store ptr %data_address, ptr %data_address.dbg.spill, align 8, !dbg !1360
  call void @llvm.dbg.declare(metadata ptr %data_address.dbg.spill, metadata !1362, metadata !DIExpression()), !dbg !1369
  store i64 %len, ptr %metadata.dbg.spill, align 8, !dbg !1347
  call void @llvm.dbg.declare(metadata ptr %metadata.dbg.spill, metadata !1368, metadata !DIExpression()), !dbg !1369
  %2 = bitcast ptr %_18 to ptr, !dbg !1369
  store ptr %data_address, ptr %2, align 8, !dbg !1369
  %3 = getelementptr inbounds { ptr, i64 }, ptr %_18, i32 0, i32 1, !dbg !1369
  store i64 %len, ptr %3, align 8, !dbg !1369
  %4 = bitcast ptr %_17 to ptr, !dbg !1369
  %5 = getelementptr inbounds { ptr, i64 }, ptr %_18, i32 0, i32 0, !dbg !1369
  %6 = load ptr, ptr %5, align 8, !dbg !1369
  %7 = getelementptr inbounds { ptr, i64 }, ptr %_18, i32 0, i32 1, !dbg !1369
  %8 = load i64, ptr %7, align 8, !dbg !1369
  %9 = getelementptr inbounds { ptr, i64 }, ptr %4, i32 0, i32 0, !dbg !1369
  store ptr %6, ptr %9, align 8, !dbg !1369
  %10 = getelementptr inbounds { ptr, i64 }, ptr %4, i32 0, i32 1, !dbg !1369
  store i64 %8, ptr %10, align 8, !dbg !1369
  %11 = bitcast ptr %_17 to ptr, !dbg !1369
  %12 = getelementptr inbounds { ptr, i64 }, ptr %11, i32 0, i32 0, !dbg !1369
  %_10.0 = load ptr, ptr %12, align 8, !dbg !1369
  %13 = getelementptr inbounds { ptr, i64 }, ptr %11, i32 0, i32 1, !dbg !1369
  %_10.1 = load i64, ptr %13, align 8, !dbg !1369
  %14 = getelementptr inbounds { ptr, i64 }, ptr %v.dbg.spill, i32 0, i32 0, !dbg !1306
  store ptr %_10.0, ptr %14, align 8, !dbg !1306
  %15 = getelementptr inbounds { ptr, i64 }, ptr %v.dbg.spill, i32 0, i32 1, !dbg !1306
  store i64 %_10.1, ptr %15, align 8, !dbg !1306
  call void @llvm.dbg.declare(metadata ptr %v.dbg.spill, metadata !1371, metadata !DIExpression()), !dbg !1379
  %16 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 0, !dbg !1379
  store ptr %_10.0, ptr %16, align 8, !dbg !1379
  %17 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 1, !dbg !1379
  store i64 %_10.1, ptr %17, align 8, !dbg !1379
  %18 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 0, !dbg !1379
  %19 = load ptr, ptr %18, align 8, !dbg !1379, !nonnull !23, !align !388, !noundef !23
  %20 = getelementptr inbounds { ptr, i64 }, ptr %0, i32 0, i32 1, !dbg !1379
  %21 = load i64, ptr %20, align 8, !dbg !1379
  br label %bb2, !dbg !1379

bb2:                                              ; preds = %bb1
  %22 = insertvalue { ptr, i64 } undef, ptr %19, 0, !dbg !1381
  %23 = insertvalue { ptr, i64 } %22, i64 %21, 1, !dbg !1381
  ret { ptr, i64 } %23, !dbg !1381
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN70_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h80e90bd87493e4d3E"(ptr align 8 %self) unnamed_addr #2 !dbg !1382 {
start:
  %metadata.dbg.spill = alloca i64, align 8
  %data_address.dbg.spill = alloca ptr, align 8
  %self.dbg.spill1 = alloca ptr, align 8
  %len.dbg.spill = alloca i64, align 8
  %data.dbg.spill = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  %_11 = alloca { ptr, i64 }, align 8
  %_10 = alloca %"core::ptr::metadata::PtrRepr<[u8]>", align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1387, metadata !DIExpression()), !dbg !1388
  %data = call ptr @"_ZN5alloc3vec16Vec$LT$T$C$A$GT$10as_mut_ptr17hf0ab5348698999aeE"(ptr align 8 %self), !dbg !1389
  store ptr %data, ptr %data.dbg.spill, align 8, !dbg !1389
  call void @llvm.dbg.declare(metadata ptr %data.dbg.spill, metadata !1390, metadata !DIExpression()), !dbg !1401
  br label %bb1, !dbg !1389

bb1:                                              ; preds = %start
  %0 = getelementptr inbounds %"alloc::vec::Vec<u8>", ptr %self, i32 0, i32 1, !dbg !1403
  %len = load i64, ptr %0, align 8, !dbg !1403
  store i64 %len, ptr %len.dbg.spill, align 8, !dbg !1403
  call void @llvm.dbg.declare(metadata ptr %len.dbg.spill, metadata !1400, metadata !DIExpression()), !dbg !1401
  store ptr %data, ptr %self.dbg.spill1, align 8, !dbg !1401
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill1, metadata !1404, metadata !DIExpression()), !dbg !1410
  %data_address = bitcast ptr %data to ptr, !dbg !1410
  store ptr %data_address, ptr %data_address.dbg.spill, align 8, !dbg !1410
  call void @llvm.dbg.declare(metadata ptr %data_address.dbg.spill, metadata !1412, metadata !DIExpression()), !dbg !1419
  store i64 %len, ptr %metadata.dbg.spill, align 8, !dbg !1401
  call void @llvm.dbg.declare(metadata ptr %metadata.dbg.spill, metadata !1418, metadata !DIExpression()), !dbg !1419
  %1 = bitcast ptr %_11 to ptr, !dbg !1419
  store ptr %data_address, ptr %1, align 8, !dbg !1419
  %2 = getelementptr inbounds { ptr, i64 }, ptr %_11, i32 0, i32 1, !dbg !1419
  store i64 %len, ptr %2, align 8, !dbg !1419
  %3 = bitcast ptr %_10 to ptr, !dbg !1419
  %4 = getelementptr inbounds { ptr, i64 }, ptr %_11, i32 0, i32 0, !dbg !1419
  %5 = load ptr, ptr %4, align 8, !dbg !1419
  %6 = getelementptr inbounds { ptr, i64 }, ptr %_11, i32 0, i32 1, !dbg !1419
  %7 = load i64, ptr %6, align 8, !dbg !1419
  %8 = getelementptr inbounds { ptr, i64 }, ptr %3, i32 0, i32 0, !dbg !1419
  store ptr %5, ptr %8, align 8, !dbg !1419
  %9 = getelementptr inbounds { ptr, i64 }, ptr %3, i32 0, i32 1, !dbg !1419
  store i64 %7, ptr %9, align 8, !dbg !1419
  %10 = bitcast ptr %_10 to ptr, !dbg !1419
  %11 = getelementptr inbounds { ptr, i64 }, ptr %10, i32 0, i32 0, !dbg !1419
  %_2.0 = load ptr, ptr %11, align 8, !dbg !1419
  %12 = getelementptr inbounds { ptr, i64 }, ptr %10, i32 0, i32 1, !dbg !1419
  %_2.1 = load i64, ptr %12, align 8, !dbg !1419
  br label %bb2, !dbg !1421

bb2:                                              ; preds = %bb1
  ret void, !dbg !1422
}

; Function Attrs: nonlazybind uwtable
define internal void @"_ZN77_$LT$alloc..raw_vec..RawVec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hf626a1dd0a70221dE"(ptr align 8 %self) unnamed_addr #2 !dbg !1423 {
start:
  %layout.dbg.spill = alloca { i64, i64 }, align 8
  %ptr.dbg.spill = alloca ptr, align 8
  %self.dbg.spill = alloca ptr, align 8
  %_2 = alloca %"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>", align 8
  store ptr %self, ptr %self.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %self.dbg.spill, metadata !1429, metadata !DIExpression()), !dbg !1433
  call void @"_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$14current_memory17hea955b31486f6310E"(ptr sret(%"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>") %_2, ptr align 8 %self), !dbg !1434
  br label %bb1, !dbg !1434

bb1:                                              ; preds = %start
  %0 = getelementptr inbounds %"core::option::Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>", ptr %_2, i32 0, i32 1, !dbg !1435
  %1 = load i64, ptr %0, align 8, !dbg !1435, !range !778, !noundef !23
  %2 = icmp eq i64 %1, 0, !dbg !1435
  %_4 = select i1 %2, i64 0, i64 1, !dbg !1435
  %3 = icmp eq i64 %_4, 1, !dbg !1435
  br i1 %3, label %bb2, label %bb4, !dbg !1435

bb2:                                              ; preds = %bb1
  %4 = bitcast ptr %_2 to ptr, !dbg !1436
  %5 = bitcast ptr %4 to ptr, !dbg !1436
  %6 = bitcast ptr %5 to ptr, !dbg !1436
  %ptr = load ptr, ptr %6, align 8, !dbg !1436, !nonnull !23, !noundef !23
  store ptr %ptr, ptr %ptr.dbg.spill, align 8, !dbg !1436
  call void @llvm.dbg.declare(metadata ptr %ptr.dbg.spill, metadata !1430, metadata !DIExpression()), !dbg !1436
  %7 = bitcast ptr %_2 to ptr, !dbg !1437
  %8 = bitcast ptr %7 to ptr, !dbg !1437
  %9 = getelementptr inbounds { ptr, { i64, i64 } }, ptr %8, i32 0, i32 1, !dbg !1437
  %10 = getelementptr inbounds { i64, i64 }, ptr %9, i32 0, i32 0, !dbg !1437
  %layout.0 = load i64, ptr %10, align 8, !dbg !1437
  %11 = getelementptr inbounds { i64, i64 }, ptr %9, i32 0, i32 1, !dbg !1437
  %layout.1 = load i64, ptr %11, align 8, !dbg !1437, !range !752, !noundef !23
  %12 = getelementptr inbounds { i64, i64 }, ptr %layout.dbg.spill, i32 0, i32 0, !dbg !1437
  store i64 %layout.0, ptr %12, align 8, !dbg !1437
  %13 = getelementptr inbounds { i64, i64 }, ptr %layout.dbg.spill, i32 0, i32 1, !dbg !1437
  store i64 %layout.1, ptr %13, align 8, !dbg !1437
  call void @llvm.dbg.declare(metadata ptr %layout.dbg.spill, metadata !1432, metadata !DIExpression()), !dbg !1437
  %_7 = bitcast ptr %self to ptr, !dbg !1438
  call void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hc195185e441b0100E"(ptr align 1 %_7, ptr %ptr, i64 %layout.0, i64 %layout.1), !dbg !1438
  br label %bb3, !dbg !1438

bb4:                                              ; preds = %bb3, %bb1
  ret void, !dbg !1439

bb3:                                              ; preds = %bb2
  br label %bb4, !dbg !1440
}

; Function Attrs: nonlazybind uwtable
define internal void @_ZN18build_script_build4main17h51fc63ceaa531570E() unnamed_addr #2 personality ptr @rust_eh_personality !dbg !1441 {
start:
  %0 = alloca { ptr, i32 }, align 8
  %_11 = alloca [1 x { ptr, ptr }], align 8
  %_4 = alloca %"core::fmt::Arguments", align 8
  %_2 = alloca %"core::result::Result<alloc::string::String, std::env::VarError>", align 8
  %manifest_dir = alloca %"alloc::string::String", align 8
  call void @llvm.dbg.declare(metadata ptr %manifest_dir, metadata !1445, metadata !DIExpression()), !dbg !1447
  call void @_ZN3std3env3var17h1ab2aebfffbd5e57E(ptr sret(%"core::result::Result<alloc::string::String, std::env::VarError>") %_2, ptr align 1 @alloc114, i64 18), !dbg !1448
  br label %bb1, !dbg !1448

bb1:                                              ; preds = %start
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17hc8210bfc41415118E"(ptr sret(%"alloc::string::String") %manifest_dir, ptr %_2, ptr align 8 @alloc116), !dbg !1448
  br label %bb2, !dbg !1448

bb2:                                              ; preds = %bb1
  %1 = invoke { ptr, ptr } @_ZN4core3fmt10ArgumentV111new_display17h8e936bdad87877f0E(ptr align 8 %manifest_dir)
          to label %bb3 unwind label %cleanup, !dbg !1449

bb7:                                              ; preds = %cleanup
  invoke void @"_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h017085301cfa8a38E"(ptr %manifest_dir) #12
          to label %bb8 unwind label %abort, !dbg !1450

cleanup:                                          ; preds = %bb4, %bb3, %bb2
  %2 = landingpad { ptr, i32 }
          cleanup
  %3 = extractvalue { ptr, i32 } %2, 0
  %4 = extractvalue { ptr, i32 } %2, 1
  %5 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 0
  store ptr %3, ptr %5, align 8
  %6 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 1
  store i32 %4, ptr %6, align 8
  br label %bb7

bb3:                                              ; preds = %bb2
  %_12.0 = extractvalue { ptr, ptr } %1, 0, !dbg !1449
  %_12.1 = extractvalue { ptr, ptr } %1, 1, !dbg !1449
  %7 = getelementptr inbounds [1 x { ptr, ptr }], ptr %_11, i64 0, i64 0, !dbg !1449
  %8 = getelementptr inbounds { ptr, ptr }, ptr %7, i32 0, i32 0, !dbg !1449
  store ptr %_12.0, ptr %8, align 8, !dbg !1449
  %9 = getelementptr inbounds { ptr, ptr }, ptr %7, i32 0, i32 1, !dbg !1449
  store ptr %_12.1, ptr %9, align 8, !dbg !1449
  %_8.0 = bitcast ptr %_11 to ptr, !dbg !1449
  invoke void @_ZN4core3fmt9Arguments6new_v117h4b70dcc115ea8332E(ptr sret(%"core::fmt::Arguments") %_4, ptr align 8 @alloc5, i64 2, ptr align 8 %_8.0, i64 1)
          to label %bb4 unwind label %cleanup, !dbg !1449

bb4:                                              ; preds = %bb3
  invoke void @_ZN3std2io5stdio6_print17h141fc01f1d2bd34dE(ptr %_4)
          to label %bb5 unwind label %cleanup, !dbg !1449

bb5:                                              ; preds = %bb4
  call void @"_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h017085301cfa8a38E"(ptr %manifest_dir), !dbg !1450
  br label %bb6, !dbg !1450

abort:                                            ; preds = %bb7
  %10 = landingpad { ptr, i32 }
          cleanup, !dbg !1451
  call void @_ZN4core9panicking15panic_no_unwind17h62f8113f44cbfcbfE() #13, !dbg !1451
  unreachable, !dbg !1451

bb8:                                              ; preds = %bb7
  %11 = bitcast ptr %0 to ptr, !dbg !1451
  %12 = load ptr, ptr %11, align 8, !dbg !1451
  %13 = getelementptr inbounds { ptr, i32 }, ptr %0, i32 0, i32 1, !dbg !1451
  %14 = load i32, ptr %13, align 8, !dbg !1451
  %15 = insertvalue { ptr, i32 } undef, ptr %12, 0, !dbg !1451
  %16 = insertvalue { ptr, i32 } %15, i32 %14, 1, !dbg !1451
  resume { ptr, i32 } %16, !dbg !1451

bb6:                                              ; preds = %bb5
  ret void, !dbg !1452
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #3

; Function Attrs: nonlazybind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #2

; Function Attrs: nonlazybind uwtable
declare i64 @_ZN3std2rt19lang_start_internal17h498f9556b87c8e5fE(ptr align 1, ptr align 8, i64, ptr) unnamed_addr #2

; Function Attrs: nonlazybind uwtable
declare void @_ZN3std3env4_var17h48effbaa8b2613b5E(ptr sret(%"core::result::Result<alloc::string::String, std::env::VarError>"), ptr align 1, i64) unnamed_addr #2

; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_ZN4core9panicking9panic_fmt17h62ccf03c8a8a51b5E(ptr, ptr align 8) unnamed_addr #4

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64) #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(none)
declare i1 @llvm.expect.i1(i1, i1) #5

; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_ZN4core9panicking15panic_no_unwind17h62f8113f44cbfcbfE() unnamed_addr #6

; Function Attrs: nonlazybind uwtable
declare zeroext i1 @"_ZN55_$LT$std..env..VarError$u20$as$u20$core..fmt..Debug$GT$3fmt17he46da4fdbd9f8b4bE"(ptr align 8, ptr align 8) unnamed_addr #2

; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_ZN4core6result13unwrap_failed17hff48f82f03d418aeE(ptr align 1, i64, ptr align 1, ptr align 8, ptr align 8) unnamed_addr #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write)
declare void @llvm.assume(i1 noundef) #7

; Function Attrs: nonlazybind uwtable
declare zeroext i1 @"_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17hde81f4d22eef4d42E"(ptr align 1, i64, ptr align 8) unnamed_addr #2

; Function Attrs: nounwind nonlazybind uwtable
declare void @__rust_dealloc(ptr, i64, i64) unnamed_addr #8

; Function Attrs: nonlazybind uwtable
declare void @_ZN3std2io5stdio6_print17h141fc01f1d2bd34dE(ptr) unnamed_addr #2

; Function Attrs: nonlazybind
define i32 @main(i32 %0, ptr %1) unnamed_addr #9 {
top:
  %2 = load volatile i8, ptr @__rustc_debug_gdb_scripts_section__, align 1
  %3 = sext i32 %0 to i64
  %4 = call i64 @_ZN3std2rt10lang_start17he4b4cd36ba5e3c57E(ptr @_ZN18build_script_build4main17h51fc63ceaa531570E, i64 %3, ptr %1)
  %5 = trunc i64 %4 to i32
  ret i32 %5
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #10

attributes #0 = { inlinehint nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #1 = { noinline nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #2 = { nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #3 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #4 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(none) }
attributes #6 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #7 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write) }
attributes #8 = { nounwind nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #9 = { nonlazybind "target-cpu"="x86-64" }
attributes #10 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #11 = { noreturn }
attributes #12 = { noinline }
attributes #13 = { noinline noreturn nounwind }
attributes #14 = { nounwind }

!llvm.module.flags = !{!89, !90, !91, !92, !93}
!llvm.dbg.cu = !{!94}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "<std::rt::lang_start::{closure_env#0}<()> as core::ops::function::Fn<()>>::{vtable}", scope: null, file: !2, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "<unknown>", directory: "")
!3 = !DICompositeType(tag: DW_TAG_structure_type, name: "<std::rt::lang_start::{closure_env#0}<()> as core::ops::function::Fn<()>>::{vtable_type}", file: !2, size: 384, align: 64, flags: DIFlagArtificial, elements: !4, vtableHolder: !14, templateParams: !23, identifier: "dee041a15dfe076460e1ead4b963607c")
!4 = !{!5, !8, !10, !11, !12, !13}
!5 = !DIDerivedType(tag: DW_TAG_member, name: "drop_in_place", scope: !3, file: !2, baseType: !6, size: 64, align: 64)
!6 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*const ()", baseType: !7, size: 64, align: 64, dwarfAddressSpace: 0)
!7 = !DIBasicType(name: "()", encoding: DW_ATE_unsigned)
!8 = !DIDerivedType(tag: DW_TAG_member, name: "size", scope: !3, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!9 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!10 = !DIDerivedType(tag: DW_TAG_member, name: "align", scope: !3, file: !2, baseType: !9, size: 64, align: 64, offset: 128)
!11 = !DIDerivedType(tag: DW_TAG_member, name: "__method3", scope: !3, file: !2, baseType: !6, size: 64, align: 64, offset: 192)
!12 = !DIDerivedType(tag: DW_TAG_member, name: "__method4", scope: !3, file: !2, baseType: !6, size: 64, align: 64, offset: 256)
!13 = !DIDerivedType(tag: DW_TAG_member, name: "__method5", scope: !3, file: !2, baseType: !6, size: 64, align: 64, offset: 320)
!14 = !DICompositeType(tag: DW_TAG_structure_type, name: "{closure_env#0}<()>", scope: !15, file: !2, size: 64, align: 64, elements: !18, templateParams: !23, identifier: "eb9421142c7534b89a47eb687fc5227b")
!15 = !DINamespace(name: "lang_start", scope: !16)
!16 = !DINamespace(name: "rt", scope: !17)
!17 = !DINamespace(name: "std", scope: null)
!18 = !{!19}
!19 = !DIDerivedType(tag: DW_TAG_member, name: "main", scope: !14, file: !2, baseType: !20, size: 64, align: 64)
!20 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "fn()", baseType: !21, size: 64, align: 64, dwarfAddressSpace: 0)
!21 = !DISubroutineType(types: !22)
!22 = !{null}
!23 = !{}
!24 = !DIGlobalVariableExpression(var: !25, expr: !DIExpression())
!25 = distinct !DIGlobalVariable(name: "<std::env::VarError as core::fmt::Debug>::{vtable}", scope: null, file: !2, type: !26, isLocal: true, isDefinition: true)
!26 = !DICompositeType(tag: DW_TAG_structure_type, name: "<std::env::VarError as core::fmt::Debug>::{vtable_type}", file: !2, size: 256, align: 64, flags: DIFlagArtificial, elements: !27, vtableHolder: !32, templateParams: !23, identifier: "ccbbf1710fb61c32bb15a29c6020dd04")
!27 = !{!28, !29, !30, !31}
!28 = !DIDerivedType(tag: DW_TAG_member, name: "drop_in_place", scope: !26, file: !2, baseType: !6, size: 64, align: 64)
!29 = !DIDerivedType(tag: DW_TAG_member, name: "size", scope: !26, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!30 = !DIDerivedType(tag: DW_TAG_member, name: "align", scope: !26, file: !2, baseType: !9, size: 64, align: 64, offset: 128)
!31 = !DIDerivedType(tag: DW_TAG_member, name: "__method3", scope: !26, file: !2, baseType: !6, size: 64, align: 64, offset: 192)
!32 = !DICompositeType(tag: DW_TAG_structure_type, name: "VarError", scope: !33, file: !2, size: 192, align: 64, elements: !34, templateParams: !23, identifier: "8046a220ebaf00ea9dba1b36877933c")
!33 = !DINamespace(name: "env", scope: !17)
!34 = !{!35}
!35 = !DICompositeType(tag: DW_TAG_variant_part, scope: !32, file: !2, size: 192, align: 64, elements: !36, templateParams: !23, identifier: "6a13e0b48b8114a51dcf4b3ba20dd95a", discriminator: !87)
!36 = !{!37, !39}
!37 = !DIDerivedType(tag: DW_TAG_member, name: "NotPresent", scope: !35, file: !2, baseType: !38, size: 192, align: 64, extraData: i64 0)
!38 = !DICompositeType(tag: DW_TAG_structure_type, name: "NotPresent", scope: !32, file: !2, size: 192, align: 64, elements: !23, identifier: "1451b8589f47f6e42a9c4255dedfaba5")
!39 = !DIDerivedType(tag: DW_TAG_member, name: "NotUnicode", scope: !35, file: !2, baseType: !40, size: 192, align: 64)
!40 = !DICompositeType(tag: DW_TAG_structure_type, name: "NotUnicode", scope: !32, file: !2, size: 192, align: 64, elements: !41, templateParams: !23, identifier: "5456c1511e4ce8fdf30239994548b8c")
!41 = !{!42}
!42 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !40, file: !2, baseType: !43, size: 192, align: 64)
!43 = !DICompositeType(tag: DW_TAG_structure_type, name: "OsString", scope: !44, file: !2, size: 192, align: 64, elements: !46, templateParams: !23, identifier: "454fd02cfcb0b08abf1fd1aab45238b0")
!44 = !DINamespace(name: "os_str", scope: !45)
!45 = !DINamespace(name: "ffi", scope: !17)
!46 = !{!47}
!47 = !DIDerivedType(tag: DW_TAG_member, name: "inner", scope: !43, file: !2, baseType: !48, size: 192, align: 64)
!48 = !DICompositeType(tag: DW_TAG_structure_type, name: "Buf", scope: !49, file: !2, size: 192, align: 64, elements: !52, templateParams: !23, identifier: "d1927bc8800b0f11dc3d6fb85fbbef70")
!49 = !DINamespace(name: "os_str", scope: !50)
!50 = !DINamespace(name: "unix", scope: !51)
!51 = !DINamespace(name: "sys", scope: !17)
!52 = !{!53}
!53 = !DIDerivedType(tag: DW_TAG_member, name: "inner", scope: !48, file: !2, baseType: !54, size: 192, align: 64)
!54 = !DICompositeType(tag: DW_TAG_structure_type, name: "Vec<u8, alloc::alloc::Global>", scope: !55, file: !2, size: 192, align: 64, elements: !57, templateParams: !84, identifier: "f48a096c1ed19eb7ba15a7173429013")
!55 = !DINamespace(name: "vec", scope: !56)
!56 = !DINamespace(name: "alloc", scope: null)
!57 = !{!58, !86}
!58 = !DIDerivedType(tag: DW_TAG_member, name: "buf", scope: !54, file: !2, baseType: !59, size: 128, align: 64)
!59 = !DICompositeType(tag: DW_TAG_structure_type, name: "RawVec<u8, alloc::alloc::Global>", scope: !60, file: !2, size: 128, align: 64, elements: !61, templateParams: !84, identifier: "d09dab1a097018b9dd4dad6f3ce84c27")
!60 = !DINamespace(name: "raw_vec", scope: !56)
!61 = !{!62, !80, !81}
!62 = !DIDerivedType(tag: DW_TAG_member, name: "ptr", scope: !59, file: !2, baseType: !63, size: 64, align: 64)
!63 = !DICompositeType(tag: DW_TAG_structure_type, name: "Unique<u8>", scope: !64, file: !2, size: 64, align: 64, elements: !67, templateParams: !75, identifier: "7e72c5db004520f6d0779c7d4ace2142")
!64 = !DINamespace(name: "unique", scope: !65)
!65 = !DINamespace(name: "ptr", scope: !66)
!66 = !DINamespace(name: "core", scope: null)
!67 = !{!68, !77}
!68 = !DIDerivedType(tag: DW_TAG_member, name: "pointer", scope: !63, file: !2, baseType: !69, size: 64, align: 64)
!69 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonNull<u8>", scope: !70, file: !2, size: 64, align: 64, elements: !71, templateParams: !75, identifier: "3160283ea80cecf6149fff38a2e996de")
!70 = !DINamespace(name: "non_null", scope: !65)
!71 = !{!72}
!72 = !DIDerivedType(tag: DW_TAG_member, name: "pointer", scope: !69, file: !2, baseType: !73, size: 64, align: 64)
!73 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*const u8", baseType: !74, size: 64, align: 64, dwarfAddressSpace: 0)
!74 = !DIBasicType(name: "u8", size: 8, encoding: DW_ATE_unsigned)
!75 = !{!76}
!76 = !DITemplateTypeParameter(name: "T", type: !74)
!77 = !DIDerivedType(tag: DW_TAG_member, name: "_marker", scope: !63, file: !2, baseType: !78, align: 8)
!78 = !DICompositeType(tag: DW_TAG_structure_type, name: "PhantomData<u8>", scope: !79, file: !2, align: 8, elements: !23, templateParams: !75, identifier: "e338a8151f1037c76eadd10ab3c53972")
!79 = !DINamespace(name: "marker", scope: !66)
!80 = !DIDerivedType(tag: DW_TAG_member, name: "cap", scope: !59, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!81 = !DIDerivedType(tag: DW_TAG_member, name: "alloc", scope: !59, file: !2, baseType: !82, align: 8)
!82 = !DICompositeType(tag: DW_TAG_structure_type, name: "Global", scope: !83, file: !2, align: 8, elements: !23, identifier: "3328ba4994ba07f4a4a3e83fae935932")
!83 = !DINamespace(name: "alloc", scope: !56)
!84 = !{!76, !85}
!85 = !DITemplateTypeParameter(name: "A", type: !82)
!86 = !DIDerivedType(tag: DW_TAG_member, name: "len", scope: !54, file: !2, baseType: !9, size: 64, align: 64, offset: 128)
!87 = !DIDerivedType(tag: DW_TAG_member, scope: !32, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!88 = !DIBasicType(name: "u64", size: 64, encoding: DW_ATE_unsigned)
!89 = !{i32 8, !"PIC Level", i32 2}
!90 = !{i32 7, !"PIE Level", i32 2}
!91 = !{i32 2, !"RtLibUseGOT", i32 1}
!92 = !{i32 2, !"Dwarf Version", i32 4}
!93 = !{i32 2, !"Debug Info Version", i32 3}
!94 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !95, producer: "clang LLVM (rustc version 1.65.0-nightly (d394408fb 2022-08-07))", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !96, globals: !174)
!95 = !DIFile(filename: "build.rs/@/50xxd17d9t8dq3o4", directory: "/home/val/c2rust/tests/enums")
!96 = !{!97, !106}
!97 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "Alignment", scope: !98, file: !2, baseType: !74, size: 8, align: 8, flags: DIFlagEnumClass, elements: !101)
!98 = !DINamespace(name: "v1", scope: !99)
!99 = !DINamespace(name: "rt", scope: !100)
!100 = !DINamespace(name: "fmt", scope: !66)
!101 = !{!102, !103, !104, !105}
!102 = !DIEnumerator(name: "Left", value: 0, isUnsigned: true)
!103 = !DIEnumerator(name: "Right", value: 1, isUnsigned: true)
!104 = !DIEnumerator(name: "Center", value: 2, isUnsigned: true)
!105 = !DIEnumerator(name: "Unknown", value: 3, isUnsigned: true)
!106 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "ValidAlignEnum64", scope: !107, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagEnumClass, elements: !109)
!107 = !DINamespace(name: "valid_align", scope: !108)
!108 = !DINamespace(name: "mem", scope: !66)
!109 = !{!110, !111, !112, !113, !114, !115, !116, !117, !118, !119, !120, !121, !122, !123, !124, !125, !126, !127, !128, !129, !130, !131, !132, !133, !134, !135, !136, !137, !138, !139, !140, !141, !142, !143, !144, !145, !146, !147, !148, !149, !150, !151, !152, !153, !154, !155, !156, !157, !158, !159, !160, !161, !162, !163, !164, !165, !166, !167, !168, !169, !170, !171, !172, !173}
!110 = !DIEnumerator(name: "_Align1Shl0", value: 1, isUnsigned: true)
!111 = !DIEnumerator(name: "_Align1Shl1", value: 2, isUnsigned: true)
!112 = !DIEnumerator(name: "_Align1Shl2", value: 4, isUnsigned: true)
!113 = !DIEnumerator(name: "_Align1Shl3", value: 8, isUnsigned: true)
!114 = !DIEnumerator(name: "_Align1Shl4", value: 16, isUnsigned: true)
!115 = !DIEnumerator(name: "_Align1Shl5", value: 32, isUnsigned: true)
!116 = !DIEnumerator(name: "_Align1Shl6", value: 64, isUnsigned: true)
!117 = !DIEnumerator(name: "_Align1Shl7", value: 128, isUnsigned: true)
!118 = !DIEnumerator(name: "_Align1Shl8", value: 256, isUnsigned: true)
!119 = !DIEnumerator(name: "_Align1Shl9", value: 512, isUnsigned: true)
!120 = !DIEnumerator(name: "_Align1Shl10", value: 1024, isUnsigned: true)
!121 = !DIEnumerator(name: "_Align1Shl11", value: 2048, isUnsigned: true)
!122 = !DIEnumerator(name: "_Align1Shl12", value: 4096, isUnsigned: true)
!123 = !DIEnumerator(name: "_Align1Shl13", value: 8192, isUnsigned: true)
!124 = !DIEnumerator(name: "_Align1Shl14", value: 16384, isUnsigned: true)
!125 = !DIEnumerator(name: "_Align1Shl15", value: 32768, isUnsigned: true)
!126 = !DIEnumerator(name: "_Align1Shl16", value: 65536, isUnsigned: true)
!127 = !DIEnumerator(name: "_Align1Shl17", value: 131072, isUnsigned: true)
!128 = !DIEnumerator(name: "_Align1Shl18", value: 262144, isUnsigned: true)
!129 = !DIEnumerator(name: "_Align1Shl19", value: 524288, isUnsigned: true)
!130 = !DIEnumerator(name: "_Align1Shl20", value: 1048576, isUnsigned: true)
!131 = !DIEnumerator(name: "_Align1Shl21", value: 2097152, isUnsigned: true)
!132 = !DIEnumerator(name: "_Align1Shl22", value: 4194304, isUnsigned: true)
!133 = !DIEnumerator(name: "_Align1Shl23", value: 8388608, isUnsigned: true)
!134 = !DIEnumerator(name: "_Align1Shl24", value: 16777216, isUnsigned: true)
!135 = !DIEnumerator(name: "_Align1Shl25", value: 33554432, isUnsigned: true)
!136 = !DIEnumerator(name: "_Align1Shl26", value: 67108864, isUnsigned: true)
!137 = !DIEnumerator(name: "_Align1Shl27", value: 134217728, isUnsigned: true)
!138 = !DIEnumerator(name: "_Align1Shl28", value: 268435456, isUnsigned: true)
!139 = !DIEnumerator(name: "_Align1Shl29", value: 536870912, isUnsigned: true)
!140 = !DIEnumerator(name: "_Align1Shl30", value: 1073741824, isUnsigned: true)
!141 = !DIEnumerator(name: "_Align1Shl31", value: 2147483648, isUnsigned: true)
!142 = !DIEnumerator(name: "_Align1Shl32", value: 4294967296, isUnsigned: true)
!143 = !DIEnumerator(name: "_Align1Shl33", value: 8589934592, isUnsigned: true)
!144 = !DIEnumerator(name: "_Align1Shl34", value: 17179869184, isUnsigned: true)
!145 = !DIEnumerator(name: "_Align1Shl35", value: 34359738368, isUnsigned: true)
!146 = !DIEnumerator(name: "_Align1Shl36", value: 68719476736, isUnsigned: true)
!147 = !DIEnumerator(name: "_Align1Shl37", value: 137438953472, isUnsigned: true)
!148 = !DIEnumerator(name: "_Align1Shl38", value: 274877906944, isUnsigned: true)
!149 = !DIEnumerator(name: "_Align1Shl39", value: 549755813888, isUnsigned: true)
!150 = !DIEnumerator(name: "_Align1Shl40", value: 1099511627776, isUnsigned: true)
!151 = !DIEnumerator(name: "_Align1Shl41", value: 2199023255552, isUnsigned: true)
!152 = !DIEnumerator(name: "_Align1Shl42", value: 4398046511104, isUnsigned: true)
!153 = !DIEnumerator(name: "_Align1Shl43", value: 8796093022208, isUnsigned: true)
!154 = !DIEnumerator(name: "_Align1Shl44", value: 17592186044416, isUnsigned: true)
!155 = !DIEnumerator(name: "_Align1Shl45", value: 35184372088832, isUnsigned: true)
!156 = !DIEnumerator(name: "_Align1Shl46", value: 70368744177664, isUnsigned: true)
!157 = !DIEnumerator(name: "_Align1Shl47", value: 140737488355328, isUnsigned: true)
!158 = !DIEnumerator(name: "_Align1Shl48", value: 281474976710656, isUnsigned: true)
!159 = !DIEnumerator(name: "_Align1Shl49", value: 562949953421312, isUnsigned: true)
!160 = !DIEnumerator(name: "_Align1Shl50", value: 1125899906842624, isUnsigned: true)
!161 = !DIEnumerator(name: "_Align1Shl51", value: 2251799813685248, isUnsigned: true)
!162 = !DIEnumerator(name: "_Align1Shl52", value: 4503599627370496, isUnsigned: true)
!163 = !DIEnumerator(name: "_Align1Shl53", value: 9007199254740992, isUnsigned: true)
!164 = !DIEnumerator(name: "_Align1Shl54", value: 18014398509481984, isUnsigned: true)
!165 = !DIEnumerator(name: "_Align1Shl55", value: 36028797018963968, isUnsigned: true)
!166 = !DIEnumerator(name: "_Align1Shl56", value: 72057594037927936, isUnsigned: true)
!167 = !DIEnumerator(name: "_Align1Shl57", value: 144115188075855872, isUnsigned: true)
!168 = !DIEnumerator(name: "_Align1Shl58", value: 288230376151711744, isUnsigned: true)
!169 = !DIEnumerator(name: "_Align1Shl59", value: 576460752303423488, isUnsigned: true)
!170 = !DIEnumerator(name: "_Align1Shl60", value: 1152921504606846976, isUnsigned: true)
!171 = !DIEnumerator(name: "_Align1Shl61", value: 2305843009213693952, isUnsigned: true)
!172 = !DIEnumerator(name: "_Align1Shl62", value: 4611686018427387904, isUnsigned: true)
!173 = !DIEnumerator(name: "_Align1Shl63", value: 9223372036854775808, isUnsigned: true)
!174 = !{!0, !24}
!175 = distinct !DISubprogram(name: "from<u8>", linkageName: "_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd6350e6730446559E", scope: !177, file: !176, line: 770, type: !178, scopeLine: 770, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !180)
!176 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/non_null.rs", directory: "", checksumkind: CSK_MD5, checksum: "856acc92efd7925b83dd1e3c577ddbdc")
!177 = !DINamespace(name: "{impl#16}", scope: !70)
!178 = !DISubroutineType(types: !179)
!179 = !{!69, !63}
!180 = !{!181}
!181 = !DILocalVariable(name: "unique", arg: 1, scope: !175, file: !176, line: 770, type: !63)
!182 = !DILocation(line: 770, column: 13, scope: !175)
!183 = !DILocation(line: 773, column: 41, scope: !175)
!184 = !DILocalVariable(name: "self", scope: !185, file: !176, line: 773, type: !63, align: 8)
!185 = !DILexicalBlockFile(scope: !186, file: !176, discriminator: 0)
!186 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha55716535ab1b589E", scope: !63, file: !187, line: 103, type: !188, scopeLine: 103, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !191)
!187 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/unique.rs", directory: "", checksumkind: CSK_MD5, checksum: "acdefab5f14df6e5aef1141fd6b768c9")
!188 = !DISubroutineType(types: !189)
!189 = !{!190, !63}
!190 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut u8", baseType: !74, size: 64, align: 64, dwarfAddressSpace: 0)
!191 = !{!184}
!192 = !DILocation(line: 773, column: 41, scope: !185, inlinedAt: !183)
!193 = !DILocalVariable(name: "self", scope: !194, file: !176, line: 773, type: !69, align: 8)
!194 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17hf95529f8199b6675E", scope: !69, file: !176, line: 330, type: !195, scopeLine: 330, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !197)
!195 = !DISubroutineType(types: !196)
!196 = !{!190, !69}
!197 = !{!193}
!198 = !DILocation(line: 773, column: 41, scope: !194, inlinedAt: !199)
!199 = !DILocation(line: 104, column: 9, scope: !186, inlinedAt: !183)
!200 = !DILocalVariable(name: "ptr", scope: !201, file: !176, line: 773, type: !190, align: 8)
!201 = distinct !DISubprogram(name: "new_unchecked<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h9e66c3bf20657540E", scope: !69, file: !176, line: 196, type: !202, scopeLine: 196, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !204)
!202 = !DISubroutineType(types: !203)
!203 = !{!69, !190}
!204 = !{!200}
!205 = !DILocation(line: 773, column: 18, scope: !201, inlinedAt: !206)
!206 = !DILocation(line: 773, column: 18, scope: !175)
!207 = !DILocation(line: 774, column: 6, scope: !175)
!208 = distinct !DISubprogram(name: "__rust_begin_short_backtrace<fn(), ()>", linkageName: "_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17hb7516deb05ead5dbE", scope: !210, file: !209, line: 118, type: !212, scopeLine: 118, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !218, retainedNodes: !214)
!209 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/sys_common/backtrace.rs", directory: "", checksumkind: CSK_MD5, checksum: "f7c76d4902bfcea1d96ffad8fbde919d")
!210 = !DINamespace(name: "backtrace", scope: !211)
!211 = !DINamespace(name: "sys_common", scope: !17)
!212 = !DISubroutineType(types: !213)
!213 = !{null, !20}
!214 = !{!215, !216}
!215 = !DILocalVariable(name: "f", arg: 1, scope: !208, file: !209, line: 118, type: !20)
!216 = !DILocalVariable(name: "result", scope: !217, file: !209, line: 122, type: !7, align: 1)
!217 = distinct !DILexicalBlock(scope: !208, file: !209, line: 122, column: 5)
!218 = !{!219, !220}
!219 = !DITemplateTypeParameter(name: "F", type: !20)
!220 = !DITemplateTypeParameter(name: "T", type: !7)
!221 = !DILocation(line: 122, column: 9, scope: !217)
!222 = !DILocation(line: 118, column: 43, scope: !208)
!223 = !DILocalVariable(name: "dummy", scope: !224, file: !209, line: 125, type: !7, align: 1)
!224 = !DILexicalBlockFile(scope: !225, file: !209, discriminator: 0)
!225 = distinct !DISubprogram(name: "black_box<()>", linkageName: "_ZN4core4hint9black_box17hb7fd115d2c4a91cfE", scope: !227, file: !226, line: 225, type: !228, scopeLine: 225, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !231, retainedNodes: !230)
!226 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/hint.rs", directory: "", checksumkind: CSK_MD5, checksum: "b50bd4586a98539d3cdc821cfaa5e2e7")
!227 = !DINamespace(name: "hint", scope: !66)
!228 = !DISubroutineType(types: !229)
!229 = !{null, !7}
!230 = !{!223}
!231 = !{!220}
!232 = !DILocation(line: 125, column: 5, scope: !224, inlinedAt: !233)
!233 = !DILocation(line: 125, column: 5, scope: !217)
!234 = !DILocation(line: 122, column: 18, scope: !208)
!235 = !{i32 3340996}
!236 = !DILocation(line: 128, column: 2, scope: !208)
!237 = !DILocation(line: 128, column: 1, scope: !208)
!238 = !DILocation(line: 118, column: 1, scope: !208)
!239 = distinct !DISubprogram(name: "lang_start<()>", linkageName: "_ZN3std2rt10lang_start17he4b4cd36ba5e3c57E", scope: !16, file: !240, line: 139, type: !241, scopeLine: 139, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !231, retainedNodes: !245)
!240 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/rt.rs", directory: "", checksumkind: CSK_MD5, checksum: "53ba40c54b421907f2e3ab22fb96d5b4")
!241 = !DISubroutineType(types: !242)
!242 = !{!243, !20, !243, !244}
!243 = !DIBasicType(name: "isize", size: 64, encoding: DW_ATE_signed)
!244 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*const *const u8", baseType: !73, size: 64, align: 64, dwarfAddressSpace: 0)
!245 = !{!246, !247, !248, !249}
!246 = !DILocalVariable(name: "main", arg: 1, scope: !239, file: !240, line: 140, type: !20)
!247 = !DILocalVariable(name: "argc", arg: 2, scope: !239, file: !240, line: 141, type: !243)
!248 = !DILocalVariable(name: "argv", arg: 3, scope: !239, file: !240, line: 142, type: !244)
!249 = !DILocalVariable(name: "v", scope: !250, file: !240, line: 144, type: !243, align: 8)
!250 = distinct !DILexicalBlock(scope: !239, file: !240, line: 144, column: 5)
!251 = !DILocation(line: 140, column: 5, scope: !239)
!252 = !DILocation(line: 141, column: 5, scope: !239)
!253 = !DILocation(line: 142, column: 5, scope: !239)
!254 = !DILocation(line: 145, column: 10, scope: !239)
!255 = !DILocation(line: 145, column: 9, scope: !239)
!256 = !DILocation(line: 144, column: 17, scope: !239)
!257 = !DILocation(line: 144, column: 12, scope: !239)
!258 = !DILocation(line: 144, column: 12, scope: !250)
!259 = !DILocation(line: 150, column: 2, scope: !239)
!260 = distinct !DISubprogram(name: "{closure#0}<()>", linkageName: "_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E", scope: !15, file: !240, line: 145, type: !261, scopeLine: 145, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !231, retainedNodes: !265)
!261 = !DISubroutineType(types: !262)
!262 = !{!263, !264}
!263 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!264 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&std::rt::lang_start::{closure_env#0}<()>", baseType: !14, size: 64, align: 64, dwarfAddressSpace: 0)
!265 = !{!266}
!266 = !DILocalVariable(name: "main", scope: !260, file: !240, line: 140, type: !20, align: 8)
!267 = !{i64 8}
!268 = !DILocation(line: 140, column: 5, scope: !260)
!269 = !DILocalVariable(name: "self", scope: !270, file: !240, line: 145, type: !273, align: 1)
!270 = !DILexicalBlockFile(scope: !271, file: !240, discriminator: 0)
!271 = distinct !DISubprogram(name: "to_i32", linkageName: "_ZN3std7process8ExitCode6to_i3217hebde0c81b647a5b2E", scope: !273, file: !272, line: 1808, type: !282, scopeLine: 1808, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !284)
!272 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/process.rs", directory: "", checksumkind: CSK_MD5, checksum: "78747cd94138b7f073ffd16b64787cb4")
!273 = !DICompositeType(tag: DW_TAG_structure_type, name: "ExitCode", scope: !274, file: !2, size: 8, align: 8, elements: !275, templateParams: !23, identifier: "65270507d071436c1dbdf6fde69e5261")
!274 = !DINamespace(name: "process", scope: !17)
!275 = !{!276}
!276 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !273, file: !2, baseType: !277, size: 8, align: 8)
!277 = !DICompositeType(tag: DW_TAG_structure_type, name: "ExitCode", scope: !278, file: !2, size: 8, align: 8, elements: !280, templateParams: !23, identifier: "faca173619846f0e95e842844eb5af74")
!278 = !DINamespace(name: "process_common", scope: !279)
!279 = !DINamespace(name: "process", scope: !50)
!280 = !{!281}
!281 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !277, file: !2, baseType: !74, size: 8, align: 8)
!282 = !DISubroutineType(types: !283)
!283 = !{!263, !273}
!284 = !{!269}
!285 = !DILocation(line: 145, column: 18, scope: !270, inlinedAt: !286)
!286 = !DILocation(line: 145, column: 18, scope: !260)
!287 = !DILocation(line: 145, column: 77, scope: !260)
!288 = !DILocalVariable(name: "self", scope: !289, file: !240, line: 145, type: !294, align: 8)
!289 = !DILexicalBlockFile(scope: !290, file: !240, discriminator: 0)
!290 = distinct !DISubprogram(name: "as_i32", linkageName: "_ZN3std3sys4unix7process14process_common8ExitCode6as_i3217h3a893a11dac84e60E", scope: !277, file: !291, line: 485, type: !292, scopeLine: 485, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !295)
!291 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/sys/unix/process/process_common.rs", directory: "", checksumkind: CSK_MD5, checksum: "0172c472c69d772c784713c132680582")
!292 = !DISubroutineType(types: !293)
!293 = !{!263, !294}
!294 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&std::sys::unix::process::process_common::ExitCode", baseType: !277, size: 64, align: 64, dwarfAddressSpace: 0)
!295 = !{!288}
!296 = !DILocation(line: 145, column: 18, scope: !289, inlinedAt: !297)
!297 = !DILocation(line: 1809, column: 9, scope: !271, inlinedAt: !286)
!298 = !DILocation(line: 145, column: 17, scope: !260)
!299 = distinct !DISubprogram(name: "var<&str>", linkageName: "_ZN3std3env3var17h1ab2aebfffbd5e57E", scope: !33, file: !300, line: 227, type: !301, scopeLine: 227, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !331, retainedNodes: !329)
!300 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/env.rs", directory: "", checksumkind: CSK_MD5, checksum: "eb997a355b779581a425ead6cf0f1655")
!301 = !DISubroutineType(types: !302)
!302 = !{!303, !324}
!303 = !DICompositeType(tag: DW_TAG_structure_type, name: "Result<alloc::string::String, std::env::VarError>", scope: !304, file: !2, size: 256, align: 64, elements: !305, templateParams: !23, identifier: "9da194dcd2e8a907c7caf65024e0ab70")
!304 = !DINamespace(name: "result", scope: !66)
!305 = !{!306}
!306 = !DICompositeType(tag: DW_TAG_variant_part, scope: !303, file: !2, size: 256, align: 64, elements: !307, templateParams: !23, identifier: "67d33dd83d30ba516447755a15c2196e", discriminator: !323)
!307 = !{!308, !319}
!308 = !DIDerivedType(tag: DW_TAG_member, name: "Ok", scope: !306, file: !2, baseType: !309, size: 256, align: 64, extraData: i64 0)
!309 = !DICompositeType(tag: DW_TAG_structure_type, name: "Ok", scope: !303, file: !2, size: 256, align: 64, elements: !310, templateParams: !316, identifier: "fd7f466dc79accaee53dfe299afb7b7b")
!310 = !{!311}
!311 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !309, file: !2, baseType: !312, size: 192, align: 64, offset: 64)
!312 = !DICompositeType(tag: DW_TAG_structure_type, name: "String", scope: !313, file: !2, size: 192, align: 64, elements: !314, templateParams: !23, identifier: "f9be69e76fc784402e5b8eb88fb718b5")
!313 = !DINamespace(name: "string", scope: !56)
!314 = !{!315}
!315 = !DIDerivedType(tag: DW_TAG_member, name: "vec", scope: !312, file: !2, baseType: !54, size: 192, align: 64)
!316 = !{!317, !318}
!317 = !DITemplateTypeParameter(name: "T", type: !312)
!318 = !DITemplateTypeParameter(name: "E", type: !32)
!319 = !DIDerivedType(tag: DW_TAG_member, name: "Err", scope: !306, file: !2, baseType: !320, size: 256, align: 64, extraData: i64 1)
!320 = !DICompositeType(tag: DW_TAG_structure_type, name: "Err", scope: !303, file: !2, size: 256, align: 64, elements: !321, templateParams: !316, identifier: "984b1f1caf58cf187a683936db1c3281")
!321 = !{!322}
!322 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !320, file: !2, baseType: !32, size: 192, align: 64, offset: 64)
!323 = !DIDerivedType(tag: DW_TAG_member, scope: !303, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!324 = !DICompositeType(tag: DW_TAG_structure_type, name: "&str", file: !2, size: 128, align: 64, elements: !325, templateParams: !23, identifier: "c603ebb2af364502ef89131a86c6ad9b")
!325 = !{!326, !328}
!326 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !324, file: !2, baseType: !327, size: 64, align: 64)
!327 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !74, size: 64, align: 64, dwarfAddressSpace: 0)
!328 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !324, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!329 = !{!330}
!330 = !DILocalVariable(name: "key", arg: 1, scope: !299, file: !300, line: 227, type: !324)
!331 = !{!332}
!332 = !DITemplateTypeParameter(name: "K", type: !324)
!333 = !DILocation(line: 227, column: 29, scope: !299)
!334 = !DILocation(line: 228, column: 10, scope: !299)
!335 = !DILocation(line: 229, column: 1, scope: !299)
!336 = !DILocation(line: 228, column: 5, scope: !299)
!337 = !DILocation(line: 227, column: 1, scope: !299)
!338 = !DILocation(line: 229, column: 2, scope: !299)
!339 = distinct !DISubprogram(name: "as_ref", linkageName: "_ZN3std3ffi6os_str85_$LT$impl$u20$core..convert..AsRef$LT$std..ffi..os_str..OsStr$GT$$u20$for$u20$str$GT$6as_ref17h6f335272d1955c69E", scope: !341, file: !340, line: 1320, type: !342, scopeLine: 1320, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !355)
!340 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/ffi/os_str.rs", directory: "", checksumkind: CSK_MD5, checksum: "f63792bdff3c842d27d18548a318faba")
!341 = !DINamespace(name: "{impl#54}", scope: !44)
!342 = !DISubroutineType(types: !343)
!343 = !{!344, !324}
!344 = !DICompositeType(tag: DW_TAG_structure_type, name: "&std::ffi::os_str::OsStr", file: !2, size: 128, align: 64, elements: !345, templateParams: !23, identifier: "fef8c08dcda0f23e48d70feea0d90921")
!345 = !{!346, !354}
!346 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !344, file: !2, baseType: !347, size: 64, align: 64)
!347 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !348, size: 64, align: 64, dwarfAddressSpace: 0)
!348 = !DICompositeType(tag: DW_TAG_structure_type, name: "OsStr", scope: !44, file: !2, align: 8, elements: !349, templateParams: !23, identifier: "d7ab7c08a026e413156c261f0070868e")
!349 = !{!350}
!350 = !DIDerivedType(tag: DW_TAG_member, name: "inner", scope: !348, file: !2, baseType: !351, align: 8)
!351 = !DICompositeType(tag: DW_TAG_structure_type, name: "Slice", scope: !49, file: !2, align: 8, elements: !352, templateParams: !23, identifier: "ba965fbd54122a7c6da1f1397881640d")
!352 = !{!353}
!353 = !DIDerivedType(tag: DW_TAG_member, name: "inner", scope: !351, file: !2, baseType: !74, align: 8)
!354 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !344, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!355 = !{!356}
!356 = !DILocalVariable(name: "self", arg: 1, scope: !339, file: !340, line: 1320, type: !324)
!357 = !DILocation(line: 1320, column: 15, scope: !339)
!358 = !DILocation(line: 1321, column: 43, scope: !339)
!359 = !DILocalVariable(name: "s", scope: !360, file: !340, line: 1321, type: !324, align: 8)
!360 = !DILexicalBlockFile(scope: !361, file: !340, discriminator: 0)
!361 = distinct !DISubprogram(name: "from_str", linkageName: "_ZN3std3sys4unix6os_str5Slice8from_str17hc3d6b8a56f39cd35E", scope: !351, file: !362, line: 194, type: !363, scopeLine: 194, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !370)
!362 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/std/src/sys/unix/os_str.rs", directory: "", checksumkind: CSK_MD5, checksum: "3fffa48778a70506c3ad2634683a31ef")
!363 = !DISubroutineType(types: !364)
!364 = !{!365, !324}
!365 = !DICompositeType(tag: DW_TAG_structure_type, name: "&std::sys::unix::os_str::Slice", file: !2, size: 128, align: 64, elements: !366, templateParams: !23, identifier: "2dd56a3fa8c8a8c4ca1c1709f6681255")
!366 = !{!367, !369}
!367 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !365, file: !2, baseType: !368, size: 64, align: 64)
!368 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !351, size: 64, align: 64, dwarfAddressSpace: 0)
!369 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !365, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!370 = !{!359}
!371 = !DILocation(line: 1321, column: 27, scope: !360, inlinedAt: !372)
!372 = !DILocation(line: 1321, column: 27, scope: !339)
!373 = !DILocalVariable(name: "self", scope: !374, file: !340, line: 1321, type: !324, align: 8)
!374 = !DILexicalBlockFile(scope: !375, file: !340, discriminator: 0)
!375 = distinct !DISubprogram(name: "as_bytes", linkageName: "_ZN4core3str21_$LT$impl$u20$str$GT$8as_bytes17h13d800590348b3c6E", scope: !377, file: !376, line: 323, type: !379, scopeLine: 323, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !385)
!376 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/str/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "dd49fcee40af5f348df1f9868b20cc92")
!377 = !DINamespace(name: "{impl#0}", scope: !378)
!378 = !DINamespace(name: "str", scope: !66)
!379 = !DISubroutineType(types: !380)
!380 = !{!381, !324}
!381 = !DICompositeType(tag: DW_TAG_structure_type, name: "&[u8]", file: !2, size: 128, align: 64, elements: !382, templateParams: !23, identifier: "7d49e60d2ca720f66806f7375f860e2")
!382 = !{!383, !384}
!383 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !381, file: !2, baseType: !327, size: 64, align: 64)
!384 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !381, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!385 = !{!373}
!386 = !DILocation(line: 1321, column: 27, scope: !374, inlinedAt: !387)
!387 = !DILocation(line: 195, column: 30, scope: !361, inlinedAt: !372)
!388 = !{i64 1}
!389 = !DILocalVariable(name: "s", scope: !390, file: !340, line: 1321, type: !381, align: 8)
!390 = !DILexicalBlockFile(scope: !391, file: !340, discriminator: 0)
!391 = distinct !DISubprogram(name: "from_u8_slice", linkageName: "_ZN3std3sys4unix6os_str5Slice13from_u8_slice17h3e6f1fb114ae61fdE", scope: !351, file: !362, line: 189, type: !392, scopeLine: 189, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !394)
!392 = !DISubroutineType(types: !393)
!393 = !{!365, !381}
!394 = !{!389}
!395 = !DILocation(line: 1321, column: 27, scope: !390, inlinedAt: !396)
!396 = !DILocation(line: 195, column: 9, scope: !361, inlinedAt: !372)
!397 = !DILocalVariable(name: "inner", scope: !398, file: !340, line: 1321, type: !365, align: 8)
!398 = distinct !DISubprogram(name: "from_inner", linkageName: "_ZN3std3ffi6os_str5OsStr10from_inner17h561680d3861f66aeE", scope: !348, file: !340, line: 671, type: !399, scopeLine: 671, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !401)
!399 = !DISubroutineType(types: !400)
!400 = !{!344, !365}
!401 = !{!397}
!402 = !DILocation(line: 1321, column: 9, scope: !398, inlinedAt: !403)
!403 = !DILocation(line: 1321, column: 9, scope: !339)
!404 = !DILocation(line: 1322, column: 6, scope: !339)
!405 = distinct !DISubprogram(name: "new_display<alloc::string::String>", linkageName: "_ZN4core3fmt10ArgumentV111new_display17h8e936bdad87877f0E", scope: !407, file: !406, line: 318, type: !468, scopeLine: 318, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !473, retainedNodes: !471)
!406 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/fmt/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "18dcc19de419985ae78d2bd8ed07e5dc")
!407 = !DICompositeType(tag: DW_TAG_structure_type, name: "ArgumentV1", scope: !100, file: !2, size: 128, align: 64, elements: !408, templateParams: !23, identifier: "753c369e46bf484710f4d769a3fba395")
!408 = !{!409, !413}
!409 = !DIDerivedType(tag: DW_TAG_member, name: "value", scope: !407, file: !2, baseType: !410, size: 64, align: 64)
!410 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&core::fmt::{extern#0}::Opaque", baseType: !411, size: 64, align: 64, dwarfAddressSpace: 0)
!411 = !DICompositeType(tag: DW_TAG_structure_type, name: "Opaque", scope: !412, file: !2, align: 8, elements: !23, identifier: "83e8d27b51d2e55ae9422e57e00c6cd7")
!412 = !DINamespace(name: "{extern#0}", scope: !100)
!413 = !DIDerivedType(tag: DW_TAG_member, name: "formatter", scope: !407, file: !2, baseType: !414, size: 64, align: 64, offset: 64)
!414 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "fn(&core::fmt::{extern#0}::Opaque, &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error>", baseType: !415, size: 64, align: 64, dwarfAddressSpace: 0)
!415 = !DISubroutineType(types: !416)
!416 = !{!417, !410, !433}
!417 = !DICompositeType(tag: DW_TAG_structure_type, name: "Result<(), core::fmt::Error>", scope: !304, file: !2, size: 8, align: 8, elements: !418, templateParams: !23, identifier: "d239d58a8e95223cd52e3ad2c36d40d7")
!418 = !{!419}
!419 = !DICompositeType(tag: DW_TAG_variant_part, scope: !417, file: !2, size: 8, align: 8, elements: !420, templateParams: !23, identifier: "1fa2591b965a13cd50e38802b1727ca", discriminator: !432)
!420 = !{!421, !428}
!421 = !DIDerivedType(tag: DW_TAG_member, name: "Ok", scope: !419, file: !2, baseType: !422, size: 8, align: 8, extraData: i64 0)
!422 = !DICompositeType(tag: DW_TAG_structure_type, name: "Ok", scope: !417, file: !2, size: 8, align: 8, elements: !423, templateParams: !425, identifier: "cea751326735c343faf647063a65ad14")
!423 = !{!424}
!424 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !422, file: !2, baseType: !7, align: 8, offset: 8)
!425 = !{!220, !426}
!426 = !DITemplateTypeParameter(name: "E", type: !427)
!427 = !DICompositeType(tag: DW_TAG_structure_type, name: "Error", scope: !100, file: !2, align: 8, elements: !23, identifier: "87e319c059f1d372f32b0a49f33ec3cc")
!428 = !DIDerivedType(tag: DW_TAG_member, name: "Err", scope: !419, file: !2, baseType: !429, size: 8, align: 8, extraData: i64 1)
!429 = !DICompositeType(tag: DW_TAG_structure_type, name: "Err", scope: !417, file: !2, size: 8, align: 8, elements: !430, templateParams: !425, identifier: "6c6eb84ed910506586b60ba90dbaa2c")
!430 = !{!431}
!431 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !429, file: !2, baseType: !427, align: 8, offset: 8)
!432 = !DIDerivedType(tag: DW_TAG_member, scope: !417, file: !2, baseType: !74, size: 8, align: 8, flags: DIFlagArtificial)
!433 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut core::fmt::Formatter", baseType: !434, size: 64, align: 64, dwarfAddressSpace: 0)
!434 = !DICompositeType(tag: DW_TAG_structure_type, name: "Formatter", scope: !100, file: !2, size: 512, align: 64, elements: !435, templateParams: !23, identifier: "6e9ffaec9b89ebb810272bb66e7b2042")
!435 = !{!436, !438, !440, !441, !456, !457}
!436 = !DIDerivedType(tag: DW_TAG_member, name: "flags", scope: !434, file: !2, baseType: !437, size: 32, align: 32, offset: 384)
!437 = !DIBasicType(name: "u32", size: 32, encoding: DW_ATE_unsigned)
!438 = !DIDerivedType(tag: DW_TAG_member, name: "fill", scope: !434, file: !2, baseType: !439, size: 32, align: 32, offset: 416)
!439 = !DIBasicType(name: "char", size: 32, encoding: DW_ATE_UTF)
!440 = !DIDerivedType(tag: DW_TAG_member, name: "align", scope: !434, file: !2, baseType: !97, size: 8, align: 8, offset: 448)
!441 = !DIDerivedType(tag: DW_TAG_member, name: "width", scope: !434, file: !2, baseType: !442, size: 128, align: 64)
!442 = !DICompositeType(tag: DW_TAG_structure_type, name: "Option<usize>", scope: !443, file: !2, size: 128, align: 64, elements: !444, templateParams: !23, identifier: "5190463b0687da274ab794ccaf9d1fd8")
!443 = !DINamespace(name: "option", scope: !66)
!444 = !{!445}
!445 = !DICompositeType(tag: DW_TAG_variant_part, scope: !442, file: !2, size: 128, align: 64, elements: !446, templateParams: !23, identifier: "db59d501e5f76645f4edce4cdbfeb328", discriminator: !455)
!446 = !{!447, !451}
!447 = !DIDerivedType(tag: DW_TAG_member, name: "None", scope: !445, file: !2, baseType: !448, size: 128, align: 64, extraData: i64 0)
!448 = !DICompositeType(tag: DW_TAG_structure_type, name: "None", scope: !442, file: !2, size: 128, align: 64, elements: !23, templateParams: !449, identifier: "a1c5f3dead8f24ccdada7bc2feedd145")
!449 = !{!450}
!450 = !DITemplateTypeParameter(name: "T", type: !9)
!451 = !DIDerivedType(tag: DW_TAG_member, name: "Some", scope: !445, file: !2, baseType: !452, size: 128, align: 64, extraData: i64 1)
!452 = !DICompositeType(tag: DW_TAG_structure_type, name: "Some", scope: !442, file: !2, size: 128, align: 64, elements: !453, templateParams: !449, identifier: "3ad875242c049b8143d7577f4eb10d1a")
!453 = !{!454}
!454 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !452, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!455 = !DIDerivedType(tag: DW_TAG_member, scope: !442, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!456 = !DIDerivedType(tag: DW_TAG_member, name: "precision", scope: !434, file: !2, baseType: !442, size: 128, align: 64, offset: 128)
!457 = !DIDerivedType(tag: DW_TAG_member, name: "buf", scope: !434, file: !2, baseType: !458, size: 128, align: 64, offset: 256)
!458 = !DICompositeType(tag: DW_TAG_structure_type, name: "&mut dyn core::fmt::Write", file: !2, size: 128, align: 64, elements: !459, templateParams: !23, identifier: "3d4f80cd5361aaff4f795dd09efb8db1")
!459 = !{!460, !463}
!460 = !DIDerivedType(tag: DW_TAG_member, name: "pointer", scope: !458, file: !2, baseType: !461, size: 64, align: 64)
!461 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !462, size: 64, align: 64, dwarfAddressSpace: 0)
!462 = !DICompositeType(tag: DW_TAG_structure_type, name: "dyn core::fmt::Write", file: !2, align: 8, elements: !23, identifier: "abb712b259efc5e79bb67900edf24920")
!463 = !DIDerivedType(tag: DW_TAG_member, name: "vtable", scope: !458, file: !2, baseType: !464, size: 64, align: 64, offset: 64)
!464 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&[usize; 3]", baseType: !465, size: 64, align: 64, dwarfAddressSpace: 0)
!465 = !DICompositeType(tag: DW_TAG_array_type, baseType: !9, size: 192, align: 64, elements: !466)
!466 = !{!467}
!467 = !DISubrange(count: 3, lowerBound: 0)
!468 = !DISubroutineType(types: !469)
!469 = !{!407, !470}
!470 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&alloc::string::String", baseType: !312, size: 64, align: 64, dwarfAddressSpace: 0)
!471 = !{!472}
!472 = !DILocalVariable(name: "x", arg: 1, scope: !405, file: !406, line: 318, type: !470)
!473 = !{!317}
!474 = !DILocation(line: 318, column: 30, scope: !405)
!475 = !DILocation(line: 319, column: 23, scope: !405)
!476 = !DILocalVariable(name: "x", scope: !477, file: !406, line: 319, type: !470, align: 8)
!477 = distinct !DISubprogram(name: "new<alloc::string::String>", linkageName: "_ZN4core3fmt10ArgumentV13new17h9948c613e6ccd08dE", scope: !407, file: !406, line: 329, type: !478, scopeLine: 329, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !473, retainedNodes: !483)
!478 = !DISubroutineType(types: !479)
!479 = !{!407, !470, !480}
!480 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "fn(&alloc::string::String, &mut core::fmt::Formatter) -> core::result::Result<(), core::fmt::Error>", baseType: !481, size: 64, align: 64, dwarfAddressSpace: 0)
!481 = !DISubroutineType(types: !482)
!482 = !{!417, !470, !433}
!483 = !{!476, !484}
!484 = !DILocalVariable(name: "f", scope: !477, file: !406, line: 319, type: !480, align: 8)
!485 = !DILocation(line: 319, column: 13, scope: !477, inlinedAt: !486)
!486 = !DILocation(line: 319, column: 13, scope: !405)
!487 = !DILocation(line: 319, column: 26, scope: !405)
!488 = !DILocation(line: 320, column: 10, scope: !405)
!489 = distinct !DISubprogram(name: "new_v1", linkageName: "_ZN4core3fmt9Arguments6new_v117h4b70dcc115ea8332E", scope: !490, file: !406, line: 390, type: !549, scopeLine: 390, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !551)
!490 = !DICompositeType(tag: DW_TAG_structure_type, name: "Arguments", scope: !100, file: !2, size: 384, align: 64, elements: !491, templateParams: !23, identifier: "7e7034295abae01651800c8eb0e9b712")
!491 = !{!492, !498, !543}
!492 = !DIDerivedType(tag: DW_TAG_member, name: "pieces", scope: !490, file: !2, baseType: !493, size: 128, align: 64)
!493 = !DICompositeType(tag: DW_TAG_structure_type, name: "&[&str]", file: !2, size: 128, align: 64, elements: !494, templateParams: !23, identifier: "120d786d314e2730a5f45c5e7e56f7d")
!494 = !{!495, !497}
!495 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !493, file: !2, baseType: !496, size: 64, align: 64)
!496 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !324, size: 64, align: 64, dwarfAddressSpace: 0)
!497 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !493, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!498 = !DIDerivedType(tag: DW_TAG_member, name: "fmt", scope: !490, file: !2, baseType: !499, size: 128, align: 64, offset: 128)
!499 = !DICompositeType(tag: DW_TAG_structure_type, name: "Option<&[core::fmt::rt::v1::Argument]>", scope: !443, file: !2, size: 128, align: 64, elements: !500, templateParams: !23, identifier: "bb69cbb99024f47dbb54317ba8130317")
!500 = !{!501}
!501 = !DICompositeType(tag: DW_TAG_variant_part, scope: !499, file: !2, size: 128, align: 64, elements: !502, templateParams: !23, identifier: "ce02297fe7dbf35f547cc88f131a39b4", discriminator: !542)
!502 = !{!503, !538}
!503 = !DIDerivedType(tag: DW_TAG_member, name: "None", scope: !501, file: !2, baseType: !504, size: 128, align: 64, extraData: i64 0)
!504 = !DICompositeType(tag: DW_TAG_structure_type, name: "None", scope: !499, file: !2, size: 128, align: 64, elements: !23, templateParams: !505, identifier: "742dbe7e160661d8ca36fcfff2574850")
!505 = !{!506}
!506 = !DITemplateTypeParameter(name: "T", type: !507)
!507 = !DICompositeType(tag: DW_TAG_structure_type, name: "&[core::fmt::rt::v1::Argument]", file: !2, size: 128, align: 64, elements: !508, templateParams: !23, identifier: "5ac19a4b2fedc0a38075c82d3d698a2e")
!508 = !{!509, !537}
!509 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !507, file: !2, baseType: !510, size: 64, align: 64)
!510 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !511, size: 64, align: 64, dwarfAddressSpace: 0)
!511 = !DICompositeType(tag: DW_TAG_structure_type, name: "Argument", scope: !98, file: !2, size: 448, align: 64, elements: !512, templateParams: !23, identifier: "fbba22b504f631aebebe5f9a731b4661")
!512 = !{!513, !514}
!513 = !DIDerivedType(tag: DW_TAG_member, name: "position", scope: !511, file: !2, baseType: !9, size: 64, align: 64)
!514 = !DIDerivedType(tag: DW_TAG_member, name: "format", scope: !511, file: !2, baseType: !515, size: 384, align: 64, offset: 64)
!515 = !DICompositeType(tag: DW_TAG_structure_type, name: "FormatSpec", scope: !98, file: !2, size: 384, align: 64, elements: !516, templateParams: !23, identifier: "a89ae7a13a1def66296bab98052f520a")
!516 = !{!517, !518, !519, !520, !536}
!517 = !DIDerivedType(tag: DW_TAG_member, name: "fill", scope: !515, file: !2, baseType: !439, size: 32, align: 32, offset: 256)
!518 = !DIDerivedType(tag: DW_TAG_member, name: "align", scope: !515, file: !2, baseType: !97, size: 8, align: 8, offset: 320)
!519 = !DIDerivedType(tag: DW_TAG_member, name: "flags", scope: !515, file: !2, baseType: !437, size: 32, align: 32, offset: 288)
!520 = !DIDerivedType(tag: DW_TAG_member, name: "precision", scope: !515, file: !2, baseType: !521, size: 128, align: 64)
!521 = !DICompositeType(tag: DW_TAG_structure_type, name: "Count", scope: !98, file: !2, size: 128, align: 64, elements: !522, templateParams: !23, identifier: "41c6e2a1db95b605a371a090678c1fd8")
!522 = !{!523}
!523 = !DICompositeType(tag: DW_TAG_variant_part, scope: !521, file: !2, size: 128, align: 64, elements: !524, templateParams: !23, identifier: "eff7cdccebc4ba23639a28669cbce86", discriminator: !535)
!524 = !{!525, !529, !533}
!525 = !DIDerivedType(tag: DW_TAG_member, name: "Is", scope: !523, file: !2, baseType: !526, size: 128, align: 64, extraData: i64 0)
!526 = !DICompositeType(tag: DW_TAG_structure_type, name: "Is", scope: !521, file: !2, size: 128, align: 64, elements: !527, templateParams: !23, identifier: "927d86c22d9994b767e51a58b20493")
!527 = !{!528}
!528 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !526, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!529 = !DIDerivedType(tag: DW_TAG_member, name: "Param", scope: !523, file: !2, baseType: !530, size: 128, align: 64, extraData: i64 1)
!530 = !DICompositeType(tag: DW_TAG_structure_type, name: "Param", scope: !521, file: !2, size: 128, align: 64, elements: !531, templateParams: !23, identifier: "ce4b8bb3a4200a86c4c06a7570d8ee71")
!531 = !{!532}
!532 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !530, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!533 = !DIDerivedType(tag: DW_TAG_member, name: "Implied", scope: !523, file: !2, baseType: !534, size: 128, align: 64, extraData: i64 2)
!534 = !DICompositeType(tag: DW_TAG_structure_type, name: "Implied", scope: !521, file: !2, size: 128, align: 64, elements: !23, identifier: "b155566b9bd0239ef48aa3b8bcdef75b")
!535 = !DIDerivedType(tag: DW_TAG_member, scope: !521, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!536 = !DIDerivedType(tag: DW_TAG_member, name: "width", scope: !515, file: !2, baseType: !521, size: 128, align: 64, offset: 128)
!537 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !507, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!538 = !DIDerivedType(tag: DW_TAG_member, name: "Some", scope: !501, file: !2, baseType: !539, size: 128, align: 64)
!539 = !DICompositeType(tag: DW_TAG_structure_type, name: "Some", scope: !499, file: !2, size: 128, align: 64, elements: !540, templateParams: !505, identifier: "17f2fc106094349c7673abca4839c97a")
!540 = !{!541}
!541 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !539, file: !2, baseType: !507, size: 128, align: 64)
!542 = !DIDerivedType(tag: DW_TAG_member, scope: !499, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!543 = !DIDerivedType(tag: DW_TAG_member, name: "args", scope: !490, file: !2, baseType: !544, size: 128, align: 64, offset: 256)
!544 = !DICompositeType(tag: DW_TAG_structure_type, name: "&[core::fmt::ArgumentV1]", file: !2, size: 128, align: 64, elements: !545, templateParams: !23, identifier: "c78588d5439c4eaa18fbaab99f079cbf")
!545 = !{!546, !548}
!546 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !544, file: !2, baseType: !547, size: 64, align: 64)
!547 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !407, size: 64, align: 64, dwarfAddressSpace: 0)
!548 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !544, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!549 = !DISubroutineType(types: !550)
!550 = !{!490, !493, !544}
!551 = !{!552, !553}
!552 = !DILocalVariable(name: "pieces", arg: 1, scope: !489, file: !406, line: 390, type: !493)
!553 = !DILocalVariable(name: "args", arg: 2, scope: !489, file: !406, line: 390, type: !544)
!554 = !DILocation(line: 390, column: 25, scope: !489)
!555 = !DILocation(line: 390, column: 53, scope: !489)
!556 = !DILocation(line: 391, column: 12, scope: !489)
!557 = !DILocation(line: 391, column: 56, scope: !489)
!558 = !DILocation(line: 391, column: 41, scope: !489)
!559 = !{i8 0, i8 2}
!560 = !DILocation(line: 394, column: 34, scope: !489)
!561 = !DILocation(line: 394, column: 9, scope: !489)
!562 = !DILocation(line: 395, column: 6, scope: !489)
!563 = !DILocation(line: 392, column: 13, scope: !489)
!564 = distinct !DISubprogram(name: "checked_mul", linkageName: "_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17hb90a4357ac0c70a7E", scope: !566, file: !565, line: 555, type: !568, scopeLine: 555, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !570)
!565 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/num/uint_macros.rs", directory: "", checksumkind: CSK_MD5, checksum: "510cfe98475d713af9de72a29146058c")
!566 = !DINamespace(name: "{impl#11}", scope: !567)
!567 = !DINamespace(name: "num", scope: !66)
!568 = !DISubroutineType(types: !569)
!569 = !{!442, !9, !9}
!570 = !{!571, !572, !573, !575}
!571 = !DILocalVariable(name: "self", arg: 1, scope: !564, file: !565, line: 555, type: !9)
!572 = !DILocalVariable(name: "rhs", arg: 2, scope: !564, file: !565, line: 555, type: !9)
!573 = !DILocalVariable(name: "a", scope: !574, file: !565, line: 556, type: !9, align: 8)
!574 = distinct !DILexicalBlock(scope: !564, file: !565, line: 556, column: 13)
!575 = !DILocalVariable(name: "b", scope: !574, file: !565, line: 556, type: !576, align: 1)
!576 = !DIBasicType(name: "bool", size: 8, encoding: DW_ATE_boolean)
!577 = !DILocation(line: 555, column: 34, scope: !564)
!578 = !DILocation(line: 555, column: 40, scope: !564)
!579 = !DILocation(line: 556, column: 26, scope: !564)
!580 = !DILocalVariable(name: "self", scope: !581, file: !565, line: 556, type: !9, align: 8)
!581 = distinct !DISubprogram(name: "overflowing_mul", linkageName: "_ZN4core3num23_$LT$impl$u20$usize$GT$15overflowing_mul17hce0beb250bffdecdE", scope: !566, file: !565, line: 1688, type: !582, scopeLine: 1688, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !588)
!582 = !DISubroutineType(types: !583)
!583 = !{!584, !9, !9}
!584 = !DICompositeType(tag: DW_TAG_structure_type, name: "(usize, bool)", file: !2, size: 128, align: 64, elements: !585, templateParams: !23, identifier: "23309350ccb628a7900e37caa17b1249")
!585 = !{!586, !587}
!586 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !584, file: !2, baseType: !9, size: 64, align: 64)
!587 = !DIDerivedType(tag: DW_TAG_member, name: "__1", scope: !584, file: !2, baseType: !576, size: 8, align: 8, offset: 64)
!588 = !{!580, !589, !590, !592}
!589 = !DILocalVariable(name: "rhs", scope: !581, file: !565, line: 556, type: !9, align: 8)
!590 = !DILocalVariable(name: "a", scope: !591, file: !565, line: 556, type: !88, align: 8)
!591 = distinct !DILexicalBlock(scope: !581, file: !565, line: 1689, column: 13)
!592 = !DILocalVariable(name: "b", scope: !591, file: !565, line: 556, type: !576, align: 1)
!593 = !DILocation(line: 556, column: 26, scope: !581, inlinedAt: !579)
!594 = !DILocation(line: 556, column: 47, scope: !564)
!595 = !DILocation(line: 556, column: 26, scope: !591, inlinedAt: !579)
!596 = !DILocation(line: 556, column: 18, scope: !564)
!597 = !DILocation(line: 556, column: 18, scope: !574)
!598 = !DILocation(line: 556, column: 21, scope: !564)
!599 = !DILocation(line: 556, column: 21, scope: !574)
!600 = !DILocation(line: 557, column: 16, scope: !574)
!601 = !DILocation(line: 557, column: 42, scope: !574)
!602 = !DILocation(line: 557, column: 13, scope: !574)
!603 = !DILocation(line: 557, column: 30, scope: !574)
!604 = !DILocation(line: 558, column: 10, scope: !564)
!605 = !{i64 0, i64 2}
!606 = distinct !DISubprogram(name: "call_once<std::rt::lang_start::{closure_env#0}<()>, ()>", linkageName: "_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h66ac8c8cfdead3faE", scope: !608, file: !607, line: 248, type: !611, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !617, retainedNodes: !614)
!607 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ops/function.rs", directory: "", checksumkind: CSK_MD5, checksum: "3100065230267ed2a3b8753c70d752a6")
!608 = !DINamespace(name: "FnOnce", scope: !609)
!609 = !DINamespace(name: "function", scope: !610)
!610 = !DINamespace(name: "ops", scope: !66)
!611 = !DISubroutineType(types: !612)
!612 = !{!263, !613}
!613 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut std::rt::lang_start::{closure_env#0}<()>", baseType: !14, size: 64, align: 64, dwarfAddressSpace: 0)
!614 = !{!615, !616}
!615 = !DILocalVariable(arg: 1, scope: !606, file: !607, line: 248, type: !613)
!616 = !DILocalVariable(arg: 2, scope: !606, file: !607, line: 248, type: !7)
!617 = !{!618, !619}
!618 = !DITemplateTypeParameter(name: "Self", type: !14)
!619 = !DITemplateTypeParameter(name: "Args", type: !7)
!620 = !DILocation(line: 248, column: 5, scope: !606)
!621 = distinct !DISubprogram(name: "call_once<std::rt::lang_start::{closure_env#0}<()>, ()>", linkageName: "_ZN4core3ops8function6FnOnce9call_once17h5767b38317950c8bE", scope: !608, file: !607, line: 248, type: !622, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !617, retainedNodes: !624)
!622 = !DISubroutineType(types: !623)
!623 = !{!263, !14}
!624 = !{!625, !626}
!625 = !DILocalVariable(arg: 1, scope: !621, file: !607, line: 248, type: !14)
!626 = !DILocalVariable(arg: 2, scope: !621, file: !607, line: 248, type: !7)
!627 = !DILocation(line: 248, column: 5, scope: !621)
!628 = distinct !DISubprogram(name: "call_once<fn(), ()>", linkageName: "_ZN4core3ops8function6FnOnce9call_once17h6e624e4cb526ac89E", scope: !608, file: !607, line: 248, type: !212, scopeLine: 248, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !632, retainedNodes: !629)
!629 = !{!630, !631}
!630 = !DILocalVariable(arg: 1, scope: !628, file: !607, line: 248, type: !20)
!631 = !DILocalVariable(arg: 2, scope: !628, file: !607, line: 248, type: !7)
!632 = !{!633, !619}
!633 = !DITemplateTypeParameter(name: "Self", type: !20)
!634 = !DILocation(line: 248, column: 5, scope: !628)
!635 = distinct !DISubprogram(name: "drop_in_place<std::env::VarError>", linkageName: "_ZN4core3ptr39drop_in_place$LT$std..env..VarError$GT$17hbb9f1951a94d6b0bE", scope: !65, file: !636, line: 487, type: !637, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !642, retainedNodes: !640)
!636 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "13c32d970b0b4dd38131a1908223a155")
!637 = !DISubroutineType(types: !638)
!638 = !{null, !639}
!639 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut std::env::VarError", baseType: !32, size: 64, align: 64, dwarfAddressSpace: 0)
!640 = !{!641}
!641 = !DILocalVariable(arg: 1, scope: !635, file: !636, line: 487, type: !639)
!642 = !{!643}
!643 = !DITemplateTypeParameter(name: "T", type: !32)
!644 = !DILocation(line: 487, column: 1, scope: !635)
!645 = distinct !DISubprogram(name: "drop_in_place<alloc::string::String>", linkageName: "_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h017085301cfa8a38E", scope: !65, file: !636, line: 487, type: !646, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !473, retainedNodes: !649)
!646 = !DISubroutineType(types: !647)
!647 = !{null, !648}
!648 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut alloc::string::String", baseType: !312, size: 64, align: 64, dwarfAddressSpace: 0)
!649 = !{!650}
!650 = !DILocalVariable(arg: 1, scope: !645, file: !636, line: 487, type: !648)
!651 = !DILocation(line: 487, column: 1, scope: !645)
!652 = distinct !DISubprogram(name: "drop_in_place<alloc::vec::Vec<u8, alloc::alloc::Global>>", linkageName: "_ZN4core3ptr46drop_in_place$LT$alloc..vec..Vec$LT$u8$GT$$GT$17h0a98817a91215818E", scope: !65, file: !636, line: 487, type: !653, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !658, retainedNodes: !656)
!653 = !DISubroutineType(types: !654)
!654 = !{null, !655}
!655 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut alloc::vec::Vec<u8, alloc::alloc::Global>", baseType: !54, size: 64, align: 64, dwarfAddressSpace: 0)
!656 = !{!657}
!657 = !DILocalVariable(arg: 1, scope: !652, file: !636, line: 487, type: !655)
!658 = !{!659}
!659 = !DITemplateTypeParameter(name: "T", type: !54)
!660 = !DILocation(line: 487, column: 1, scope: !652)
!661 = distinct !DISubprogram(name: "drop_in_place<std::ffi::os_str::OsString>", linkageName: "_ZN4core3ptr47drop_in_place$LT$std..ffi..os_str..OsString$GT$17h421f40303d5a8656E", scope: !65, file: !636, line: 487, type: !662, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !667, retainedNodes: !665)
!662 = !DISubroutineType(types: !663)
!663 = !{null, !664}
!664 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut std::ffi::os_str::OsString", baseType: !43, size: 64, align: 64, dwarfAddressSpace: 0)
!665 = !{!666}
!666 = !DILocalVariable(arg: 1, scope: !661, file: !636, line: 487, type: !664)
!667 = !{!668}
!668 = !DITemplateTypeParameter(name: "T", type: !43)
!669 = !DILocation(line: 487, column: 1, scope: !661)
!670 = distinct !DISubprogram(name: "drop_in_place<std::sys::unix::os_str::Buf>", linkageName: "_ZN4core3ptr48drop_in_place$LT$std..sys..unix..os_str..Buf$GT$17he26a14dc108ef330E", scope: !65, file: !636, line: 487, type: !671, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !676, retainedNodes: !674)
!671 = !DISubroutineType(types: !672)
!672 = !{null, !673}
!673 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut std::sys::unix::os_str::Buf", baseType: !48, size: 64, align: 64, dwarfAddressSpace: 0)
!674 = !{!675}
!675 = !DILocalVariable(arg: 1, scope: !670, file: !636, line: 487, type: !673)
!676 = !{!677}
!677 = !DITemplateTypeParameter(name: "T", type: !48)
!678 = !DILocation(line: 487, column: 1, scope: !670)
!679 = distinct !DISubprogram(name: "drop_in_place<alloc::raw_vec::RawVec<u8, alloc::alloc::Global>>", linkageName: "_ZN4core3ptr53drop_in_place$LT$alloc..raw_vec..RawVec$LT$u8$GT$$GT$17h63264ea4812108b9E", scope: !65, file: !636, line: 487, type: !680, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !685, retainedNodes: !683)
!680 = !DISubroutineType(types: !681)
!681 = !{null, !682}
!682 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut alloc::raw_vec::RawVec<u8, alloc::alloc::Global>", baseType: !59, size: 64, align: 64, dwarfAddressSpace: 0)
!683 = !{!684}
!684 = !DILocalVariable(arg: 1, scope: !679, file: !636, line: 487, type: !682)
!685 = !{!686}
!686 = !DITemplateTypeParameter(name: "T", type: !59)
!687 = !DILocation(line: 487, column: 1, scope: !679)
!688 = distinct !DISubprogram(name: "drop_in_place<std::rt::lang_start::{closure_env#0}<()>>", linkageName: "_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h196226712f618a69E", scope: !65, file: !636, line: 487, type: !689, scopeLine: 487, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !693, retainedNodes: !691)
!689 = !DISubroutineType(types: !690)
!690 = !{null, !613}
!691 = !{!692}
!692 = !DILocalVariable(arg: 1, scope: !688, file: !636, line: 487, type: !613)
!693 = !{!694}
!694 = !DITemplateTypeParameter(name: "T", type: !14)
!695 = !DILocation(line: 487, column: 1, scope: !688)
!696 = distinct !DISubprogram(name: "from_size_valid_align", linkageName: "_ZN4core5alloc6layout6Layout21from_size_valid_align17h362893bcbac9d0a1E", scope: !698, file: !697, line: 77, type: !707, scopeLine: 77, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !726)
!697 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/alloc/layout.rs", directory: "", checksumkind: CSK_MD5, checksum: "2d0ac208ee70c69b94b07d38255a5525")
!698 = !DICompositeType(tag: DW_TAG_structure_type, name: "Layout", scope: !699, file: !2, size: 128, align: 64, elements: !701, templateParams: !23, identifier: "6727bf1318ffccbbbfc5e6dc0dfc8722")
!699 = !DINamespace(name: "layout", scope: !700)
!700 = !DINamespace(name: "alloc", scope: !66)
!701 = !{!702, !703}
!702 = !DIDerivedType(tag: DW_TAG_member, name: "size", scope: !698, file: !2, baseType: !9, size: 64, align: 64)
!703 = !DIDerivedType(tag: DW_TAG_member, name: "align", scope: !698, file: !2, baseType: !704, size: 64, align: 64, offset: 64)
!704 = !DICompositeType(tag: DW_TAG_structure_type, name: "ValidAlign", scope: !107, file: !2, size: 64, align: 64, elements: !705, templateParams: !23, identifier: "e392ecbcb8f7df9e6beb2b20857b4b5a")
!705 = !{!706}
!706 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !704, file: !2, baseType: !106, size: 64, align: 64)
!707 = !DISubroutineType(types: !708)
!708 = !{!709, !9, !704}
!709 = !DICompositeType(tag: DW_TAG_structure_type, name: "Result<core::alloc::layout::Layout, core::alloc::layout::LayoutError>", scope: !304, file: !2, size: 128, align: 64, elements: !710, templateParams: !23, identifier: "61ed90a3a60bf5c9da25fda9753d7b5")
!710 = !{!711}
!711 = !DICompositeType(tag: DW_TAG_variant_part, scope: !709, file: !2, size: 128, align: 64, elements: !712, templateParams: !23, identifier: "e7bb3560bfa0d3445ee2359cfbf9e5fe", discriminator: !725)
!712 = !{!713, !721}
!713 = !DIDerivedType(tag: DW_TAG_member, name: "Ok", scope: !711, file: !2, baseType: !714, size: 128, align: 64)
!714 = !DICompositeType(tag: DW_TAG_structure_type, name: "Ok", scope: !709, file: !2, size: 128, align: 64, elements: !715, templateParams: !717, identifier: "1efd2a987c8fa52528b02bba0275d8c7")
!715 = !{!716}
!716 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !714, file: !2, baseType: !698, size: 128, align: 64)
!717 = !{!718, !719}
!718 = !DITemplateTypeParameter(name: "T", type: !698)
!719 = !DITemplateTypeParameter(name: "E", type: !720)
!720 = !DICompositeType(tag: DW_TAG_structure_type, name: "LayoutError", scope: !699, file: !2, align: 8, elements: !23, identifier: "6e89e1d1b17d37435f7b87cb1d5cb26d")
!721 = !DIDerivedType(tag: DW_TAG_member, name: "Err", scope: !711, file: !2, baseType: !722, size: 128, align: 64, extraData: i64 0)
!722 = !DICompositeType(tag: DW_TAG_structure_type, name: "Err", scope: !709, file: !2, size: 128, align: 64, elements: !723, templateParams: !717, identifier: "9488fb9df60d2b7e722ab2cffead9e28")
!723 = !{!724}
!724 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !722, file: !2, baseType: !720, align: 8)
!725 = !DIDerivedType(tag: DW_TAG_member, scope: !709, file: !2, baseType: !88, size: 64, align: 64, offset: 64, flags: DIFlagArtificial)
!726 = !{!727, !728}
!727 = !DILocalVariable(name: "size", arg: 1, scope: !696, file: !697, line: 77, type: !9)
!728 = !DILocalVariable(name: "align", arg: 2, scope: !696, file: !697, line: 77, type: !704)
!729 = !DILocation(line: 77, column: 36, scope: !696)
!730 = !DILocation(line: 77, column: 49, scope: !696)
!731 = !DILocalVariable(name: "self", scope: !732, file: !697, line: 92, type: !735, align: 8)
!732 = !DILexicalBlockFile(scope: !733, file: !697, discriminator: 0)
!733 = distinct !DISubprogram(name: "get", linkageName: "_ZN4core3num7nonzero12NonZeroUsize3get17h9c94461a2a00f410E", scope: !735, file: !734, line: 82, type: !739, scopeLine: 82, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !741)
!734 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/num/nonzero.rs", directory: "", checksumkind: CSK_MD5, checksum: "f51cb88dd069db0b7fcd2123d03b69c9")
!735 = !DICompositeType(tag: DW_TAG_structure_type, name: "NonZeroUsize", scope: !736, file: !2, size: 64, align: 64, elements: !737, templateParams: !23, identifier: "c6c54dffb7a9517405cc55666c804e7")
!736 = !DINamespace(name: "nonzero", scope: !567)
!737 = !{!738}
!738 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !735, file: !2, baseType: !9, size: 64, align: 64)
!739 = !DISubroutineType(types: !740)
!740 = !{!9, !735}
!741 = !{!731}
!742 = !DILocation(line: 92, column: 42, scope: !732, inlinedAt: !743)
!743 = !DILocation(line: 92, column: 42, scope: !696)
!744 = !DILocalVariable(name: "self", scope: !745, file: !697, line: 92, type: !704, align: 8)
!745 = !DILexicalBlockFile(scope: !746, file: !697, discriminator: 0)
!746 = distinct !DISubprogram(name: "as_nonzero", linkageName: "_ZN4core3mem11valid_align10ValidAlign10as_nonzero17h74c9ba41fef24755E", scope: !704, file: !747, line: 39, type: !748, scopeLine: 39, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !750)
!747 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/mem/valid_align.rs", directory: "", checksumkind: CSK_MD5, checksum: "681d44917f5a26aec3d3954431def51e")
!748 = !DISubroutineType(types: !749)
!749 = !{!735, !704}
!750 = !{!744}
!751 = !DILocation(line: 92, column: 42, scope: !745, inlinedAt: !743)
!752 = !{i64 1, i64 -9223372036854775807}
!753 = !DILocalVariable(name: "n", scope: !754, file: !697, line: 92, type: !9, align: 8)
!754 = !DILexicalBlockFile(scope: !755, file: !697, discriminator: 0)
!755 = distinct !DISubprogram(name: "new_unchecked", linkageName: "_ZN4core3num7nonzero12NonZeroUsize13new_unchecked17hf4d6591df3991d30E", scope: !735, file: !734, line: 56, type: !756, scopeLine: 56, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !758)
!756 = !DISubroutineType(types: !757)
!757 = !{!735, !9}
!758 = !{!753, !759}
!759 = !DILocalVariable(name: "runtime", scope: !760, file: !697, line: 92, type: !763, align: 8)
!760 = !DILexicalBlockFile(scope: !761, file: !697, discriminator: 0)
!761 = distinct !DILexicalBlock(scope: !755, file: !762, line: 2336, column: 13)
!762 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/intrinsics.rs", directory: "", checksumkind: CSK_MD5, checksum: "f96ba730d7cf23ae45fdc72e7caf5f1b")
!763 = !DICompositeType(tag: DW_TAG_structure_type, name: "{closure_env#0}", scope: !764, file: !2, size: 64, align: 64, elements: !766, templateParams: !23, identifier: "cbed2d88a1ec7b20c4ad53e8c9863d89")
!764 = !DINamespace(name: "new_unchecked", scope: !765)
!765 = !DINamespace(name: "{impl#35}", scope: !736)
!766 = !{!767}
!767 = !DIDerivedType(tag: DW_TAG_member, name: "_ref__n", scope: !763, file: !2, baseType: !768, size: 64, align: 64)
!768 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&usize", baseType: !9, size: 64, align: 64, dwarfAddressSpace: 0)
!769 = !DILocation(line: 92, column: 42, scope: !754, inlinedAt: !770)
!770 = !DILocation(line: 41, column: 18, scope: !746, inlinedAt: !743)
!771 = !DILocation(line: 92, column: 41, scope: !696)
!772 = !DILocation(line: 92, column: 19, scope: !696)
!773 = !DILocation(line: 92, column: 12, scope: !696)
!774 = !DILocation(line: 97, column: 12, scope: !696)
!775 = !DILocation(line: 97, column: 9, scope: !696)
!776 = !DILocation(line: 98, column: 6, scope: !696)
!777 = !DILocation(line: 93, column: 20, scope: !696)
!778 = !{i64 0, i64 -9223372036854775807}
!779 = distinct !DISubprogram(name: "array<u8>", linkageName: "_ZN4core5alloc6layout6Layout5array17h041a339ec38f7fddE", scope: !698, file: !697, line: 416, type: !780, scopeLine: 416, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !782)
!780 = !DISubroutineType(types: !781)
!781 = !{!709, !9}
!782 = !{!783, !784, !786, !806}
!783 = !DILocalVariable(name: "n", arg: 1, scope: !779, file: !697, line: 416, type: !9)
!784 = !DILocalVariable(name: "array_size", scope: !785, file: !697, line: 417, type: !9, align: 8)
!785 = distinct !DILexicalBlock(scope: !779, file: !697, line: 417, column: 9)
!786 = !DILocalVariable(name: "residual", scope: !787, file: !697, line: 417, type: !788, align: 1)
!787 = distinct !DILexicalBlock(scope: !779, file: !697, line: 417, column: 79)
!788 = !DICompositeType(tag: DW_TAG_structure_type, name: "Result<core::convert::Infallible, core::alloc::layout::LayoutError>", scope: !304, file: !2, align: 8, elements: !789, templateParams: !23, identifier: "2408e7ead4450472646681a937f2eed")
!789 = !{!790}
!790 = !DICompositeType(tag: DW_TAG_variant_part, scope: !788, file: !2, align: 8, elements: !791, templateParams: !23, identifier: "6cbcec323d74ab47f813265a09655e1e")
!791 = !{!792, !802}
!792 = !DIDerivedType(tag: DW_TAG_member, name: "Ok", scope: !790, file: !2, baseType: !793, align: 8)
!793 = !DICompositeType(tag: DW_TAG_structure_type, name: "Ok", scope: !788, file: !2, align: 8, elements: !794, templateParams: !800, identifier: "40ec0a271e0cb2d34d257ba58fdead82")
!794 = !{!795}
!795 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !793, file: !2, baseType: !796, align: 8)
!796 = !DICompositeType(tag: DW_TAG_structure_type, name: "Infallible", scope: !797, file: !2, align: 8, elements: !798, templateParams: !23, identifier: "54da939063c7c2baf203c9f582cd0995")
!797 = !DINamespace(name: "convert", scope: !66)
!798 = !{!799}
!799 = !DICompositeType(tag: DW_TAG_variant_part, scope: !796, file: !2, align: 8, elements: !23, identifier: "8a046f69014feadb4a5e941e4277afe9")
!800 = !{!801, !719}
!801 = !DITemplateTypeParameter(name: "T", type: !796)
!802 = !DIDerivedType(tag: DW_TAG_member, name: "Err", scope: !790, file: !2, baseType: !803, align: 8)
!803 = !DICompositeType(tag: DW_TAG_structure_type, name: "Err", scope: !788, file: !2, align: 8, elements: !804, templateParams: !800, identifier: "72611e72c15211a4d55dae520b84155f")
!804 = !{!805}
!805 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !803, file: !2, baseType: !720, align: 8)
!806 = !DILocalVariable(name: "val", scope: !807, file: !697, line: 417, type: !9, align: 8)
!807 = distinct !DILexicalBlock(scope: !779, file: !697, line: 417, column: 26)
!808 = !DILocation(line: 416, column: 21, scope: !779)
!809 = !DILocalVariable(name: "self", scope: !810, file: !697, line: 417, type: !833, align: 8)
!810 = !DILexicalBlockFile(scope: !811, file: !697, discriminator: 0)
!811 = distinct !DISubprogram(name: "branch<usize, core::alloc::layout::LayoutError>", linkageName: "_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17h01b9356de3b95360E", scope: !813, file: !812, line: 2117, type: !814, scopeLine: 2117, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !841, retainedNodes: !847)
!812 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/result.rs", directory: "", checksumkind: CSK_MD5, checksum: "376d3f50f2b6d030dde9244768e6c6e1")
!813 = !DINamespace(name: "{impl#27}", scope: !304)
!814 = !DISubroutineType(types: !815)
!815 = !{!816, !833}
!816 = !DICompositeType(tag: DW_TAG_structure_type, name: "ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::layout::LayoutError>, usize>", scope: !817, file: !2, size: 128, align: 64, elements: !818, templateParams: !23, identifier: "ce5c98f9de0798e97388caf7b24b4edc")
!817 = !DINamespace(name: "control_flow", scope: !610)
!818 = !{!819}
!819 = !DICompositeType(tag: DW_TAG_variant_part, scope: !816, file: !2, size: 128, align: 64, elements: !820, templateParams: !23, identifier: "6bdd8e43359c9849ce58ffeff4bb9b82", discriminator: !832)
!820 = !{!821, !828}
!821 = !DIDerivedType(tag: DW_TAG_member, name: "Continue", scope: !819, file: !2, baseType: !822, size: 128, align: 64, extraData: i64 0)
!822 = !DICompositeType(tag: DW_TAG_structure_type, name: "Continue", scope: !816, file: !2, size: 128, align: 64, elements: !823, templateParams: !825, identifier: "b6fdadee5e49b7207145efbc9b42a94a")
!823 = !{!824}
!824 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !822, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!825 = !{!826, !827}
!826 = !DITemplateTypeParameter(name: "B", type: !788)
!827 = !DITemplateTypeParameter(name: "C", type: !9)
!828 = !DIDerivedType(tag: DW_TAG_member, name: "Break", scope: !819, file: !2, baseType: !829, size: 128, align: 64, extraData: i64 1)
!829 = !DICompositeType(tag: DW_TAG_structure_type, name: "Break", scope: !816, file: !2, size: 128, align: 64, elements: !830, templateParams: !825, identifier: "b5889c00b354165f6e6f55dba1990157")
!830 = !{!831}
!831 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !829, file: !2, baseType: !788, align: 8, offset: 64)
!832 = !DIDerivedType(tag: DW_TAG_member, scope: !816, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!833 = !DICompositeType(tag: DW_TAG_structure_type, name: "Result<usize, core::alloc::layout::LayoutError>", scope: !304, file: !2, size: 128, align: 64, elements: !834, templateParams: !23, identifier: "c2a525df37a04684d727d3bb68e24786")
!834 = !{!835}
!835 = !DICompositeType(tag: DW_TAG_variant_part, scope: !833, file: !2, size: 128, align: 64, elements: !836, templateParams: !23, identifier: "59922648ff1b36fe1aa289683c505c74", discriminator: !846)
!836 = !{!837, !842}
!837 = !DIDerivedType(tag: DW_TAG_member, name: "Ok", scope: !835, file: !2, baseType: !838, size: 128, align: 64, extraData: i64 0)
!838 = !DICompositeType(tag: DW_TAG_structure_type, name: "Ok", scope: !833, file: !2, size: 128, align: 64, elements: !839, templateParams: !841, identifier: "98a9acae3d260aa3de9b86f4a7044881")
!839 = !{!840}
!840 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !838, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!841 = !{!450, !719}
!842 = !DIDerivedType(tag: DW_TAG_member, name: "Err", scope: !835, file: !2, baseType: !843, size: 128, align: 64, extraData: i64 1)
!843 = !DICompositeType(tag: DW_TAG_structure_type, name: "Err", scope: !833, file: !2, size: 128, align: 64, elements: !844, templateParams: !841, identifier: "3430eaa712a080f75cd3b02585f182")
!844 = !{!845}
!845 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !843, file: !2, baseType: !720, align: 8, offset: 64)
!846 = !DIDerivedType(tag: DW_TAG_member, scope: !833, file: !2, baseType: !88, size: 64, align: 64, flags: DIFlagArtificial)
!847 = !{!809, !848, !851}
!848 = !DILocalVariable(name: "v", scope: !849, file: !697, line: 417, type: !9, align: 8)
!849 = !DILexicalBlockFile(scope: !850, file: !697, discriminator: 0)
!850 = distinct !DILexicalBlock(scope: !811, file: !812, line: 2119, column: 13)
!851 = !DILocalVariable(name: "e", scope: !852, file: !697, line: 417, type: !720, align: 1)
!852 = !DILexicalBlockFile(scope: !853, file: !697, discriminator: 0)
!853 = distinct !DILexicalBlock(scope: !811, file: !812, line: 2120, column: 13)
!854 = !DILocation(line: 417, column: 26, scope: !810, inlinedAt: !855)
!855 = !DILocation(line: 417, column: 26, scope: !779)
!856 = !DILocalVariable(name: "self", scope: !857, file: !697, line: 417, type: !442, align: 8)
!857 = !DILexicalBlockFile(scope: !858, file: !697, discriminator: 0)
!858 = distinct !DISubprogram(name: "ok_or<usize, core::alloc::layout::LayoutError>", linkageName: "_ZN4core6option15Option$LT$T$GT$5ok_or17h3f9cf4b3ecb1447dE", scope: !442, file: !859, line: 1051, type: !860, scopeLine: 1051, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !841, retainedNodes: !862)
!859 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/option.rs", directory: "", checksumkind: CSK_MD5, checksum: "86a5483c3993f03690545387e943de77")
!860 = !DISubroutineType(types: !861)
!861 = !{!833, !442, !720}
!862 = !{!856, !863, !864}
!863 = !DILocalVariable(name: "err", scope: !857, file: !697, line: 417, type: !720, align: 1)
!864 = !DILocalVariable(name: "v", scope: !865, file: !697, line: 417, type: !9, align: 8)
!865 = !DILexicalBlockFile(scope: !866, file: !697, discriminator: 0)
!866 = distinct !DILexicalBlock(scope: !858, file: !859, line: 1056, column: 13)
!867 = !DILocation(line: 417, column: 26, scope: !857, inlinedAt: !855)
!868 = !DILocation(line: 417, column: 79, scope: !787)
!869 = !DILocalVariable(name: "residual", scope: !870, file: !697, line: 417, type: !788, align: 1)
!870 = !DILexicalBlockFile(scope: !871, file: !697, discriminator: 0)
!871 = distinct !DISubprogram(name: "from_residual<core::alloc::layout::Layout, core::alloc::layout::LayoutError, core::alloc::layout::LayoutError>", linkageName: "_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17h09aea3b2fae0aa14E", scope: !872, file: !812, line: 2132, type: !873, scopeLine: 2132, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !887, retainedNodes: !883)
!872 = !DINamespace(name: "{impl#28}", scope: !304)
!873 = !DISubroutineType(types: !874)
!874 = !{!709, !788, !875}
!875 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&core::panic::location::Location", baseType: !876, size: 64, align: 64, dwarfAddressSpace: 0)
!876 = !DICompositeType(tag: DW_TAG_structure_type, name: "Location", scope: !877, file: !2, size: 192, align: 64, elements: !879, templateParams: !23, identifier: "ef576a844c237f54e9e75bf7bba044c0")
!877 = !DINamespace(name: "location", scope: !878)
!878 = !DINamespace(name: "panic", scope: !66)
!879 = !{!880, !881, !882}
!880 = !DIDerivedType(tag: DW_TAG_member, name: "file", scope: !876, file: !2, baseType: !324, size: 128, align: 64)
!881 = !DIDerivedType(tag: DW_TAG_member, name: "line", scope: !876, file: !2, baseType: !437, size: 32, align: 32, offset: 128)
!882 = !DIDerivedType(tag: DW_TAG_member, name: "col", scope: !876, file: !2, baseType: !437, size: 32, align: 32, offset: 160)
!883 = !{!869, !884}
!884 = !DILocalVariable(name: "e", scope: !885, file: !697, line: 417, type: !720, align: 1)
!885 = !DILexicalBlockFile(scope: !886, file: !697, discriminator: 0)
!886 = distinct !DILexicalBlock(scope: !871, file: !812, line: 2134, column: 13)
!887 = !{!718, !719, !888}
!888 = !DITemplateTypeParameter(name: "F", type: !720)
!889 = !DILocation(line: 417, column: 26, scope: !870, inlinedAt: !890)
!890 = !DILocation(line: 417, column: 26, scope: !787)
!891 = !DILocation(line: 417, column: 26, scope: !852, inlinedAt: !855)
!892 = !DILocation(line: 417, column: 26, scope: !885, inlinedAt: !890)
!893 = !DILocation(line: 417, column: 26, scope: !865, inlinedAt: !855)
!894 = !DILocation(line: 417, column: 26, scope: !849, inlinedAt: !855)
!895 = !DILocation(line: 417, column: 26, scope: !807)
!896 = !DILocation(line: 417, column: 13, scope: !785)
!897 = !DILocation(line: 419, column: 51, scope: !898, inlinedAt: !903)
!898 = !DILexicalBlockFile(scope: !899, file: !697, discriminator: 0)
!899 = distinct !DISubprogram(name: "align_of<u8>", linkageName: "_ZN4core3mem8align_of17ha4113a27be856913E", scope: !108, file: !900, line: 464, type: !901, scopeLine: 464, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !23)
!900 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/mem/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "27c8869548c9dcb65186c5584c2586f6")
!901 = !DISubroutineType(types: !902)
!902 = !{!9}
!903 = !DILocation(line: 56, column: 44, scope: !904, inlinedAt: !907)
!904 = distinct !DISubprogram(name: "of<u8>", linkageName: "_ZN4core3mem11valid_align10ValidAlign2of17hf7aea6fc634b45dbE", scope: !704, file: !747, line: 54, type: !905, scopeLine: 54, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !23)
!905 = !DISubroutineType(types: !906)
!906 = !{!704}
!907 = !DILocation(line: 419, column: 51, scope: !785)
!908 = !DILocalVariable(name: "align", scope: !909, file: !697, line: 419, type: !9, align: 8)
!909 = !DILexicalBlockFile(scope: !910, file: !697, discriminator: 0)
!910 = distinct !DISubprogram(name: "new_unchecked", linkageName: "_ZN4core3mem11valid_align10ValidAlign13new_unchecked17h6a78b49e1ff9760cE", scope: !704, file: !747, line: 29, type: !911, scopeLine: 29, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !913)
!911 = !DISubroutineType(types: !912)
!912 = !{!704, !9}
!913 = !{!908, !914}
!914 = !DILocalVariable(name: "runtime", scope: !915, file: !697, line: 419, type: !917, align: 8)
!915 = !DILexicalBlockFile(scope: !916, file: !697, discriminator: 0)
!916 = distinct !DILexicalBlock(scope: !910, file: !762, line: 2336, column: 13)
!917 = !DICompositeType(tag: DW_TAG_structure_type, name: "{closure_env#0}", scope: !918, file: !2, size: 64, align: 64, elements: !920, templateParams: !23, identifier: "a24236e50785a0359acaebf14a869a84")
!918 = !DINamespace(name: "new_unchecked", scope: !919)
!919 = !DINamespace(name: "{impl#0}", scope: !107)
!920 = !{!921}
!921 = !DIDerivedType(tag: DW_TAG_member, name: "_ref__align", scope: !917, file: !2, baseType: !768, size: 64, align: 64)
!922 = !DILocation(line: 419, column: 51, scope: !909, inlinedAt: !923)
!923 = !DILocation(line: 56, column: 18, scope: !904, inlinedAt: !907)
!924 = !DILocation(line: 420, column: 6, scope: !779)
!925 = !DILocation(line: 419, column: 9, scope: !785)
!926 = distinct !DISubprogram(name: "unwrap<alloc::string::String, std::env::VarError>", linkageName: "_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17hc8210bfc41415118E", scope: !303, file: !812, line: 1101, type: !927, scopeLine: 1101, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !316, retainedNodes: !929)
!927 = !DISubroutineType(types: !928)
!928 = !{!312, !303, !875}
!929 = !{!930, !931, !933}
!930 = !DILocalVariable(name: "self", arg: 1, scope: !926, file: !812, line: 1101, type: !303)
!931 = !DILocalVariable(name: "t", scope: !932, file: !812, line: 1106, type: !312, align: 8)
!932 = distinct !DILexicalBlock(scope: !926, file: !812, line: 1106, column: 13)
!933 = !DILocalVariable(name: "e", scope: !934, file: !812, line: 1107, type: !32, align: 8)
!934 = distinct !DILexicalBlock(scope: !926, file: !812, line: 1107, column: 13)
!935 = !DILocation(line: 1106, column: 16, scope: !932)
!936 = !DILocation(line: 1101, column: 19, scope: !926)
!937 = !DILocation(line: 1107, column: 17, scope: !934)
!938 = !DILocation(line: 1105, column: 15, scope: !926)
!939 = !DILocation(line: 1105, column: 9, scope: !926)
!940 = !DILocation(line: 1106, column: 16, scope: !926)
!941 = !DILocation(line: 1109, column: 6, scope: !926)
!942 = !DILocation(line: 1107, column: 17, scope: !926)
!943 = !DILocation(line: 1107, column: 84, scope: !934)
!944 = !DILocation(line: 1107, column: 23, scope: !934)
!945 = !DILocation(line: 1107, column: 86, scope: !926)
!946 = !DILocation(line: 1101, column: 5, scope: !926)
!947 = distinct !DISubprogram(name: "from<core::alloc::layout::LayoutError>", linkageName: "_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h3d20e1e9b1fe581cE", scope: !949, file: !948, line: 559, type: !950, scopeLine: 559, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !954, retainedNodes: !952)
!948 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/convert/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "e9a22d2b51b4cfd278a09c9d531e27c4")
!949 = !DINamespace(name: "{impl#4}", scope: !797)
!950 = !DISubroutineType(types: !951)
!951 = !{null, !720}
!952 = !{!953}
!953 = !DILocalVariable(name: "t", arg: 1, scope: !947, file: !948, line: 559, type: !720)
!954 = !{!955}
!955 = !DITemplateTypeParameter(name: "T", type: !720)
!956 = !DILocation(line: 559, column: 13, scope: !947)
!957 = !DILocation(line: 561, column: 6, scope: !947)
!958 = distinct !DISubprogram(name: "into<core::ptr::unique::Unique<u8>, core::ptr::non_null::NonNull<u8>>", linkageName: "_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h093103a2bfe88da2E", scope: !959, file: !948, line: 549, type: !178, scopeLine: 549, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !962, retainedNodes: !960)
!959 = !DINamespace(name: "{impl#3}", scope: !797)
!960 = !{!961}
!961 = !DILocalVariable(name: "self", arg: 1, scope: !958, file: !948, line: 549, type: !63)
!962 = !{!963, !964}
!963 = !DITemplateTypeParameter(name: "T", type: !63)
!964 = !DITemplateTypeParameter(name: "U", type: !69)
!965 = !DILocation(line: 549, column: 13, scope: !958)
!966 = !DILocation(line: 550, column: 9, scope: !958)
!967 = !DILocation(line: 551, column: 6, scope: !958)
!968 = distinct !DISubprogram(name: "report", linkageName: "_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h8a2d015129d5babaE", scope: !969, file: !272, line: 2170, type: !970, scopeLine: 2170, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !972)
!969 = !DINamespace(name: "{impl#53}", scope: !274)
!970 = !DISubroutineType(types: !971)
!971 = !{!273, !7}
!972 = !{!973}
!973 = !DILocalVariable(name: "self", arg: 1, scope: !968, file: !272, line: 2170, type: !7)
!974 = !DILocation(line: 2170, column: 15, scope: !968)
!975 = !DILocation(line: 2172, column: 6, scope: !968)
!976 = distinct !DISubprogram(name: "as_ref<str, std::ffi::os_str::OsStr>", linkageName: "_ZN55_$LT$$RF$T$u20$as$u20$core..convert..AsRef$LT$U$GT$$GT$6as_ref17h8db5e479bfb5017aE", scope: !977, file: !948, line: 491, type: !978, scopeLine: 491, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !983, retainedNodes: !981)
!977 = !DINamespace(name: "{impl#0}", scope: !797)
!978 = !DISubroutineType(types: !979)
!979 = !{!344, !980}
!980 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&&str", baseType: !324, size: 64, align: 64, dwarfAddressSpace: 0)
!981 = !{!982}
!982 = !DILocalVariable(name: "self", arg: 1, scope: !976, file: !948, line: 491, type: !980)
!983 = !{!76, !984}
!984 = !DITemplateTypeParameter(name: "U", type: !348)
!985 = !DILocation(line: 491, column: 15, scope: !976)
!986 = !DILocation(line: 492, column: 33, scope: !976)
!987 = !DILocation(line: 492, column: 9, scope: !976)
!988 = !DILocation(line: 493, column: 6, scope: !976)
!989 = distinct !DISubprogram(name: "as_mut_ptr<u8, alloc::alloc::Global>", linkageName: "_ZN5alloc3vec16Vec$LT$T$C$A$GT$10as_mut_ptr17hf0ab5348698999aeE", scope: !54, file: !990, line: 1204, type: !991, scopeLine: 1204, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !994)
!990 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/alloc/src/vec/mod.rs", directory: "", checksumkind: CSK_MD5, checksum: "ccced07f4d2284e276bdff9c5cb81e82")
!991 = !DISubroutineType(types: !992)
!992 = !{!190, !993}
!993 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut alloc::vec::Vec<u8, alloc::alloc::Global>", baseType: !54, size: 64, align: 64, dwarfAddressSpace: 0)
!994 = !{!995, !996}
!995 = !DILocalVariable(name: "self", arg: 1, scope: !989, file: !990, line: 1204, type: !993)
!996 = !DILocalVariable(name: "ptr", scope: !997, file: !990, line: 1207, type: !190, align: 8)
!997 = distinct !DILexicalBlock(scope: !989, file: !990, line: 1207, column: 9)
!998 = !DILocation(line: 1204, column: 23, scope: !989)
!999 = !DILocalVariable(name: "metadata", scope: !1000, file: !990, line: 1209, type: !7, align: 1)
!1000 = !DILexicalBlockFile(scope: !1001, file: !990, discriminator: 0)
!1001 = distinct !DISubprogram(name: "from_raw_parts_mut<u8>", linkageName: "_ZN4core3ptr8metadata18from_raw_parts_mut17hdf3ccd62c26a3421E", scope: !1003, file: !1002, line: 127, type: !1004, scopeLine: 127, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1007)
!1002 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/metadata.rs", directory: "", checksumkind: CSK_MD5, checksum: "59565ed3c34dee3e8f8928c29f8f7ce4")
!1003 = !DINamespace(name: "metadata", scope: !65)
!1004 = !DISubroutineType(types: !1005)
!1005 = !{!190, !1006, !7}
!1006 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*mut ()", baseType: !7, size: 64, align: 64, dwarfAddressSpace: 0)
!1007 = !{!1008, !999}
!1008 = !DILocalVariable(name: "data_address", scope: !1000, file: !990, line: 1209, type: !1006, align: 8)
!1009 = !DILocation(line: 1209, column: 21, scope: !1000, inlinedAt: !1010)
!1010 = !DILocation(line: 668, column: 5, scope: !1011, inlinedAt: !1014)
!1011 = distinct !DISubprogram(name: "null_mut<u8>", linkageName: "_ZN4core3ptr8null_mut17hb85bf713688bbfa1E", scope: !65, file: !636, line: 667, type: !1012, scopeLine: 667, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !23)
!1012 = !DISubroutineType(types: !1013)
!1013 = !{!190}
!1014 = !DILocation(line: 38, column: 41, scope: !1015, inlinedAt: !1024)
!1015 = distinct !DISubprogram(name: "is_null<u8>", linkageName: "_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17h9dc7df5c57c58925E", scope: !1017, file: !1016, line: 35, type: !1019, scopeLine: 35, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1021)
!1016 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/mut_ptr.rs", directory: "", checksumkind: CSK_MD5, checksum: "6672664af50614ec3c026afd55307af7")
!1017 = !DINamespace(name: "{impl#0}", scope: !1018)
!1018 = !DINamespace(name: "mut_ptr", scope: !65)
!1019 = !DISubroutineType(types: !1020)
!1020 = !{!576, !190}
!1021 = !{!1022}
!1022 = !DILocalVariable(name: "self", scope: !1023, file: !990, line: 1209, type: !190, align: 8)
!1023 = !DILexicalBlockFile(scope: !1015, file: !990, discriminator: 0)
!1024 = !DILocation(line: 1209, column: 21, scope: !997)
!1025 = !DILocation(line: 1207, column: 19, scope: !989)
!1026 = !DILocalVariable(name: "self", scope: !1027, file: !990, line: 1207, type: !1032, align: 8)
!1027 = !DILexicalBlockFile(scope: !1028, file: !990, discriminator: 0)
!1028 = distinct !DISubprogram(name: "ptr<u8, alloc::alloc::Global>", linkageName: "_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$3ptr17hd2965d8d15b23788E", scope: !59, file: !1029, line: 223, type: !1030, scopeLine: 223, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1033)
!1029 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/alloc/src/raw_vec.rs", directory: "", checksumkind: CSK_MD5, checksum: "7882a816b01a8bc5234f4586c1b0290b")
!1030 = !DISubroutineType(types: !1031)
!1031 = !{!190, !1032}
!1032 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&alloc::raw_vec::RawVec<u8, alloc::alloc::Global>", baseType: !59, size: 64, align: 64, dwarfAddressSpace: 0)
!1033 = !{!1026}
!1034 = !DILocation(line: 1207, column: 19, scope: !1027, inlinedAt: !1025)
!1035 = !DILocalVariable(name: "self", scope: !1036, file: !990, line: 1207, type: !63, align: 8)
!1036 = !DILexicalBlockFile(scope: !1037, file: !990, discriminator: 0)
!1037 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha55716535ab1b589E", scope: !63, file: !187, line: 103, type: !188, scopeLine: 103, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1038)
!1038 = !{!1035}
!1039 = !DILocation(line: 1207, column: 19, scope: !1036, inlinedAt: !1040)
!1040 = !DILocation(line: 224, column: 9, scope: !1028, inlinedAt: !1025)
!1041 = !DILocalVariable(name: "self", scope: !1042, file: !990, line: 1207, type: !69, align: 8)
!1042 = !DILexicalBlockFile(scope: !1043, file: !990, discriminator: 0)
!1043 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17hf95529f8199b6675E", scope: !69, file: !176, line: 330, type: !195, scopeLine: 330, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1044)
!1044 = !{!1041}
!1045 = !DILocation(line: 1207, column: 19, scope: !1042, inlinedAt: !1046)
!1046 = !DILocation(line: 104, column: 9, scope: !1037, inlinedAt: !1040)
!1047 = !DILocation(line: 1207, column: 13, scope: !997)
!1048 = !DILocation(line: 1209, column: 21, scope: !1023, inlinedAt: !1024)
!1049 = !DILocalVariable(name: "self", scope: !1050, file: !990, line: 1209, type: !190, align: 8)
!1050 = !DILexicalBlockFile(scope: !1051, file: !990, discriminator: 0)
!1051 = distinct !DISubprogram(name: "guaranteed_eq<u8>", linkageName: "_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$13guaranteed_eq17he9c749abe586e6dfE", scope: !1017, file: !1016, line: 707, type: !1052, scopeLine: 707, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1054)
!1052 = !DISubroutineType(types: !1053)
!1053 = !{!576, !190, !190}
!1054 = !{!1049, !1055}
!1055 = !DILocalVariable(name: "other", scope: !1050, file: !990, line: 1209, type: !190, align: 8)
!1056 = !DILocation(line: 1209, column: 21, scope: !1050, inlinedAt: !1057)
!1057 = !DILocation(line: 38, column: 9, scope: !1015, inlinedAt: !1024)
!1058 = !DILocation(line: 1209, column: 21, scope: !1059, inlinedAt: !1065)
!1059 = !DILexicalBlockFile(scope: !1060, file: !990, discriminator: 0)
!1060 = distinct !DISubprogram(name: "invalid_mut<()>", linkageName: "_ZN4core3ptr11invalid_mut17h766709a69147b3ddE", scope: !65, file: !636, line: 569, type: !1061, scopeLine: 569, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !231, retainedNodes: !1063)
!1061 = !DISubroutineType(types: !1062)
!1062 = !{!1006, !9}
!1063 = !{!1064}
!1064 = !DILocalVariable(name: "addr", scope: !1059, file: !990, line: 1209, type: !9, align: 8)
!1065 = !DILocation(line: 668, column: 24, scope: !1011, inlinedAt: !1014)
!1066 = !DILocation(line: 1209, column: 20, scope: !997)
!1067 = !DILocation(line: 1209, column: 13, scope: !997)
!1068 = !DILocation(line: 1212, column: 6, scope: !989)
!1069 = distinct !DISubprogram(name: "as_ptr<u8, alloc::alloc::Global>", linkageName: "_ZN5alloc3vec16Vec$LT$T$C$A$GT$6as_ptr17h107a2e3cbc7884cfE", scope: !54, file: !990, line: 1167, type: !1070, scopeLine: 1167, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1073)
!1070 = !DISubroutineType(types: !1071)
!1071 = !{!73, !1072}
!1072 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&alloc::vec::Vec<u8, alloc::alloc::Global>", baseType: !54, size: 64, align: 64, dwarfAddressSpace: 0)
!1073 = !{!1074, !1075}
!1074 = !DILocalVariable(name: "self", arg: 1, scope: !1069, file: !990, line: 1167, type: !1072)
!1075 = !DILocalVariable(name: "ptr", scope: !1076, file: !990, line: 1170, type: !190, align: 8)
!1076 = distinct !DILexicalBlock(scope: !1069, file: !990, line: 1170, column: 9)
!1077 = !DILocation(line: 1167, column: 19, scope: !1069)
!1078 = !DILocalVariable(name: "metadata", scope: !1079, file: !990, line: 1172, type: !7, align: 1)
!1079 = !DILexicalBlockFile(scope: !1080, file: !990, discriminator: 0)
!1080 = distinct !DISubprogram(name: "from_raw_parts_mut<u8>", linkageName: "_ZN4core3ptr8metadata18from_raw_parts_mut17hdf3ccd62c26a3421E", scope: !1003, file: !1002, line: 127, type: !1004, scopeLine: 127, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1081)
!1081 = !{!1082, !1078}
!1082 = !DILocalVariable(name: "data_address", scope: !1079, file: !990, line: 1172, type: !1006, align: 8)
!1083 = !DILocation(line: 1172, column: 21, scope: !1079, inlinedAt: !1084)
!1084 = !DILocation(line: 668, column: 5, scope: !1085, inlinedAt: !1086)
!1085 = distinct !DISubprogram(name: "null_mut<u8>", linkageName: "_ZN4core3ptr8null_mut17hb85bf713688bbfa1E", scope: !65, file: !636, line: 667, type: !1012, scopeLine: 667, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !23)
!1086 = !DILocation(line: 38, column: 41, scope: !1087, inlinedAt: !1091)
!1087 = distinct !DISubprogram(name: "is_null<u8>", linkageName: "_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17h9dc7df5c57c58925E", scope: !1017, file: !1016, line: 35, type: !1019, scopeLine: 35, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1088)
!1088 = !{!1089}
!1089 = !DILocalVariable(name: "self", scope: !1090, file: !990, line: 1172, type: !190, align: 8)
!1090 = !DILexicalBlockFile(scope: !1087, file: !990, discriminator: 0)
!1091 = !DILocation(line: 1172, column: 21, scope: !1076)
!1092 = !DILocation(line: 1170, column: 19, scope: !1069)
!1093 = !DILocalVariable(name: "self", scope: !1094, file: !990, line: 1170, type: !1032, align: 8)
!1094 = !DILexicalBlockFile(scope: !1095, file: !990, discriminator: 0)
!1095 = distinct !DISubprogram(name: "ptr<u8, alloc::alloc::Global>", linkageName: "_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$3ptr17hd2965d8d15b23788E", scope: !59, file: !1029, line: 223, type: !1030, scopeLine: 223, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1096)
!1096 = !{!1093}
!1097 = !DILocation(line: 1170, column: 19, scope: !1094, inlinedAt: !1092)
!1098 = !DILocalVariable(name: "self", scope: !1099, file: !990, line: 1170, type: !63, align: 8)
!1099 = !DILexicalBlockFile(scope: !1100, file: !990, discriminator: 0)
!1100 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha55716535ab1b589E", scope: !63, file: !187, line: 103, type: !188, scopeLine: 103, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1101)
!1101 = !{!1098}
!1102 = !DILocation(line: 1170, column: 19, scope: !1099, inlinedAt: !1103)
!1103 = !DILocation(line: 224, column: 9, scope: !1095, inlinedAt: !1092)
!1104 = !DILocalVariable(name: "self", scope: !1105, file: !990, line: 1170, type: !69, align: 8)
!1105 = !DILexicalBlockFile(scope: !1106, file: !990, discriminator: 0)
!1106 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17hf95529f8199b6675E", scope: !69, file: !176, line: 330, type: !195, scopeLine: 330, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1107)
!1107 = !{!1104}
!1108 = !DILocation(line: 1170, column: 19, scope: !1105, inlinedAt: !1109)
!1109 = !DILocation(line: 104, column: 9, scope: !1100, inlinedAt: !1103)
!1110 = !DILocation(line: 1170, column: 13, scope: !1076)
!1111 = !DILocation(line: 1172, column: 21, scope: !1090, inlinedAt: !1091)
!1112 = !DILocalVariable(name: "self", scope: !1113, file: !990, line: 1172, type: !190, align: 8)
!1113 = !DILexicalBlockFile(scope: !1114, file: !990, discriminator: 0)
!1114 = distinct !DISubprogram(name: "guaranteed_eq<u8>", linkageName: "_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$13guaranteed_eq17he9c749abe586e6dfE", scope: !1017, file: !1016, line: 707, type: !1052, scopeLine: 707, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1115)
!1115 = !{!1112, !1116}
!1116 = !DILocalVariable(name: "other", scope: !1113, file: !990, line: 1172, type: !190, align: 8)
!1117 = !DILocation(line: 1172, column: 21, scope: !1113, inlinedAt: !1118)
!1118 = !DILocation(line: 38, column: 9, scope: !1087, inlinedAt: !1091)
!1119 = !DILocation(line: 1172, column: 21, scope: !1120, inlinedAt: !1124)
!1120 = !DILexicalBlockFile(scope: !1121, file: !990, discriminator: 0)
!1121 = distinct !DISubprogram(name: "invalid_mut<()>", linkageName: "_ZN4core3ptr11invalid_mut17h766709a69147b3ddE", scope: !65, file: !636, line: 569, type: !1061, scopeLine: 569, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !231, retainedNodes: !1122)
!1122 = !{!1123}
!1123 = !DILocalVariable(name: "addr", scope: !1120, file: !990, line: 1172, type: !9, align: 8)
!1124 = !DILocation(line: 668, column: 24, scope: !1085, inlinedAt: !1086)
!1125 = !DILocation(line: 1172, column: 20, scope: !1076)
!1126 = !DILocation(line: 1172, column: 13, scope: !1076)
!1127 = !DILocation(line: 1175, column: 6, scope: !1069)
!1128 = distinct !DISubprogram(name: "current_memory<u8, alloc::alloc::Global>", linkageName: "_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$14current_memory17hea955b31486f6310E", scope: !59, file: !1029, line: 240, type: !1129, scopeLine: 240, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1148)
!1129 = !DISubroutineType(types: !1130)
!1130 = !{!1131, !1032}
!1131 = !DICompositeType(tag: DW_TAG_structure_type, name: "Option<(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)>", scope: !443, file: !2, size: 192, align: 64, elements: !1132, templateParams: !23, identifier: "2441bf159aec13ad0ba597f59aeb1a1")
!1132 = !{!1133}
!1133 = !DICompositeType(tag: DW_TAG_variant_part, scope: !1131, file: !2, size: 192, align: 64, elements: !1134, templateParams: !23, identifier: "d785942d6e728cf8ed28d4d1a571b7a3", discriminator: !1147)
!1134 = !{!1135, !1143}
!1135 = !DIDerivedType(tag: DW_TAG_member, name: "None", scope: !1133, file: !2, baseType: !1136, size: 192, align: 64, extraData: i64 0)
!1136 = !DICompositeType(tag: DW_TAG_structure_type, name: "None", scope: !1131, file: !2, size: 192, align: 64, elements: !23, templateParams: !1137, identifier: "4d71821a6a04b7dadd5f931d25e98cb2")
!1137 = !{!1138}
!1138 = !DITemplateTypeParameter(name: "T", type: !1139)
!1139 = !DICompositeType(tag: DW_TAG_structure_type, name: "(core::ptr::non_null::NonNull<u8>, core::alloc::layout::Layout)", file: !2, size: 192, align: 64, elements: !1140, templateParams: !23, identifier: "c358a41279bc49b48121f0f71b1b3c8")
!1140 = !{!1141, !1142}
!1141 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !1139, file: !2, baseType: !69, size: 64, align: 64)
!1142 = !DIDerivedType(tag: DW_TAG_member, name: "__1", scope: !1139, file: !2, baseType: !698, size: 128, align: 64, offset: 64)
!1143 = !DIDerivedType(tag: DW_TAG_member, name: "Some", scope: !1133, file: !2, baseType: !1144, size: 192, align: 64)
!1144 = !DICompositeType(tag: DW_TAG_structure_type, name: "Some", scope: !1131, file: !2, size: 192, align: 64, elements: !1145, templateParams: !1137, identifier: "3a54c5b1a06a194b358330f440d65fe5")
!1145 = !{!1146}
!1146 = !DIDerivedType(tag: DW_TAG_member, name: "__0", scope: !1144, file: !2, baseType: !1139, size: 192, align: 64)
!1147 = !DIDerivedType(tag: DW_TAG_member, scope: !1131, file: !2, baseType: !88, size: 64, align: 64, offset: 128, flags: DIFlagArtificial)
!1148 = !{!1149, !1150}
!1149 = !DILocalVariable(name: "self", arg: 1, scope: !1128, file: !1029, line: 240, type: !1032)
!1150 = !DILocalVariable(name: "layout", scope: !1151, file: !1029, line: 247, type: !698, align: 8)
!1151 = distinct !DILexicalBlock(scope: !1128, file: !1029, line: 247, column: 17)
!1152 = !DILocation(line: 240, column: 23, scope: !1128)
!1153 = !DILocalVariable(name: "self", scope: !1154, file: !1029, line: 247, type: !709, align: 8)
!1154 = !DILexicalBlockFile(scope: !1155, file: !1029, discriminator: 0)
!1155 = distinct !DISubprogram(name: "unwrap_unchecked<core::alloc::layout::Layout, core::alloc::layout::LayoutError>", linkageName: "_ZN4core6result19Result$LT$T$C$E$GT$16unwrap_unchecked17h56d89e3ff2ae9ba4E", scope: !709, file: !812, line: 1520, type: !1156, scopeLine: 1520, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !717, retainedNodes: !1158)
!1156 = !DISubroutineType(types: !1157)
!1157 = !{!698, !709, !875}
!1158 = !{!1153, !1159}
!1159 = !DILocalVariable(name: "t", scope: !1160, file: !1029, line: 247, type: !698, align: 8)
!1160 = !DILexicalBlockFile(scope: !1161, file: !1029, discriminator: 0)
!1161 = distinct !DILexicalBlock(scope: !1155, file: !812, line: 1523, column: 13)
!1162 = !DILocation(line: 247, column: 30, scope: !1154, inlinedAt: !1163)
!1163 = !DILocation(line: 247, column: 30, scope: !1128)
!1164 = !DILocalVariable(name: "pointer", scope: !1165, file: !1029, line: 248, type: !69, align: 8)
!1165 = !DILexicalBlockFile(scope: !1166, file: !1029, discriminator: 0)
!1166 = distinct !DISubprogram(name: "from<u8>", linkageName: "_ZN119_$LT$core..ptr..unique..Unique$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..non_null..NonNull$LT$T$GT$$GT$$GT$4from17h1c3c3f3bab145b6fE", scope: !1167, file: !187, line: 190, type: !1168, scopeLine: 190, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1170)
!1167 = !DINamespace(name: "{impl#11}", scope: !64)
!1168 = !DISubroutineType(types: !1169)
!1169 = !{!63, !69}
!1170 = !{!1164}
!1171 = !DILocation(line: 248, column: 23, scope: !1165, inlinedAt: !1172)
!1172 = !DILocation(line: 137, column: 9, scope: !1173, inlinedAt: !1181)
!1173 = distinct !DISubprogram(name: "cast<u8, u8>", linkageName: "_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17h525929ca60f0c1d5E", scope: !63, file: !187, line: 136, type: !1174, scopeLine: 136, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !1179, retainedNodes: !1176)
!1174 = !DISubroutineType(types: !1175)
!1175 = !{!63, !63}
!1176 = !{!1177}
!1177 = !DILocalVariable(name: "self", scope: !1178, file: !1029, line: 248, type: !63, align: 8)
!1178 = !DILexicalBlockFile(scope: !1173, file: !1029, discriminator: 0)
!1179 = !{!76, !1180}
!1180 = !DITemplateTypeParameter(name: "U", type: !74)
!1181 = !DILocation(line: 248, column: 23, scope: !1151)
!1182 = !DILocation(line: 241, column: 12, scope: !1128)
!1183 = !DILocation(line: 241, column: 40, scope: !1128)
!1184 = !DILocation(line: 247, column: 49, scope: !1128)
!1185 = !DILocation(line: 242, column: 13, scope: !1128)
!1186 = !DILocation(line: 241, column: 9, scope: !1128)
!1187 = !DILocation(line: 251, column: 6, scope: !1128)
!1188 = !DILocation(line: 247, column: 30, scope: !1160, inlinedAt: !1163)
!1189 = !DILocation(line: 247, column: 21, scope: !1151)
!1190 = !DILocation(line: 248, column: 23, scope: !1178, inlinedAt: !1181)
!1191 = !DILocalVariable(name: "self", scope: !1192, file: !1029, line: 248, type: !69, align: 8)
!1192 = !DILexicalBlockFile(scope: !1193, file: !1029, discriminator: 0)
!1193 = distinct !DISubprogram(name: "cast<u8, u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h3cb335321a5461f6E", scope: !69, file: !176, line: 453, type: !1194, scopeLine: 453, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !1179, retainedNodes: !1196)
!1194 = !DISubroutineType(types: !1195)
!1195 = !{!69, !69}
!1196 = !{!1191}
!1197 = !DILocation(line: 248, column: 23, scope: !1192, inlinedAt: !1198)
!1198 = !DILocation(line: 137, column: 22, scope: !1173, inlinedAt: !1181)
!1199 = !DILocalVariable(name: "self", scope: !1200, file: !1029, line: 248, type: !69, align: 8)
!1200 = !DILexicalBlockFile(scope: !1201, file: !1029, discriminator: 0)
!1201 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17hf95529f8199b6675E", scope: !69, file: !176, line: 330, type: !195, scopeLine: 330, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1202)
!1202 = !{!1199}
!1203 = !DILocation(line: 248, column: 23, scope: !1200, inlinedAt: !1204)
!1204 = !DILocation(line: 455, column: 41, scope: !1193, inlinedAt: !1198)
!1205 = !DILocalVariable(name: "ptr", scope: !1206, file: !1029, line: 248, type: !190, align: 8)
!1206 = !DILexicalBlockFile(scope: !1207, file: !1029, discriminator: 0)
!1207 = distinct !DISubprogram(name: "new_unchecked<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h9e66c3bf20657540E", scope: !69, file: !176, line: 196, type: !202, scopeLine: 196, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1208)
!1208 = !{!1205}
!1209 = !DILocation(line: 248, column: 23, scope: !1206, inlinedAt: !1210)
!1210 = !DILocation(line: 455, column: 18, scope: !1193, inlinedAt: !1198)
!1211 = !DILocation(line: 247, column: 30, scope: !1212, inlinedAt: !1214)
!1212 = !DILexicalBlockFile(scope: !1213, file: !1029, discriminator: 0)
!1213 = distinct !DISubprogram(name: "unreachable_unchecked", linkageName: "_ZN4core4hint21unreachable_unchecked17h7044fce09d646658E", scope: !227, file: !226, line: 100, type: !21, scopeLine: 100, flags: DIFlagPrototyped | DIFlagNoReturn, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !23)
!1214 = !DILocation(line: 1525, column: 32, scope: !1155, inlinedAt: !1163)
!1215 = !DILocation(line: 248, column: 22, scope: !1151)
!1216 = !DILocation(line: 248, column: 17, scope: !1151)
!1217 = distinct !DISubprogram(name: "fmt", linkageName: "_ZN60_$LT$alloc..string..String$u20$as$u20$core..fmt..Display$GT$3fmt17hf3eccfebf7e287d9E", scope: !1219, file: !1218, line: 2227, type: !481, scopeLine: 2227, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1220)
!1218 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/alloc/src/string.rs", directory: "", checksumkind: CSK_MD5, checksum: "e1c2cdf24b94f38a53da13b30e8aa8ef")
!1219 = !DINamespace(name: "{impl#20}", scope: !313)
!1220 = !{!1221, !1222}
!1221 = !DILocalVariable(name: "self", arg: 1, scope: !1217, file: !1218, line: 2227, type: !470)
!1222 = !DILocalVariable(name: "f", arg: 2, scope: !1217, file: !1218, line: 2227, type: !433)
!1223 = !DILocation(line: 2227, column: 12, scope: !1217)
!1224 = !DILocation(line: 2227, column: 19, scope: !1217)
!1225 = !DILocation(line: 2228, column: 28, scope: !1217)
!1226 = !DILocation(line: 2228, column: 9, scope: !1217)
!1227 = !DILocation(line: 2229, column: 6, scope: !1217)
!1228 = distinct !DISubprogram(name: "deallocate", linkageName: "_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hc195185e441b0100E", scope: !1230, file: !1229, line: 246, type: !1231, scopeLine: 246, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1234)
!1229 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/alloc/src/alloc.rs", directory: "", checksumkind: CSK_MD5, checksum: "b6c7758b12bd6b7f0705d9bc90e671ea")
!1230 = !DINamespace(name: "{impl#1}", scope: !83)
!1231 = !DISubroutineType(types: !1232)
!1232 = !{null, !1233, !69, !698}
!1233 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&alloc::alloc::Global", baseType: !82, size: 64, align: 64, dwarfAddressSpace: 0)
!1234 = !{!1235, !1236, !1237}
!1235 = !DILocalVariable(name: "self", arg: 1, scope: !1228, file: !1229, line: 246, type: !1233)
!1236 = !DILocalVariable(name: "ptr", arg: 2, scope: !1228, file: !1229, line: 246, type: !69)
!1237 = !DILocalVariable(name: "layout", arg: 3, scope: !1228, file: !1229, line: 246, type: !698)
!1238 = !DILocation(line: 246, column: 26, scope: !1228)
!1239 = !DILocation(line: 246, column: 33, scope: !1228)
!1240 = !DILocation(line: 246, column: 51, scope: !1228)
!1241 = !DILocalVariable(name: "layout", scope: !1242, file: !1229, line: 250, type: !698, align: 8)
!1242 = distinct !DISubprogram(name: "dealloc", linkageName: "_ZN5alloc5alloc7dealloc17h0b1a547c099ea60eE", scope: !83, file: !1229, line: 112, type: !1243, scopeLine: 112, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1245)
!1243 = !DISubroutineType(types: !1244)
!1244 = !{null, !190, !698}
!1245 = !{!1246, !1241}
!1246 = !DILocalVariable(name: "ptr", scope: !1242, file: !1229, line: 250, type: !190, align: 8)
!1247 = !DILocation(line: 250, column: 22, scope: !1242, inlinedAt: !1248)
!1248 = !DILocation(line: 250, column: 22, scope: !1228)
!1249 = !DILocalVariable(name: "self", scope: !1250, file: !1229, line: 250, type: !735, align: 8)
!1250 = !DILexicalBlockFile(scope: !1251, file: !1229, discriminator: 0)
!1251 = distinct !DISubprogram(name: "get", linkageName: "_ZN4core3num7nonzero12NonZeroUsize3get17h9c94461a2a00f410E", scope: !735, file: !734, line: 82, type: !739, scopeLine: 82, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1252)
!1252 = !{!1249}
!1253 = !DILocation(line: 250, column: 22, scope: !1250, inlinedAt: !1254)
!1254 = !DILocation(line: 131, column: 9, scope: !1255, inlinedAt: !1262)
!1255 = distinct !DISubprogram(name: "align", linkageName: "_ZN4core5alloc6layout6Layout5align17h0c84d30fdece91c4E", scope: !698, file: !697, line: 130, type: !1256, scopeLine: 130, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1259)
!1256 = !DISubroutineType(types: !1257)
!1257 = !{!9, !1258}
!1258 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&core::alloc::layout::Layout", baseType: !698, size: 64, align: 64, dwarfAddressSpace: 0)
!1259 = !{!1260}
!1260 = !DILocalVariable(name: "self", scope: !1261, file: !1229, line: 250, type: !1258, align: 8)
!1261 = !DILexicalBlockFile(scope: !1255, file: !1229, discriminator: 0)
!1262 = !DILocation(line: 113, column: 49, scope: !1242, inlinedAt: !1248)
!1263 = !DILocalVariable(name: "self", scope: !1264, file: !1229, line: 250, type: !704, align: 8)
!1264 = !DILexicalBlockFile(scope: !1265, file: !1229, discriminator: 0)
!1265 = distinct !DISubprogram(name: "as_nonzero", linkageName: "_ZN4core3mem11valid_align10ValidAlign10as_nonzero17h74c9ba41fef24755E", scope: !704, file: !747, line: 39, type: !748, scopeLine: 39, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1266)
!1266 = !{!1263}
!1267 = !DILocation(line: 250, column: 22, scope: !1264, inlinedAt: !1254)
!1268 = !DILocation(line: 247, column: 12, scope: !1228)
!1269 = !DILocalVariable(name: "self", scope: !1270, file: !1229, line: 247, type: !1258, align: 8)
!1270 = !DILexicalBlockFile(scope: !1271, file: !1229, discriminator: 0)
!1271 = distinct !DISubprogram(name: "size", linkageName: "_ZN4core5alloc6layout6Layout4size17h7930d014522e2d4cE", scope: !698, file: !697, line: 120, type: !1256, scopeLine: 120, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1272)
!1272 = !{!1269}
!1273 = !DILocation(line: 247, column: 12, scope: !1270, inlinedAt: !1268)
!1274 = !DILocation(line: 247, column: 9, scope: !1228)
!1275 = !DILocation(line: 250, column: 30, scope: !1228)
!1276 = !DILocalVariable(name: "self", scope: !1277, file: !1229, line: 250, type: !69, align: 8)
!1277 = !DILexicalBlockFile(scope: !1278, file: !1229, discriminator: 0)
!1278 = distinct !DISubprogram(name: "as_ptr<u8>", linkageName: "_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17hf95529f8199b6675E", scope: !69, file: !176, line: 330, type: !195, scopeLine: 330, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1279)
!1279 = !{!1276}
!1280 = !DILocation(line: 250, column: 30, scope: !1277, inlinedAt: !1275)
!1281 = !DILocation(line: 250, column: 44, scope: !1228)
!1282 = !DILocalVariable(name: "self", scope: !1283, file: !1229, line: 250, type: !1258, align: 8)
!1283 = !DILexicalBlockFile(scope: !1284, file: !1229, discriminator: 0)
!1284 = distinct !DISubprogram(name: "size", linkageName: "_ZN4core5alloc6layout6Layout4size17h7930d014522e2d4cE", scope: !698, file: !697, line: 120, type: !1256, scopeLine: 120, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1285)
!1285 = !{!1282}
!1286 = !DILocation(line: 250, column: 22, scope: !1283, inlinedAt: !1287)
!1287 = !DILocation(line: 113, column: 34, scope: !1242, inlinedAt: !1248)
!1288 = !DILocation(line: 250, column: 22, scope: !1261, inlinedAt: !1262)
!1289 = !DILocalVariable(name: "n", scope: !1290, file: !1229, line: 250, type: !9, align: 8)
!1290 = !DILexicalBlockFile(scope: !1291, file: !1229, discriminator: 0)
!1291 = distinct !DISubprogram(name: "new_unchecked", linkageName: "_ZN4core3num7nonzero12NonZeroUsize13new_unchecked17hf4d6591df3991d30E", scope: !735, file: !734, line: 56, type: !756, scopeLine: 56, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1292)
!1292 = !{!1289, !1293}
!1293 = !DILocalVariable(name: "runtime", scope: !1294, file: !1229, line: 250, type: !763, align: 8)
!1294 = !DILexicalBlockFile(scope: !1295, file: !1229, discriminator: 0)
!1295 = distinct !DILexicalBlock(scope: !1291, file: !762, line: 2336, column: 13)
!1296 = !DILocation(line: 250, column: 22, scope: !1290, inlinedAt: !1297)
!1297 = !DILocation(line: 41, column: 18, scope: !1265, inlinedAt: !1254)
!1298 = !DILocation(line: 252, column: 6, scope: !1228)
!1299 = distinct !DISubprogram(name: "deref", linkageName: "_ZN65_$LT$alloc..string..String$u20$as$u20$core..ops..deref..Deref$GT$5deref17hb4bb5046c19f2651E", scope: !1300, file: !1218, line: 2412, type: !1301, scopeLine: 2412, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1303)
!1300 = !DINamespace(name: "{impl#37}", scope: !313)
!1301 = !DISubroutineType(types: !1302)
!1302 = !{!324, !470}
!1303 = !{!1304}
!1304 = !DILocalVariable(name: "self", arg: 1, scope: !1299, file: !1218, line: 2412, type: !470)
!1305 = !DILocation(line: 2412, column: 14, scope: !1299)
!1306 = !DILocation(line: 2413, column: 43, scope: !1299)
!1307 = !DILocalVariable(name: "self", scope: !1308, file: !1218, line: 2413, type: !1072, align: 8)
!1308 = !DILexicalBlockFile(scope: !1309, file: !1218, discriminator: 0)
!1309 = distinct !DISubprogram(name: "deref<u8, alloc::alloc::Global>", linkageName: "_ZN72_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h4023f127840f7205E", scope: !1310, file: !990, line: 2531, type: !1311, scopeLine: 2531, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1313)
!1310 = !DINamespace(name: "{impl#10}", scope: !55)
!1311 = !DISubroutineType(types: !1312)
!1312 = !{!381, !1072}
!1313 = !{!1307}
!1314 = !DILocation(line: 2413, column: 43, scope: !1308, inlinedAt: !1306)
!1315 = !DILocalVariable(name: "data", scope: !1316, file: !1218, line: 2413, type: !73, align: 8)
!1316 = !DILexicalBlockFile(scope: !1317, file: !1218, discriminator: 0)
!1317 = distinct !DISubprogram(name: "from_raw_parts<u8>", linkageName: "_ZN4core5slice3raw14from_raw_parts17h00a8411519a56052E", scope: !1319, file: !1318, line: 90, type: !1321, scopeLine: 90, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1323)
!1318 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/slice/raw.rs", directory: "", checksumkind: CSK_MD5, checksum: "bc05ab33aeb77226885613c6dc511a0a")
!1319 = !DINamespace(name: "raw", scope: !1320)
!1320 = !DINamespace(name: "slice", scope: !66)
!1321 = !DISubroutineType(types: !1322)
!1322 = !{!381, !73, !9}
!1323 = !{!1315, !1324, !1325}
!1324 = !DILocalVariable(name: "len", scope: !1316, file: !1218, line: 2413, type: !9, align: 8)
!1325 = !DILocalVariable(name: "runtime", scope: !1326, file: !1218, line: 2413, type: !1328, align: 8)
!1326 = !DILexicalBlockFile(scope: !1327, file: !1218, discriminator: 0)
!1327 = distinct !DILexicalBlock(scope: !1317, file: !762, line: 2336, column: 13)
!1328 = !DICompositeType(tag: DW_TAG_structure_type, name: "{closure_env#0}<u8>", scope: !1329, file: !2, size: 128, align: 64, elements: !1330, templateParams: !23, identifier: "ca6adac9bf5585e57d20f143c4c8a4b5")
!1329 = !DINamespace(name: "from_raw_parts", scope: !1319)
!1330 = !{!1331, !1333}
!1331 = !DIDerivedType(tag: DW_TAG_member, name: "_ref__data", scope: !1328, file: !2, baseType: !1332, size: 64, align: 64)
!1332 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&*const u8", baseType: !73, size: 64, align: 64, dwarfAddressSpace: 0)
!1333 = !DIDerivedType(tag: DW_TAG_member, name: "_ref__len", scope: !1328, file: !2, baseType: !768, size: 64, align: 64, offset: 64)
!1334 = !DILocation(line: 2413, column: 43, scope: !1316, inlinedAt: !1335)
!1335 = !DILocation(line: 2532, column: 18, scope: !1309, inlinedAt: !1306)
!1336 = !DILocalVariable(name: "data", scope: !1337, file: !1218, line: 2413, type: !73, align: 8)
!1337 = !DILexicalBlockFile(scope: !1338, file: !1218, discriminator: 0)
!1338 = distinct !DISubprogram(name: "slice_from_raw_parts<u8>", linkageName: "_ZN4core3ptr20slice_from_raw_parts17h934e5049742b1f57E", scope: !65, file: !636, line: 695, type: !1339, scopeLine: 695, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1345)
!1339 = !DISubroutineType(types: !1340)
!1340 = !{!1341, !73, !9}
!1341 = !DICompositeType(tag: DW_TAG_structure_type, name: "*const [u8]", file: !2, size: 128, align: 64, elements: !1342, templateParams: !23, identifier: "7b54d414f2f329e57c9aa3e4ca07f4")
!1342 = !{!1343, !1344}
!1343 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !1341, file: !2, baseType: !327, size: 64, align: 64)
!1344 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !1341, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!1345 = !{!1336, !1346}
!1346 = !DILocalVariable(name: "len", scope: !1337, file: !1218, line: 2413, type: !9, align: 8)
!1347 = !DILocation(line: 2413, column: 43, scope: !1337, inlinedAt: !1348)
!1348 = !DILocation(line: 97, column: 11, scope: !1317, inlinedAt: !1335)
!1349 = !DILocalVariable(name: "self", scope: !1350, file: !1218, line: 2413, type: !73, align: 8)
!1350 = !DILexicalBlockFile(scope: !1351, file: !1218, discriminator: 0)
!1351 = distinct !DISubprogram(name: "cast<u8, ()>", linkageName: "_ZN4core3ptr9const_ptr33_$LT$impl$u20$$BP$const$u20$T$GT$4cast17h470bfa4e48187043E", scope: !1353, file: !1352, line: 46, type: !1355, scopeLine: 46, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !1358, retainedNodes: !1357)
!1352 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/ptr/const_ptr.rs", directory: "", checksumkind: CSK_MD5, checksum: "1874e43cb83f8af3048974827047cb9c")
!1353 = !DINamespace(name: "{impl#0}", scope: !1354)
!1354 = !DINamespace(name: "const_ptr", scope: !65)
!1355 = !DISubroutineType(types: !1356)
!1356 = !{!6, !73}
!1357 = !{!1349}
!1358 = !{!76, !1359}
!1359 = !DITemplateTypeParameter(name: "U", type: !7)
!1360 = !DILocation(line: 2413, column: 43, scope: !1350, inlinedAt: !1361)
!1361 = !DILocation(line: 696, column: 20, scope: !1338, inlinedAt: !1348)
!1362 = !DILocalVariable(name: "data_address", scope: !1363, file: !1218, line: 2413, type: !6, align: 8)
!1363 = !DILexicalBlockFile(scope: !1364, file: !1218, discriminator: 0)
!1364 = distinct !DISubprogram(name: "from_raw_parts<[u8]>", linkageName: "_ZN4core3ptr8metadata14from_raw_parts17hafcf9f3205d03e3aE", scope: !1003, file: !1002, line: 110, type: !1365, scopeLine: 110, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1367)
!1365 = !DISubroutineType(types: !1366)
!1366 = !{!1341, !6, !9}
!1367 = !{!1362, !1368}
!1368 = !DILocalVariable(name: "metadata", scope: !1363, file: !1218, line: 2413, type: !9, align: 8)
!1369 = !DILocation(line: 2413, column: 43, scope: !1363, inlinedAt: !1370)
!1370 = !DILocation(line: 696, column: 5, scope: !1338, inlinedAt: !1348)
!1371 = !DILocalVariable(name: "v", scope: !1372, file: !1218, line: 2413, type: !381, align: 8)
!1372 = !DILexicalBlockFile(scope: !1373, file: !1218, discriminator: 0)
!1373 = distinct !DISubprogram(name: "from_utf8_unchecked", linkageName: "_ZN4core3str8converts19from_utf8_unchecked17he549ab4a53945828E", scope: !1375, file: !1374, line: 170, type: !1376, scopeLine: 170, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !23, retainedNodes: !1378)
!1374 = !DIFile(filename: "/rustc/d394408fb38c4de61f765a3ed5189d2731a1da91/library/core/src/str/converts.rs", directory: "", checksumkind: CSK_MD5, checksum: "459d256946ab11c35b95264d728167a0")
!1375 = !DINamespace(name: "converts", scope: !378)
!1376 = !DISubroutineType(types: !1377)
!1377 = !{!324, !381}
!1378 = !{!1371}
!1379 = !DILocation(line: 2413, column: 18, scope: !1372, inlinedAt: !1380)
!1380 = !DILocation(line: 2413, column: 18, scope: !1299)
!1381 = !DILocation(line: 2414, column: 6, scope: !1299)
!1382 = distinct !DISubprogram(name: "drop<u8, alloc::alloc::Global>", linkageName: "_ZN70_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h80e90bd87493e4d3E", scope: !1383, file: !990, line: 2915, type: !1384, scopeLine: 2915, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1386)
!1383 = !DINamespace(name: "{impl#28}", scope: !55)
!1384 = !DISubroutineType(types: !1385)
!1385 = !{null, !993}
!1386 = !{!1387}
!1387 = !DILocalVariable(name: "self", arg: 1, scope: !1382, file: !990, line: 2915, type: !993)
!1388 = !DILocation(line: 2915, column: 13, scope: !1382)
!1389 = !DILocation(line: 2920, column: 62, scope: !1382)
!1390 = !DILocalVariable(name: "data", scope: !1391, file: !990, line: 2920, type: !190, align: 8)
!1391 = !DILexicalBlockFile(scope: !1392, file: !990, discriminator: 0)
!1392 = distinct !DISubprogram(name: "slice_from_raw_parts_mut<u8>", linkageName: "_ZN4core3ptr24slice_from_raw_parts_mut17hd509ea7f437949d9E", scope: !65, file: !636, line: 727, type: !1393, scopeLine: 727, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1399)
!1393 = !DISubroutineType(types: !1394)
!1394 = !{!1395, !190, !9}
!1395 = !DICompositeType(tag: DW_TAG_structure_type, name: "*mut [u8]", file: !2, size: 128, align: 64, elements: !1396, templateParams: !23, identifier: "2081d302591cc0e6b89f57ab75a79c1e")
!1396 = !{!1397, !1398}
!1397 = !DIDerivedType(tag: DW_TAG_member, name: "data_ptr", scope: !1395, file: !2, baseType: !327, size: 64, align: 64)
!1398 = !DIDerivedType(tag: DW_TAG_member, name: "length", scope: !1395, file: !2, baseType: !9, size: 64, align: 64, offset: 64)
!1399 = !{!1390, !1400}
!1400 = !DILocalVariable(name: "len", scope: !1391, file: !990, line: 2920, type: !9, align: 8)
!1401 = !DILocation(line: 2920, column: 32, scope: !1391, inlinedAt: !1402)
!1402 = !DILocation(line: 2920, column: 32, scope: !1382)
!1403 = !DILocation(line: 2920, column: 81, scope: !1382)
!1404 = !DILocalVariable(name: "self", scope: !1405, file: !990, line: 2920, type: !190, align: 8)
!1405 = !DILexicalBlockFile(scope: !1406, file: !990, discriminator: 0)
!1406 = distinct !DISubprogram(name: "cast<u8, ()>", linkageName: "_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$4cast17h5adc6ce3b450e238E", scope: !1017, file: !1016, line: 45, type: !1407, scopeLine: 45, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !1358, retainedNodes: !1409)
!1407 = !DISubroutineType(types: !1408)
!1408 = !{!1006, !190}
!1409 = !{!1404}
!1410 = !DILocation(line: 2920, column: 32, scope: !1405, inlinedAt: !1411)
!1411 = !DILocation(line: 728, column: 24, scope: !1392, inlinedAt: !1402)
!1412 = !DILocalVariable(name: "data_address", scope: !1413, file: !990, line: 2920, type: !1006, align: 8)
!1413 = !DILexicalBlockFile(scope: !1414, file: !990, discriminator: 0)
!1414 = distinct !DISubprogram(name: "from_raw_parts_mut<[u8]>", linkageName: "_ZN4core3ptr8metadata18from_raw_parts_mut17h33ee51c692f019dfE", scope: !1003, file: !1002, line: 127, type: !1415, scopeLine: 127, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !75, retainedNodes: !1417)
!1415 = !DISubroutineType(types: !1416)
!1416 = !{!1395, !1006, !9}
!1417 = !{!1412, !1418}
!1418 = !DILocalVariable(name: "metadata", scope: !1413, file: !990, line: 2920, type: !9, align: 8)
!1419 = !DILocation(line: 2920, column: 32, scope: !1413, inlinedAt: !1420)
!1420 = !DILocation(line: 728, column: 5, scope: !1392, inlinedAt: !1402)
!1421 = !DILocation(line: 2920, column: 13, scope: !1382)
!1422 = !DILocation(line: 2923, column: 6, scope: !1382)
!1423 = distinct !DISubprogram(name: "drop<u8, alloc::alloc::Global>", linkageName: "_ZN77_$LT$alloc..raw_vec..RawVec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hf626a1dd0a70221dE", scope: !1424, file: !1029, line: 477, type: !1425, scopeLine: 477, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !94, templateParams: !84, retainedNodes: !1428)
!1424 = !DINamespace(name: "{impl#3}", scope: !60)
!1425 = !DISubroutineType(types: !1426)
!1426 = !{null, !1427}
!1427 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut alloc::raw_vec::RawVec<u8, alloc::alloc::Global>", baseType: !59, size: 64, align: 64, dwarfAddressSpace: 0)
!1428 = !{!1429, !1430, !1432}
!1429 = !DILocalVariable(name: "self", arg: 1, scope: !1423, file: !1029, line: 477, type: !1427)
!1430 = !DILocalVariable(name: "ptr", scope: !1431, file: !1029, line: 478, type: !69, align: 8)
!1431 = distinct !DILexicalBlock(scope: !1423, file: !1029, line: 478, column: 60)
!1432 = !DILocalVariable(name: "layout", scope: !1431, file: !1029, line: 478, type: !698, align: 8)
!1433 = !DILocation(line: 477, column: 13, scope: !1423)
!1434 = !DILocation(line: 478, column: 38, scope: !1431)
!1435 = !DILocation(line: 478, column: 16, scope: !1431)
!1436 = !DILocation(line: 478, column: 22, scope: !1431)
!1437 = !DILocation(line: 478, column: 27, scope: !1431)
!1438 = !DILocation(line: 479, column: 22, scope: !1431)
!1439 = !DILocation(line: 481, column: 6, scope: !1423)
!1440 = !DILocation(line: 478, column: 9, scope: !1423)
!1441 = distinct !DISubprogram(name: "main", linkageName: "_ZN18build_script_build4main17h51fc63ceaa531570E", scope: !1443, file: !1442, line: 3, type: !21, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagMainSubprogram, unit: !94, templateParams: !23, retainedNodes: !1444)
!1442 = !DIFile(filename: "build.rs", directory: "/home/val/c2rust/tests/enums", checksumkind: CSK_MD5, checksum: "bd66bd68531e5c946ac8b5b2bdc05c85")
!1443 = !DINamespace(name: "build_script_build", scope: null)
!1444 = !{!1445}
!1445 = !DILocalVariable(name: "manifest_dir", scope: !1446, file: !1442, line: 4, type: !312, align: 8)
!1446 = distinct !DILexicalBlock(scope: !1441, file: !1442, line: 4, column: 5)
!1447 = !DILocation(line: 4, column: 9, scope: !1446)
!1448 = !DILocation(line: 4, column: 24, scope: !1441)
!1449 = !DILocation(line: 6, column: 5, scope: !1446)
!1450 = !DILocation(line: 7, column: 1, scope: !1441)
!1451 = !DILocation(line: 3, column: 1, scope: !1441)
!1452 = !DILocation(line: 7, column: 2, scope: !1441)

^0 = module: (path: "./enums/target/debug/build/enum-tests-e089ccba7d518cf6/build_script_build-e089ccba7d518cf6.bc", hash: (3399227774, 4137518031, 2974510573, 138967228, 2700001591))
^1 = gv: (name: "alloc109", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^64)))) ; guid = 532713461843866787
^2 = gv: (name: "llvm.memcpy.p0i8.p0i8.i64") ; guid = 614884070845456474
^3 = gv: (name: "alloc4", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 679918980297323401
^4 = gv: (name: "_ZN3std2rt10lang_start17he4b4cd36ba5e3c57E", summaries: (function: (module: ^0, flags: (linkage: external, visibility: hidden, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 18, calls: ((callee: ^16)), refs: (^8)))) ; guid = 788324216603475447
^5 = gv: (name: "_ZN4core9panicking9panic_fmt17h62ccf03c8a8a51b5E") ; guid = 827351306837972430
^6 = gv: (name: "_ZN18build_script_build4main17h51fc63ceaa531570E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 42, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 0, mustBeUnreachable: 0), calls: ((callee: ^34), (callee: ^52), (callee: ^51), (callee: ^13), (callee: ^56), (callee: ^27), (callee: ^42)), refs: (^49, ^48, ^18, ^60)))) ; guid = 892545408763883673
^7 = gv: (name: "_ZN5alloc3vec16Vec$LT$T$C$A$GT$10as_mut_ptr17hf0ab5348698999aeE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 48))) ; guid = 1864805119877204189
^8 = gv: (name: "vtable.0", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^45, ^12, ^66)))) ; guid = 1971357743223293017
^9 = gv: (name: "llvm.expect.i1") ; guid = 2587125569932775682
^10 = gv: (name: "_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hc195185e441b0100E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 49, calls: ((callee: ^21))))) ; guid = 2712119259984702482
^11 = gv: (name: "_ZN55_$LT$std..env..VarError$u20$as$u20$core..fmt..Debug$GT$3fmt17he46da4fdbd9f8b4bE") ; guid = 2736009175504303697
^12 = gv: (name: "_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h66ac8c8cfdead3faE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 7, calls: ((callee: ^31))))) ; guid = 2853983599465147899
^13 = gv: (name: "_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h017085301cfa8a38E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 6, calls: ((callee: ^41))))) ; guid = 3018226397178917390
^14 = gv: (name: "vtable.1", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^61, ^11)))) ; guid = 3597560949461929725
^15 = gv: (name: "alloc110", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 3853147846103935630
^16 = gv: (name: "_ZN3std2rt19lang_start_internal17h498f9556b87c8e5fE") ; guid = 3879134089768320115
^17 = gv: (name: "_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd6350e6730446559E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 12))) ; guid = 3884435065603415306
^18 = gv: (name: "alloc116", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^55)))) ; guid = 4305218872608525448
^19 = gv: (name: "_ZN70_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h80e90bd87493e4d3E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 39, calls: ((callee: ^7))))) ; guid = 4415565488209657924
^20 = gv: (name: "_ZN77_$LT$alloc..raw_vec..RawVec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hf626a1dd0a70221dE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 34, calls: ((callee: ^28), (callee: ^10))))) ; guid = 4519604417176056032
^21 = gv: (name: "__rust_dealloc") ; guid = 4639430271351303854
^22 = gv: (name: "alloc13", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 5176256132832799374
^23 = gv: (name: "_ZN4core5alloc6layout6Layout5array17h041a339ec38f7fddE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 78, calls: ((callee: ^47), (callee: ^30), (callee: ^35))))) ; guid = 5682666680420760619
^24 = gv: (name: "llvm.assume") ; guid = 6385187066495850096
^25 = gv: (name: "llvm.umul.with.overflow.i64") ; guid = 6837502597287762023
^26 = gv: (name: "_ZN4core6result13unwrap_failed17hff48f82f03d418aeE") ; guid = 7013031364768356509
^27 = gv: (name: "_ZN3std2io5stdio6_print17h141fc01f1d2bd34dE") ; guid = 7070043249408112355
^28 = gv: (name: "_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$14current_memory17hea955b31486f6310E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 78, calls: ((callee: ^23), (callee: ^29))))) ; guid = 7545660092886322770
^29 = gv: (name: "_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h093103a2bfe88da2E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 5, calls: ((callee: ^17))))) ; guid = 7688182172724293230
^30 = gv: (name: "_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h3d20e1e9b1fe581cE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 2))) ; guid = 8029908458404848097
^31 = gv: (name: "_ZN4core3ops8function6FnOnce9call_once17h5767b38317950c8bE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 23, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 0, mustBeUnreachable: 0), calls: ((callee: ^45)), refs: (^49)))) ; guid = 8276833953804504892
^32 = gv: (name: "_ZN4core3ops8function6FnOnce9call_once17h6e624e4cb526ac89E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 6, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 0, hasUnknownCall: 1, mustBeUnreachable: 0)))) ; guid = 9765421252748408294
^33 = gv: (name: "_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h8a2d015129d5babaE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 2))) ; guid = 9770204460027457820
^34 = gv: (name: "_ZN3std3env3var17h1ab2aebfffbd5e57E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 28, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 0, mustBeUnreachable: 0), calls: ((callee: ^65), (callee: ^40)), refs: (^49)))) ; guid = 10385369156007821007
^35 = gv: (name: "_ZN4core5alloc6layout6Layout21from_size_valid_align17h362893bcbac9d0a1E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 41))) ; guid = 10424450021191632128
^36 = gv: (name: "__rustc_debug_gdb_scripts_section__", summaries: (variable: (module: ^0, flags: (linkage: linkonce_odr, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 0, canAutoHide: 1), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 11475342894608204461
^37 = gv: (name: "_ZN4core3ptr47drop_in_place$LT$std..ffi..os_str..OsString$GT$17h421f40303d5a8656E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 6, calls: ((callee: ^62))))) ; guid = 11537081811531078069
^38 = gv: (name: "_ZN3std3ffi6os_str85_$LT$impl$u20$core..convert..AsRef$LT$std..ffi..os_str..OsStr$GT$$u20$for$u20$str$GT$6as_ref17h6f335272d1955c69E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 50))) ; guid = 11637856048728269973
^39 = gv: (name: "_ZN65_$LT$alloc..string..String$u20$as$u20$core..ops..deref..Deref$GT$5deref17hb4bb5046c19f2651E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 62, calls: ((callee: ^43))))) ; guid = 11729100670403160130
^40 = gv: (name: "_ZN3std3env4_var17h48effbaa8b2613b5E") ; guid = 12001253703259316028
^41 = gv: (name: "_ZN4core3ptr46drop_in_place$LT$alloc..vec..Vec$LT$u8$GT$$GT$17h0a98817a91215818E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 28, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 0, mustBeUnreachable: 0), calls: ((callee: ^19), (callee: ^50), (callee: ^42)), refs: (^49)))) ; guid = 12451725948408244091
^42 = gv: (name: "_ZN4core9panicking15panic_no_unwind17h62f8113f44cbfcbfE") ; guid = 12728155646447917706
^43 = gv: (name: "_ZN5alloc3vec16Vec$LT$T$C$A$GT$6as_ptr17h107a2e3cbc7884cfE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 48))) ; guid = 13149437661177441320
^44 = gv: (name: "llvm.dbg.declare") ; guid = 13513223491971101989
^45 = gv: (name: "_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h7596c761f25e6e47E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 17, calls: ((callee: ^63), (callee: ^33))))) ; guid = 13531826165324567513
^46 = gv: (name: "alloc16", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 13563875522963885021
^47 = gv: (name: "_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17hb90a4357ac0c70a7E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 68))) ; guid = 14630318317711255469
^48 = gv: (name: "alloc114", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 14759678384213125728
^49 = gv: (name: "rust_eh_personality") ; guid = 14807195490537628141
^50 = gv: (name: "_ZN4core3ptr53drop_in_place$LT$alloc..raw_vec..RawVec$LT$u8$GT$$GT$17h63264ea4812108b9E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 5, calls: ((callee: ^20))))) ; guid = 15135727680115394776
^51 = gv: (name: "_ZN4core3fmt10ArgumentV111new_display17h8e936bdad87877f0E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 28, refs: (^57)))) ; guid = 15195121395766964385
^52 = gv: (name: "_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17hc8210bfc41415118E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 39, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 0, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 0, mustBeUnreachable: 0), calls: ((callee: ^26), (callee: ^61), (callee: ^42)), refs: (^49, ^14, ^15)))) ; guid = 15315262755653711258
^53 = gv: (name: "main", summaries: (function: (module: ^0, flags: (linkage: external, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 0, canAutoHide: 0), insts: 5, calls: ((callee: ^4)), refs: (^36, ^6)))) ; guid = 15822663052811949562
^54 = gv: (name: "alloc14", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^22)))) ; guid = 16034895122952980091
^55 = gv: (name: "alloc115", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 16050011913600061116
^56 = gv: (name: "_ZN4core3fmt9Arguments6new_v117h4b70dcc115ea8332E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 51, calls: ((callee: ^56), (callee: ^5)), refs: (^46, ^54, ^1)))) ; guid = 16285098749772921773
^57 = gv: (name: "_ZN60_$LT$alloc..string..String$u20$as$u20$core..fmt..Display$GT$3fmt17hf3eccfebf7e287d9E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 11, calls: ((callee: ^39), (callee: ^59))))) ; guid = 16420698317512973340
^58 = gv: (name: "alloc6", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 16449001747878802504
^59 = gv: (name: "_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17hde81f4d22eef4d42E") ; guid = 16511831571186081041
^60 = gv: (name: "alloc5", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1), refs: (^3, ^58)))) ; guid = 16609412219955701674
^61 = gv: (name: "_ZN4core3ptr39drop_in_place$LT$std..env..VarError$GT$17hbb9f1951a94d6b0bE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 13, calls: ((callee: ^37))))) ; guid = 16747349896647353124
^62 = gv: (name: "_ZN4core3ptr48drop_in_place$LT$std..sys..unix..os_str..Buf$GT$17he26a14dc108ef330E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 6, calls: ((callee: ^41))))) ; guid = 16779375273609663861
^63 = gv: (name: "_ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17hb7516deb05ead5dbE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 18, funcFlags: (readNone: 0, readOnly: 0, noRecurse: 0, returnDoesNotAlias: 0, noInline: 1, alwaysInline: 0, noUnwind: 0, mayThrow: 1, hasUnknownCall: 1, mustBeUnreachable: 0), calls: ((callee: ^32)), refs: (^49)))) ; guid = 17650341175173257349
^64 = gv: (name: "alloc108", summaries: (variable: (module: ^0, flags: (linkage: private, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), varFlags: (readonly: 1, writeonly: 0, constant: 1)))) ; guid = 17849096829375754426
^65 = gv: (name: "_ZN55_$LT$$RF$T$u20$as$u20$core..convert..AsRef$LT$U$GT$$GT$6as_ref17h8db5e479bfb5017aE", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 13, calls: ((callee: ^38))))) ; guid = 17857817978248459493
^66 = gv: (name: "_ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h196226712f618a69E", summaries: (function: (module: ^0, flags: (linkage: internal, visibility: default, notEligibleToImport: 0, live: 0, dsoLocal: 1, canAutoHide: 0), insts: 3))) ; guid = 17863658599955447770
^67 = blockcount: 153
