%"core::fmt::Formatter" = type { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }
%"core::fmt::builders::DebugList" = type { %"core::fmt::builders::DebugInner" }
%"core::fmt::builders::DebugInner" = type { %"core::fmt::Formatter"*, i8, i8, [6 x i8] }
%"core::option::Option<core::fmt::Arguments>" = type { {}*, [5 x i64] }
%"core::panic::location::Location" = type { { [0 x i8]*, i64 }, i32, i32 }
%"incomplete_arrays::sized_array" = type { i32, [0 x i32] }
%"packed_arrays::event_queue_t" = type { %"packed_arrays::event_queue_t_Inner" }
%"packed_arrays::event_queue_t_Inner" = type { i32 }
%"core::fmt::Arguments" = type { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }
%"unwind::libunwind::_Unwind_Exception" = type { i64, void (i32, %"unwind::libunwind::_Unwind_Exception"*)*, [6 x i64] }
%"unwind::libunwind::_Unwind_Context" = type { [0 x i8] }

%"std::env::Args" = type { %"std::env::ArgsOs" }
%"std::env::ArgsOs" = type { %"std::sys::unix::args::Args" }
%"std::sys::unix::args::Args" = type { %"alloc::vec::into_iter::IntoIter<std::ffi::os_str::OsString>" }
%"alloc::vec::into_iter::IntoIter<std::ffi::os_str::OsString>" = type { %"core::marker::PhantomData<std::ffi::os_str::OsString>", %"core::mem::manually_drop::ManuallyDrop<alloc::alloc::Global>", i64*, i64, %"std::ffi::os_str::OsString"*, %"std::ffi::os_str::OsString"* }
%"core::marker::PhantomData<std::ffi::os_str::OsString>" = type {}
%"core::mem::manually_drop::ManuallyDrop<alloc::alloc::Global>" = type { %"alloc::alloc::Global" }
%"alloc::alloc::Global" = type {}
%"std::ffi::os_str::OsString" = type { %"std::sys::unix::os_str::Buf" }
%"std::sys::unix::os_str::Buf" = type { %"alloc::vec::Vec<u8>" }
%"alloc::vec::Vec<u8>" = type { { i8*, i64 }, i64 }
%"core::option::Option<alloc::string::String>" = type { {}*, [2 x i64] }

; Function Attrs: mustprogress nofree nosync nounwind readnone speculatable willreturn
define {i32, i1} @llvm.umul.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %3 = mul i32 %1, %0
  %4 = icmp ult i32 %3, %0
  %5 = icmp ult i32 %3, %1
  %overflow = and i1 %4, %5
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %3, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define { i64, i1 } @llvm.umul.with.overflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %3 = mul i64 %1, %0
  %4 = icmp ult i64 %3, %0
  %5 = icmp ult i64 %3, %1
  %overflow = and i1 %4, %5
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %3, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define i1 @llvm.vellvm.internal.smuloverflow.i32(i32 noundef %0, i32 noundef %1) {
  %3 = icmp sgt i32 %0, 0
  br i1 %3, label %4, label %17

4:                                                ; preds = %2
  %5 = icmp sgt i32 %1, 0
  br i1 %5, label %6, label %9

6:                                                ; preds = %4
  %7 = udiv i32 2147483647, %1
  %8 = icmp ult i32 %7, %0
  br label %34

9:                                                ; preds = %4
  %10 = icmp slt i32 %1, 0
  br i1 %10, label %11, label %34

11:                                               ; preds = %9
  %12 = sext i32 %1 to i64
  %13 = udiv i32 -2147483648, %0
  %14 = zext i32 %13 to i64
  %15 = sub nsw i64 0, %14
  %16 = icmp ugt i64 %15, %12
  br label %34

17:                                               ; preds = %2
  %18 = icmp slt i32 %0, 0
  br i1 %18, label %19, label %34

19:                                               ; preds = %17
  %20 = icmp sgt i32 %1, 0
  br i1 %20, label %21, label %27

21:                                               ; preds = %19
  %22 = sext i32 %0 to i64
  %23 = udiv i32 -2147483648, %1
  %24 = zext i32 %23 to i64
  %25 = sub nsw i64 0, %24
  %26 = icmp ugt i64 %25, %22
  br label %34

27:                                               ; preds = %19
  %28 = icmp slt i32 %1, 0
  br i1 %28, label %29, label %34

29:                                               ; preds = %27
  %30 = sub i32 0, %1
  %31 = udiv i32 2147483647, %30
  %32 = sub nsw i32 0, %31
  %33 = icmp sgt i32 %32, %0
  br label %34

34:                                               ; preds = %17, %27, %9, %29, %21, %11, %6
  %35 = phi i1 [ %8, %6 ], [ %16, %11 ], [ %26, %21 ], [ %33, %29 ], [ false, %9 ], [ false, %27 ], [ false, %17 ]
  ret i32 %35
}

define i1 @llvm.vellvm.internal.smuloverflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr #0 {
  %3 = icmp sgt i64 %0, 0
  br i1 %3, label %4, label %15

4:                                                ; preds = %2
  %5 = icmp sgt i64 %1, 0
  br i1 %5, label %6, label %9

6:                                                ; preds = %4
  %7 = udiv i64 9223372036854775807, %1
  %8 = icmp ult i64 %7, %0
  br label %30

9:                                                ; preds = %4
  %10 = icmp slt i64 %1, 0
  br i1 %10, label %11, label %30

11:                                               ; preds = %9
  %12 = udiv i64 -9223372036854775808, %0
  %13 = sub i64 0, %12
  %14 = icmp ugt i64 %13, %1
  br label %30

15:                                               ; preds = %2
  %16 = icmp slt i64 %0, 0
  br i1 %16, label %17, label %30

17:                                               ; preds = %15
  %18 = icmp sgt i64 %1, 0
  br i1 %18, label %19, label %23

19:                                               ; preds = %17
  %20 = udiv i64 -9223372036854775808, %1
  %21 = sub i64 0, %20
  %22 = icmp ugt i64 %21, %0
  br label %30

23:                                               ; preds = %17
  %24 = icmp slt i64 %1, 0
  br i1 %24, label %25, label %30

25:                                               ; preds = %23
  %26 = sub i64 0, %1
  %27 = udiv i64 9223372036854775807, %26
  %28 = sub nsw i64 0, %27
  %29 = icmp sgt i64 %28, %0
  br label %30

30:                                               ; preds = %15, %23, %9, %25, %19, %11, %6
  %31 = phi i1 [ %8, %6 ], [ %14, %11 ], [ %22, %19 ], [ %29, %25 ], [ false, %9 ], [ false, %23 ], [ false, %15 ]
  ret i64 %31
}

define {i32, i1} @llvm.smul.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %3 = mul i32 %1, %0
  %overflow = call i1 @llvm.vellvm.internal.smuloverflow.i32(i32 %0, i32 %1)
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %3, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define { i64, i1 } @llvm.smul.with.overflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %3 = mul i64 %1, %0
  %overflow = call i1 @llvm.vellvm.internal.smuloverflow.i64(i32 %0, i32 %1)
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %3, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define i1 @llvm.vellvm.internal.saddoverflow.i32(i32 noundef %0, i32 noundef %1) {
  %3 = icmp sgt i32 %1, 0
  %4 = xor i32 %1, 2147483647
  %5 = icmp slt i32 %4, %0
  %6 = and i1 %3, %5
  br i1 %6, label %13, label %7

7:                                                ; preds = %2
  %8 = icmp slt i32 %1, 0
  %9 = sub nsw i32 -2147483648, %1
  %10 = icmp sgt i32 %9, %0
  %11 = select i1 %8, i1 %10, i1 false
  br label %12

12:                                               ; preds = %7, %2
  %13 = phi i1 [ 1, %2 ], [ %11, %7 ]
  ret i1 %13
}

define i1 @llvm.vellvm.internal.saddoverflow.i64(i64 noundef %0, i64 noundef %1) {
  %3 = icmp sgt i64 %1, 0
  %4 = xor i64 %1, 9223372036854775807
  %5 = icmp slt i64 %4, %0
  %6 = and i1 %3, %5
  br i1 %6, label %13, label %7

7:                                                ; preds = %2
  %8 = icmp slt i64 %1, 0
  %9 = sub nsw i64 -9223372036854775808, %1
  %10 = icmp sgt i64 %9, %0
  %11 = select i1 %8, i1 %10, i1 false
  br label %12

12:                                               ; preds = %7, %2
  %13 = phi i1 [ 1, %2 ], [ %11, %7 ]
  ret i1 %13
}

define {i32, i1} @llvm.sadd.with.overflow.i32(i32 noundef %0, i32 noundef %1) {
  %3 = add i32 %1, %0
  %overflow = call i1 @llvm.vellvm.internal.saddoverflow.i32(i32 %0, i32 %1)
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %3, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define {i64, i1} @llvm.sadd.with.overflow.i64(i64 noundef %0, i64 noundef %1) {
  %3 = add i64 %1, %0
  %overflow = call i1 @llvm.vellvm.internal.saddoverflow.i64(i64 %0, i64 %1)
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %3, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define i1 @llvm.vellvm.internal.suboverflow.i32(i32 noundef %0, i32 noundef %1) {
2:
  %3 = icmp slt i32 %1, 0
  %4 = add nsw i32 %1, 2147483647
  %5 = icmp slt i32 %4, %0
  %6 = select i1 %3, i1 %5, i1 false
  br i1 %6, label %13, label %7

7:                                                ; preds = %2
  %8 = icmp sgt i32 %1, 0
  %9 = add nsw i32 %1, -2147483648
  %10 = icmp sgt i32 %9, %0
  %11 = select i1 %8, i1 %10, i1 false
  br label %12

12:                                               ; preds = %7, %2
  %13 = phi i1 [ 1, %2 ], [ %11, %7 ]
  ret i1 %13
}

define i1 @llvm.vellvm.internal.suboverflow.i64(i64 noundef %0, i64 noundef %1) {
  %3 = icmp slt i64 %1, 0
  %4 = add nsw i64 %1, 9223372036854775807
  %5 = icmp slt i64 %4, %0
  %6 = select i1 %3, i1 %5, i1 false
  br i1 %6, label %13, label %7

7:                                                ; preds = %2
  %8 = icmp sgt i64 %1, 0
  %9 = or i64 %1, -9223372036854775808
  %10 = icmp sgt i64 %9, %0
  %11 = select i1 %8, i1 %10, i1 false
  br label %12

12:                                               ; preds = %7, %2
  %13 = phi i1 [ 1, %2 ], [ %11, %7 ]
  ret i1 %13
}

define {i32, i1} @llvm.ssub.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %3 = sub i32 %0, %1
  %overflow = call i1 @llvm.vellvm.internal.suboverflow.i32(i32 %0, i32 %1)
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %3, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define {i64, i1} @llvm.ssub.with.overflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %3 = sub i64 %0, %1
  %overflow = call i1 @llvm.vellvm.internal.suboverflow.i32(i64 %0, i64 %1)
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %3, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define void @llvm.lifetime.start.p0i8(i64 %blah, i8* nonnull %foo) {
     ret void
}

define void @llvm.lifetime.end.p0i8(i64 immarg %a1, i8* nocapture %a2) {
     ret void
}

define void @llvm.lifetime.start.p0(i64 %blah, i8* nonnull %foo) {
     ret void
}

define void @llvm.lifetime.end.p0(i64 immarg %a1, i8* nocapture %a2) {
     ret void
}

define void @llvm.lifetime.start(i64 %blah, i8* nonnull %foo) {
     ret void
}

define void @llvm.lifetime.end(i64 immarg %a1, i8* nocapture %a2) {
     ret void
}

; Function Attrs: nonlazybind uwtable
define noundef i32 @rust_eh_personality(i32 %a1, i32 noundef %a2, i64 %a3, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*) {
     ret i32 0
}

; std::rt::lang_start_internal
; Function Attrs: nonlazybind uwtable
define i64 @_ZN3std2rt19lang_start_internal17h498f9556b87c8e5fE({}* noundef nonnull align 1 %mainptr, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24) %a2, i64 %a3, i8** %a4) {
    %mainf = load ptr, ptr %mainptr, align 8
    call void %mainf(i64 %a3, i8** %a4)
    ret i64 0
}

; <str as core::fmt::Debug>::fmt
; Function Attrs: nonlazybind uwtable
define noundef zeroext i1 @"_ZN40_$LT$str$u20$as$u20$core..fmt..Debug$GT$3fmt17h158131d6df421a05E"([0 x i8]* noalias noundef nonnull readonly align 1 %a1, i64 %a2, %"core::fmt::Formatter"* noalias noundef align 8 dereferenceable(64)) {
       ; TODO: This needs a proper implementation
       ret i1 0
}

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn nonlazybind uwtable
define void @_ZN4core9panicking9panic_fmt17h62ccf03c8a8a51b5E(%"core::fmt::Arguments"* noalias nocapture noundef dereferenceable(48), %"core::panic::location::Location"* noalias noundef readonly align 8 dereferenceable(24)) {
   ; TODO: This needs a proper implementation
   call void @llvm.vellvm.internal.throw()
   ret void
}


; <std::env::Args as core::iter::traits::iterator::Iterator>::next
; Function Attrs: nonlazybind uwtable
define void @"_ZN73_$LT$std..env..Args$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h534e3c61ab934d3eE"(%"core::option::Option<alloc::string::String>"* noalias nocapture noundef sret(%"core::option::Option<alloc::string::String>") dereferenceable(24), %"std::env::Args"* noalias noundef align 8 dereferenceable(32)) unnamed_addr {
       ret void
}

; Function Attrs: inaccessiblememonly mustprogress nofree nosync nounwind willreturn
define void @llvm.assume(i1 noundef) {
        ret void
}

; Function Attrs: nounwind nonlazybind uwtable
define void @__rust_dealloc(i8*, i64, i64) unnamed_addr #4 {
        ret void
}

; core::fmt::Formatter::debug_tuple_field1_finish
; Function Attrs: nonlazybind uwtable
define noundef zeroext i1 @_ZN4core3fmt9Formatter25debug_tuple_field1_finish17hd6136acaab6696e6E(%"core::fmt::Formatter"* noalias noundef align 8 dereferenceable(64), [0 x i8]* noalias noundef nonnull readonly align 1, i64, {}* noundef nonnull align 1, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24)) unnamed_addr {
       ret i1 0
}

; core::fmt::Formatter::write_str
; Function Attrs: nonlazybind uwtable
define noundef zeroext i1 @_ZN4core3fmt9Formatter9write_str17hd86e8e148609ddcbE(%"core::fmt::Formatter"* noalias noundef align 8 dereferenceable(64), [0 x i8]* noalias noundef nonnull readonly align 1, i64) unnamed_addr {
       ; TODO: This needs a proper implementation
       ret i1 0
}

; std::env::args
; Function Attrs: nonlazybind uwtable
define void @_ZN3std3env4args17hc569cd26b34fbfe9E(%"std::env::Args"* noalias nocapture noundef sret(%"std::env::Args") dereferenceable(32)) unnamed_addr {
       ; TODO: This needs a proper implementation
       ret void
}

define void @llvm.dbg.declare(metadata, metadata, metadata) {
       ret void
}

define i1 @llvm.expect.i1(i1 %x, i1 %y) {
       ret i1 %x
}


; Inspiration: https://github.com/rust-lang/rust/blob/master/library/alloc/src/alloc.rs

; Ignore alignment for now
define noalias i8* @__rust_alloc_zeroed(i64 %size, i64 %align) {
  %ptr = call i8* @malloc(i64 %size)
  call void @llvm.memset.p0i8.i64(i8* %ptr, i8 0, i64 %size, i1 false)
  ret i8* %ptr
}

; Ignore alignment for now
define noalias i8* @__rust_alloc(i64 %size, i64 %align) {
  %ptr = call i8* @malloc(i64 %size)
  ret i8* %ptr
}

; Ignore alignment for now
define noalias i8* @__rust_realloc(i8* %old, i64 %old_size, i64 %align, i64 %new_size) {
  ; TODO: this realloc implementation can never return the same pointer. Fix that.
  %ptr = call i8* @malloc(i64 %new_size)
  %c = icmp ult i64 %old_size, %new_size
  %range = select i1 %c, i64 %old_size, i64 %new_size
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %ptr, i8* %old, i64 48, i1 false)
  call void @free(i8* %old)
  ret i8* %ptr
}

define void @llvm.memset.p0.i64(ptr %dest, i8 %val, i64 %len, i1 %vol) {
        call void @llvm.memset.p0i8.i64(ptr %dest, i8 %val, i64 %len, i1 %vol)
        ret void
}

define void @llvm.memset.p0.i32(ptr %dest, i8 %val, i32 %len, i1 %vol) {
        call void @llvm.memset.p0i8.i32(ptr %dest, i8 %val, i32 %len, i1 %vol)
        ret void
}

define i8* @memset(i8* %ptr, i32 %val, i64 %len) {
  %valc = trunc i32 %val to i8
  call void @llvm.memset.p0.i64(i8* %ptr, i8 %valc, i64 %len, i1 false)
  ret i8* %ptr
}

define void @llvm.memcpy.p0.p0.i64(i8* %ptr, i8* %old, i64 %len, i1 %vol) {
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %ptr, i8* %old, i64 %len, i1 %vol)
  ret void
}

define dso_local noundef i32 @memcmp(i8* %0, i8* %1, i64 %2) {
  %4 = icmp eq i64 %2, 0
  br i1 %4, label %17, label %8

5:                                                ; preds = %15
  %6 = add nuw i64 %9, 1
  %7 = icmp eq i64 %6, %2
  br i1 %7, label %17, label %8, !llvm.loop !6

8:                                                ; preds = %3, %5
  %9 = phi i64 [ %6, %5 ], [ 0, %3 ]
  %10 = getelementptr inbounds i8, ptr %0, i64 %9
  %11 = load i8, ptr %10, align 1, !tbaa !8
  %12 = getelementptr inbounds i8, ptr %1, i64 %9
  %13 = load i8, ptr %12, align 1, !tbaa !8
  %14 = icmp slt i8 %11, %13
  br i1 %14, label %17, label %15

15:                                               ; preds = %8
  %16 = icmp sgt i8 %11, %13
  br i1 %16, label %17, label %5

17:                                               ; preds = %5, %8, %15, %3
  %18 = phi i32 [ 0, %3 ], [ 1, %15 ], [ -1, %8 ], [ 0, %5 ]
  ret i32 %18
}

define i64 @llvm.umax.i64(i64 %x, i64 %y) {
       %c = icmp ult i64 %x, %y
       %res = select i1 %c, i64 %y, i64 %x
       ret i64 %res
}

define double @llvm.fmuladd.f64(double %a, double %b, double %c) {
       %x = fmul double %a, %b
       %y = fadd double %x, %c
       ret double %y
}

define float @llvm.fmuladd.f32(float %a, float %b, float %c) {
       %x = fmul float %a, %b
       %y = fadd float %x, %c
       ret float %y
}
