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
@anon.cb3a820676433a993734d74257001914.1 = private unnamed_addr constant <{ i8*, [16 x i8], i8*, i8*, i8* }> <{ i8* bitcast (void (i8**)* @"_ZN4core3ptr27drop_in_place$LT$$RF$u8$GT$17h2e7752968013085eE" to i8*), [16 x i8] c"\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", i8* bitcast (i1 (%2**, [0 x i8]*, i64)* @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_str17hee7ed837f2be72c2E" to i8*), i8* bitcast (i1 (%2**, i32)* @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$10write_char17h0564e19f9542fbb8E" to i8*), i8* bitcast (i1 (%2**, %13*)* @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_fmt17hc11cd155d0861a3cE" to i8*) }>, align 8

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
  %15 = sub i64 0, %14
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
  %25 = sub i64 0, %24
  %26 = icmp ugt i64 %25, %22
  br label %34

27:                                               ; preds = %19
  %28 = icmp slt i32 %1, 0
  br i1 %28, label %29, label %34

29:                                               ; preds = %27
  %30 = sub i32 0, %1
  %31 = udiv i32 2147483647, %30
  %32 = sub i32 0, %31
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
  %28 = sub i64 0, %27
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
  %9 = sub i32 -2147483648, %1
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
  %9 = sub i64 -9223372036854775808, %1
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
  %4 = add i32 %1, 2147483647
  %5 = icmp slt i32 %4, %0
  %6 = select i1 %3, i1 %5, i1 false
  br i1 %6, label %13, label %7

7:                                                ; preds = %2
  %8 = icmp sgt i32 %1, 0
  %9 = add i32 %1, -2147483648
  %10 = icmp sgt i32 %9, %0
  %11 = select i1 %8, i1 %10, i1 false
  br label %12

12:                                               ; preds = %7, %2
  %13 = phi i1 [ 1, %2 ], [ %11, %7 ]
  ret i1 %13
}

define i1 @llvm.vellvm.internal.suboverflow.i64(i64 noundef %0, i64 noundef %1) {
  %3 = icmp slt i64 %1, 0
  %4 = add i64 %1, 9223372036854775807
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
  %overflow = call i1 @llvm.vellvm.internal.suboverflow.i64(i64 %0, i64 %1)
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


; core::ptr::drop_in_place<&u8>
define internal void @"_ZN4core3ptr27drop_in_place$LT$$RF$u8$GT$17h2e7752968013085eE"(i8** nocapture readnone %0) unnamed_addr #6 !dbg !75465 {
  ret void, !dbg !75466
}

; <&mut W as core::fmt::Write>::write_str
define internal noundef zeroext i1 @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_str17hee7ed837f2be72c2E"(%2** noalias nocapture noundef readonly align 8 dereferenceable(8) %0, [0 x i8]* noalias nocapture noundef nonnull readonly align 1 %1, i64 %2) unnamed_addr #1 !dbg !75467 {
  %4 = load %2*, %2** %0, align 8, !dbg !75468, !nonnull !23, !align !618, !noundef !23
  tail call void @llvm.experimental.noalias.scope.decl(metadata !75469), !dbg !75468
  tail call void @llvm.experimental.noalias.scope.decl(metadata !75472), !dbg !75475
  tail call void @llvm.experimental.noalias.scope.decl(metadata !75480), !dbg !75483
  tail call void @llvm.experimental.noalias.scope.decl(metadata !75485), !dbg !75488
  %5 = getelementptr inbounds %2, %2* %4, i64 0, i32 0, i32 1, !dbg !75490
  %6 = load i64, i64* %5, align 8, !dbg !75490, !alias.scope !75493, !noalias !75496
  %7 = getelementptr %2, %2* %4, i64 0, i32 0, i32 0, i32 1, !dbg !75499
  %8 = load i64, i64* %7, align 8, !dbg !75499, !alias.scope !75501, !noalias !75496
  %9 = sub i64 %8, %6, !dbg !75504
  %10 = icmp ult i64 %9, %2, !dbg !75507
  br i1 %10, label %11, label %14, !dbg !75499

11:                                               ; preds = %3
  %12 = getelementptr inbounds %2, %2* %4, i64 0, i32 0, i32 0, !dbg !75508
; call alloc::raw_vec::RawVec<T,A>::reserve::do_reserve_and_handle
  tail call fastcc void @"_ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$7reserve21do_reserve_and_handle17hb01a58fd396fed7eE"({ i8*, i64 }* noalias noundef nonnull align 8 dereferenceable(16) %12, i64 %6, i64 %2), !dbg !75509, !noalias !75496
  %13 = load i64, i64* %5, align 8, !dbg !75510, !alias.scope !75512, !noalias !75496
  br label %14, !dbg !75513

14:                                               ; preds = %11, %3
  %15 = phi i64 [ %6, %3 ], [ %13, %11 ]
  %16 = getelementptr [0 x i8], [0 x i8]* %1, i64 0, i64 0, !dbg !75514
  %17 = getelementptr inbounds %2, %2* %4, i64 0, i32 0, i32 0, i32 0, !dbg !75518
  %18 = load i8*, i8** %17, align 8, !dbg !75518, !alias.scope !75512, !noalias !75496
  %19 = getelementptr inbounds i8, i8* %18, i64 %15, !dbg !75519
  tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %19, i8* nonnull align 1 %16, i64 %2, i1 false), !dbg !75522, !noalias !75512
  %20 = add i64 %15, %2, !dbg !75524
  store i64 %20, i64* %5, align 8, !dbg !75524, !alias.scope !75512, !noalias !75496
  ret i1 false, !dbg !75525
}

define internal noundef zeroext i1 @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$10write_char17h0564e19f9542fbb8E"({ { { i8*, i64 }, i64 } }** noalias nocapture noundef readonly align 8 dereferenceable(8) %0, i32 noundef %1) unnamed_addr #1 !dbg !75526 {
  %3 = load { { { i8*, i64 }, i64 } }*, { { { i8*, i64 }, i64 } }** %0, align 8, !dbg !75527, !nonnull !23, !align !618, !noundef !23
; call alloc::string::String::push.29
  tail call fastcc void @_ZN5alloc6string6String4push17ha636c33b8036b8eeE.29({ { { i8*, i64 }, i64 } }* noalias noundef nonnull align 8 dereferenceable(24) %3, i32 noundef %1), !dbg !75528
  ret i1 false, !dbg !75531
}

; core::fmt::write
define internal noundef zeroext i1 @_ZN4core3fmt5write17hcd15d2c673b5a9c1E({}* noundef nonnull align 1 %0, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24) %1, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* noalias nocapture noundef readonly dereferenceable(48) %2) unnamed_addr #1 personality i32 (...)* bitcast (i32 (i32, i32, i64, %693*, %694*)* @rust_eh_personality to i32 (...)*) !dbg !80722 {
  %4 = alloca { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, align 8
  %5 = bitcast { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4 to i8*, !dbg !80723
  call void @llvm.lifetime.start.p0i8(i64 64, i8* nonnull %5), !dbg !80723
  %6 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 3, !dbg !80724
  store i32 0, i32* %6, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %7 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 4, !dbg !80724
  store i32 32, i32* %7, align 4, !dbg !80724, !alias.scope !80727, !noalias !80730
  %8 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 5, !dbg !80724
  store i8 3, i8* %8, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %9 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 0, i32 0, !dbg !80724
  store i64 0, i64* %9, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %10 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 1, i32 0, !dbg !80724
  store i64 0, i64* %10, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %11 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 2, i32 0, !dbg !80724
  store {}* %0, {}** %11, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %12 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 2, i32 1, !dbg !80724
  store [3 x i64]* %1, [3 x i64]** %12, align 8, !dbg !80724, !alias.scope !80727, !noalias !80730
  %13 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 1, !dbg !80732
  %14 = bitcast { i64*, i64 }* %13 to {}**
  %15 = load {}*, {}** %14, align 8, !dbg !80732
  %16 = icmp eq {}* %15, null, !dbg !80732
  br i1 %16, label %17, label %31, !dbg !80735

17:                                               ; preds = %3
  %18 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 2, i32 1, !dbg !80736
  %19 = load i64, i64* %18, align 8, !dbg !80736
  %20 = icmp eq i64 %19, 0, !dbg !80737
  br i1 %20, label %120, label %21, !dbg !80737

21:                                               ; preds = %17
  %22 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 2, i32 0, !dbg !80736
  %23 = bitcast [0 x { i8*, i64* }]** %22 to i64**, !dbg !80736
  %24 = load i64*, i64** %23, align 8, !dbg !80736, !nonnull !23, !align !618
  %25 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2 to { [0 x i8]*, i64 }**
  %26 = load { [0 x i8]*, i64 }*, { [0 x i8]*, i64 }** %25, align 8, !nonnull !23, !align !618
  %27 = bitcast [3 x i64]** %12 to i1 ({}*, [0 x i8]*, i64)***
  %28 = add i64 %19, 1152921504606846975, !dbg !80737
  %29 = and i64 %28, 1152921504606846975, !dbg !80737
  %30 = add nuw nsw i64 %29, 1, !dbg !80737
  br label %130, !dbg !80737

31:                                               ; preds = %3
  %32 = bitcast {}* %15 to [0 x %402]*, !dbg !80735
  %33 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 1, i32 1, !dbg !80744
  %34 = load i64, i64* %33, align 8, !dbg !80744
  %35 = getelementptr inbounds [0 x %402], [0 x %402]* %32, i64 0, i64 %34, i32 0, !dbg !80745
  %36 = icmp eq i64 %34, 0, !dbg !80755
  br i1 %36, label %120, label %37, !dbg !80755

37:                                               ; preds = %31
  %38 = bitcast {}* %15 to i64*, !dbg !80762
  %39 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2 to { [0 x i8]*, i64 }**
  %40 = load { [0 x i8]*, i64 }*, { [0 x i8]*, i64 }** %39, align 8, !nonnull !23, !align !618
  %41 = bitcast [3 x i64]** %12 to i1 ({}*, [0 x i8]*, i64)***
  %42 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 2, i32 0
  %43 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 0, i32 1
  %44 = getelementptr inbounds { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* %4, i64 0, i32 1, i32 1
  br label %45, !dbg !80755

45:                                               ; preds = %118, %37
  %46 = phi i64 [ 0, %37 ], [ %49, %118 ]
  %47 = phi i64* [ %38, %37 ], [ %48, %118 ]
  %48 = getelementptr inbounds i64, i64* %47, i64 7, !dbg !80767
  %49 = add nuw nsw i64 %46, 1, !dbg !80776
  %50 = bitcast i64* %47 to %402*, !dbg !80779
  %51 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %40, i64 %46, i32 1, !dbg !80780
  %52 = load i64, i64* %51, align 8, !dbg !80780
  %53 = icmp eq i64 %52, 0, !dbg !80781
  br i1 %53, label %54, label %110, !dbg !80784

54:                                               ; preds = %110, %45
  %55 = load [0 x { i8*, i64* }]*, [0 x { i8*, i64* }]** %42, align 8, !dbg !80785, !nonnull !23, !align !618, !noundef !23
  call void @llvm.experimental.noalias.scope.decl(metadata !80787), !dbg !80790
  call void @llvm.experimental.noalias.scope.decl(metadata !80791), !dbg !80790
  call void @llvm.experimental.noalias.scope.decl(metadata !80793), !dbg !80790
  %56 = getelementptr inbounds i64, i64* %47, i64 5, !dbg !80795
  %57 = bitcast i64* %56 to i32*, !dbg !80795
  %58 = load i32, i32* %57, align 8, !dbg !80795, !range !76407, !alias.scope !80791, !noalias !80798, !noundef !23
  store i32 %58, i32* %7, align 4, !dbg !80799, !alias.scope !80787, !noalias !80800
  %59 = getelementptr inbounds i64, i64* %47, i64 6, !dbg !80801
  %60 = bitcast i64* %59 to i8*, !dbg !80801
  %61 = load i8, i8* %60, align 8, !dbg !80801, !range !6597, !alias.scope !80791, !noalias !80798, !noundef !23
  store i8 %61, i8* %8, align 8, !dbg !80802, !alias.scope !80787, !noalias !80800
  %62 = getelementptr inbounds %402, %402* %50, i64 0, i32 1, i32 3, !dbg !80803
  %63 = load i32, i32* %62, align 4, !dbg !80803, !alias.scope !80791, !noalias !80798
  store i32 %63, i32* %6, align 8, !dbg !80804, !alias.scope !80787, !noalias !80800
  %64 = getelementptr inbounds i64, i64* %47, i64 3, !dbg !80805
  %65 = load i64, i64* %64, align 8, !dbg !80805, !alias.scope !80791, !noalias !80798
  %66 = getelementptr i64, i64* %47, i64 4, !dbg !80805
  %67 = load i64, i64* %66, align 8, !dbg !80805, !alias.scope !80791, !noalias !80798
  call void @llvm.experimental.noalias.scope.decl(metadata !80807), !dbg !80805
  switch i64 %65, label %68 [
    i64 0, label %69
    i64 1, label %70
    i64 2, label %80
  ], !dbg !80810

68:                                               ; preds = %54
  unreachable, !dbg !80813

69:                                               ; preds = %54
  br label %80, !dbg !80814

70:                                               ; preds = %54
  call void @llvm.experimental.noalias.scope.decl(metadata !80815) #51, !dbg !80818
  %71 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %67, i32 1, !dbg !80821
  %72 = bitcast i64** %71 to i1 ({}*, %4*)**, !dbg !80821
  %73 = load i1 ({}*, %4*)*, i1 ({}*, %4*)** %72, align 8, !dbg !80821, !alias.scope !80824, !noalias !80825, !nonnull !23, !noundef !23
  %74 = icmp eq i1 ({}*, %4*)* %73, bitcast (i1 (i64*, %4*)* @_ZN4core3ops8function6FnOnce9call_once17h98aff63a4f5d8237E to i1 ({}*, %4*)*), !dbg !80821
  br i1 %74, label %75, label %80, !dbg !80821

75:                                               ; preds = %70
  %76 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %67, !dbg !80826
  %77 = bitcast { i8*, i64* }* %76 to i64**, !dbg !80840
  %78 = load i64*, i64** %77, align 8, !dbg !80840, !alias.scope !80824, !noalias !80825, !nonnull !23, !align !2195
  %79 = load i64, i64* %78, align 8, !dbg !80842, !noalias !80843
  br label %80, !dbg !80844

80:                                               ; preds = %75, %70, %69, %54
  %81 = phi i64 [ %67, %69 ], [ poison, %54 ], [ %79, %75 ], [ poison, %70 ]
  %82 = phi i64 [ 1, %69 ], [ 0, %54 ], [ 1, %75 ], [ 0, %70 ]
  store i64 %82, i64* %9, align 8, !dbg !80846, !alias.scope !80787, !noalias !80800
  store i64 %81, i64* %43, align 8, !dbg !80846, !alias.scope !80787, !noalias !80800
  %83 = getelementptr inbounds i64, i64* %47, i64 1, !dbg !80847
  %84 = load i64, i64* %83, align 8, !dbg !80847, !alias.scope !80791, !noalias !80798
  %85 = getelementptr i64, i64* %47, i64 2, !dbg !80847
  %86 = load i64, i64* %85, align 8, !dbg !80847, !alias.scope !80791, !noalias !80798
  call void @llvm.experimental.noalias.scope.decl(metadata !80848), !dbg !80847
  switch i64 %84, label %87 [
    i64 0, label %88
    i64 1, label %89
    i64 2, label %99
  ], !dbg !80851

87:                                               ; preds = %80
  unreachable, !dbg !80853

88:                                               ; preds = %80
  br label %99, !dbg !80854

89:                                               ; preds = %80
  call void @llvm.experimental.noalias.scope.decl(metadata !80855) #51, !dbg !80858
  %90 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %86, i32 1, !dbg !80859
  %91 = bitcast i64** %90 to i1 ({}*, %4*)**, !dbg !80859
  %92 = load i1 ({}*, %4*)*, i1 ({}*, %4*)** %91, align 8, !dbg !80859, !alias.scope !80861, !noalias !80825, !nonnull !23, !noundef !23
  %93 = icmp eq i1 ({}*, %4*)* %92, bitcast (i1 (i64*, %4*)* @_ZN4core3ops8function6FnOnce9call_once17h98aff63a4f5d8237E to i1 ({}*, %4*)*), !dbg !80859
  br i1 %93, label %94, label %99, !dbg !80859

94:                                               ; preds = %89
  %95 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %86, !dbg !80862
  %96 = bitcast { i8*, i64* }* %95 to i64**, !dbg !80867
  %97 = load i64*, i64** %96, align 8, !dbg !80867, !alias.scope !80861, !noalias !80825, !nonnull !23, !align !2195
  %98 = load i64, i64* %97, align 8, !dbg !80868, !noalias !80869
  br label %99, !dbg !80870

99:                                               ; preds = %94, %89, %88, %80
  %100 = phi i64 [ %86, %88 ], [ poison, %80 ], [ %98, %94 ], [ poison, %89 ]
  %101 = phi i64 [ 1, %88 ], [ 0, %80 ], [ 1, %94 ], [ 0, %89 ]
  store i64 %101, i64* %10, align 8, !dbg !80872, !alias.scope !80787, !noalias !80800
  store i64 %100, i64* %44, align 8, !dbg !80872, !alias.scope !80787, !noalias !80800
  %102 = load i64, i64* %47, align 8, !dbg !80873, !alias.scope !80791, !noalias !80798
  %103 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %102, !dbg !80875
  %104 = getelementptr inbounds [0 x { i8*, i64* }], [0 x { i8*, i64* }]* %55, i64 0, i64 %102, i32 1, !dbg !80889
  %105 = bitcast i64** %104 to i1 ({}*, %4*)**, !dbg !80889
  %106 = load i1 ({}*, %4*)*, i1 ({}*, %4*)** %105, align 8, !dbg !80889, !alias.scope !80793, !noalias !80825, !nonnull !23, !noundef !23
  %107 = bitcast { i8*, i64* }* %103 to {}**, !dbg !80891
  %108 = load {}*, {}** %107, align 8, !dbg !80891, !alias.scope !80793, !noalias !80825, !nonnull !23, !align !2195, !noundef !23
  %109 = call noundef zeroext i1 %106({}* noundef nonnull align 1 %108, %4* noalias noundef nonnull align 8 dereferenceable(64) %4), !dbg !80889, !noalias !80800
  br i1 %109, label %155, label %118, !dbg !80892

110:                                              ; preds = %45
  %111 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %40, i64 %46, i32 0, !dbg !80780
  %112 = load {}*, {}** %11, align 8, !dbg !80893, !nonnull !23, !align !2195, !noundef !23
  %113 = load i1 ({}*, [0 x i8]*, i64)**, i1 ({}*, [0 x i8]*, i64)*** %41, align 8, !dbg !80893, !nonnull !23, !align !618
  %114 = load [0 x i8]*, [0 x i8]** %111, align 8, !dbg !80894, !nonnull !23, !align !2195, !noundef !23
  %115 = getelementptr inbounds i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %113, i64 3, !dbg !80893
  %116 = load i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %115, align 8, !dbg !80893, !invariant.load !23, !nonnull !23
  %117 = call noundef zeroext i1 %116({}* noundef nonnull align 1 %112, [0 x i8]* noalias noundef nonnull readonly align 1 %114, i64 %52), !dbg !80893
  br i1 %117, label %155, label %54, !dbg !80893

118:                                              ; preds = %99
  %119 = icmp eq i64* %35, %48, !dbg !80755
  br i1 %119, label %120, label %45, !dbg !80755

120:                                              ; preds = %153, %118, %31, %17
  %121 = phi i64 [ 0, %17 ], [ 0, %31 ], [ %30, %153 ], [ %49, %118 ]
  %122 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 0, i32 0, !dbg !80896
  %123 = load [0 x { [0 x i8]*, i64 }]*, [0 x { [0 x i8]*, i64 }]** %122, align 8, !dbg !80896, !nonnull !23, !align !618, !noundef !23
  %124 = getelementptr inbounds { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %2, i64 0, i32 0, i32 1, !dbg !80896
  %125 = load i64, i64* %124, align 8, !dbg !80896
  %126 = icmp ult i64 %121, %125, !dbg !80898
  %127 = getelementptr inbounds [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %123, i64 0, i64 %121, !dbg !80898
  %128 = bitcast { [0 x i8]*, i64 }* %127 to i64*, !dbg !80898
  %129 = select i1 %126, i64* %128, i64* null, !dbg !80898
  br i1 %126, label %156, label %167, !dbg !80903

130:                                              ; preds = %153, %21
  %131 = phi i64 [ 0, %21 ], [ %134, %153 ]
  %132 = phi i64* [ %24, %21 ], [ %133, %153 ]
  %133 = getelementptr inbounds i64, i64* %132, i64 2, !dbg !80904
  %134 = add nuw nsw i64 %131, 1, !dbg !80913
  %135 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %26, i64 %131, i32 1, !dbg !80916
  %136 = load i64, i64* %135, align 8, !dbg !80916
  %137 = icmp eq i64 %136, 0, !dbg !80917
  br i1 %137, label %138, label %145, !dbg !80920

138:                                              ; preds = %145, %130
  %139 = getelementptr inbounds i64, i64* %132, i64 1, !dbg !80921
  %140 = bitcast i64* %139 to i1 ({}*, %4*)**, !dbg !80921
  %141 = load i1 ({}*, %4*)*, i1 ({}*, %4*)** %140, align 8, !dbg !80921, !nonnull !23, !noundef !23
  %142 = bitcast i64* %132 to {}**, !dbg !80922
  %143 = load {}*, {}** %142, align 8, !dbg !80922, !nonnull !23, !align !2195, !noundef !23
  %144 = call noundef zeroext i1 %141({}* noundef nonnull align 1 %143, { { i64, i64 }, { i64, i64 }, { {}*, [3 x i64]* }, i32, i32, i8, [7 x i8] }* noalias noundef nonnull align 8 dereferenceable(64) %4), !dbg !80921
  call void @llvm.vellvm.internal.throw()
  br i1 %144, label %155, label %153, !dbg !80921

145:                                              ; preds = %130
  %146 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %26, i64 %131, i32 0, !dbg !80916
  %147 = load {}*, {}** %11, align 8, !dbg !80923, !nonnull !23, !align !2195, !noundef !23
  %148 = load i1 ({}*, [0 x i8]*, i64)**, i1 ({}*, [0 x i8]*, i64)*** %27, align 8, !dbg !80923, !nonnull !23, !align !618
  %149 = load [0 x i8]*, [0 x i8]** %146, align 8, !dbg !80924, !nonnull !23, !align !2195, !noundef !23
  %150 = getelementptr inbounds i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %148, i64 3, !dbg !80923
  %151 = load i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %150, align 8, !dbg !80923, !invariant.load !23, !nonnull !23
  %152 = call noundef zeroext i1 %151({}* noundef nonnull align 1 %147, [0 x i8]* noalias noundef nonnull readonly align 1 %149, i64 %136), !dbg !80923
  br i1 %152, label %155, label %138, !dbg !80923

153:                                              ; preds = %138
  %154 = icmp eq i64 %131, %29, !dbg !80737
  br i1 %154, label %120, label %130, !dbg !80737

155:                                              ; preds = %156, %145, %138, %110, %99
  call void @llvm.lifetime.end.p0i8(i64 64, i8* nonnull %5), !dbg !80925
  br label %168, !dbg !80926

156:                                              ; preds = %120
  %157 = load {}*, {}** %11, align 8, !dbg !80927, !nonnull !23, !align !2195, !noundef !23
  %158 = bitcast [3 x i64]** %12 to i1 ({}*, [0 x i8]*, i64)***, !dbg !80927
  %159 = load i1 ({}*, [0 x i8]*, i64)**, i1 ({}*, [0 x i8]*, i64)*** %158, align 8, !dbg !80927, !nonnull !23, !align !618
  %160 = bitcast i64* %129 to [0 x i8]**, !dbg !80928
  %161 = load [0 x i8]*, [0 x i8]** %160, align 8, !dbg !80928, !nonnull !23, !align !2195, !noundef !23
  %162 = getelementptr inbounds i64, i64* %129, i64 1, !dbg !80928
  %163 = load i64, i64* %162, align 8, !dbg !80928
  %164 = getelementptr inbounds i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %159, i64 3, !dbg !80927
  %165 = load i1 ({}*, [0 x i8]*, i64)*, i1 ({}*, [0 x i8]*, i64)** %164, align 8, !dbg !80927, !invariant.load !23, !nonnull !23
  %166 = call noundef zeroext i1 %165({}* noundef nonnull align 1 %157, [0 x i8]* noalias noundef nonnull readonly align 1 %161, i64 %163), !dbg !80927
  br i1 %166, label %155, label %167, !dbg !80927

167:                                              ; preds = %156, %120
  call void @llvm.lifetime.end.p0i8(i64 64, i8* nonnull %5), !dbg !80925
  br label %168, !dbg !80926

168:                                              ; preds = %167, %155
  %169 = phi i1 [ true, %155 ], [ false, %167 ]
  ret i1 %169, !dbg !80926
}

; <&mut W as core::fmt::Write>::write_fmt
; Function Attrs: nonlazybind uwtable
define internal noundef zeroext i1 @"_ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_fmt17hc11cd155d0861a3cE"({ { { i8*, i64 }, i64 } }** noalias nocapture noundef readonly align 8 dereferenceable(8) %0, %13* noalias nocapture noundef readonly dereferenceable(48) %1) unnamed_addr #1 !dbg !75532 {
  %3 = alloca { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, align 8
  %4 = alloca { { { i8*, i64 }, i64 } }*, align 8
  %5 = load { { { i8*, i64 }, i64 } }*, { { { i8*, i64 }, i64 } }** %0, align 8, !dbg !75533, !nonnull !23, !align !618, !noundef !23
  %6 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %1 to i8*, !dbg !75534
  %7 = bitcast { { { i8*, i64 }, i64 } }** %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %7)
  store { { { i8*, i64 }, i64 } }* %5, { { { i8*, i64 }, i64 } }** %4, align 8, !noalias !75535
  %8 = bitcast { { { i8*, i64 }, i64 } }** %4 to {}*, !dbg !75539
  %9 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %3 to i8*, !dbg !75541
  call void @llvm.lifetime.start.p0i8(i64 48, i8* nonnull %9), !dbg !75541, !noalias !75535
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* noundef nonnull align 8 dereferenceable(48) %9, i8* noundef nonnull align 8 dereferenceable(48) %6, i64 48, i1 false), !dbg !75541
; call core::fmt::write
  %10 = call noundef zeroext i1 @_ZN4core3fmt5write17hcd15d2c673b5a9c1E({}* noundef nonnull align 1 %8, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24) bitcast (<{ i8*, [16 x i8], i8*, i8*, i8* }>* @anon.cb3a820676433a993734d74257001914.1 to [3 x i64]*), { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* noalias nocapture noundef nonnull dereferenceable(48) %3), !dbg !75542, !noalias !75543
  call void @llvm.lifetime.end.p0i8(i64 48, i8* nonnull %9), !dbg !75544, !noalias !75535
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %7), !dbg !75545
  ret i1 %10, !dbg !75546
}

define internal void @_ZN5alloc3fmt6format12format_inner17h840d5de64fab0778E({ { { i8*, i64 }, i64 } }* noalias nocapture noundef sret({ { { i8*, i64 }, i64 } }) dereferenceable(24) %0, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* noalias nocapture noundef readonly dereferenceable(48) %1) unnamed_addr #1 personality i32 (...)* bitcast (i32 (i32, i32, i64, %693*, %694*)* @rust_eh_personality to i32 (...)*) !dbg !75337 {
  %3 = alloca {}, align 1
  %4 = alloca { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, align 8
  %5 = alloca { { { i8*, i64 }, i64 } }*, align 8
  %6 = getelementptr { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %1, i64 0, i32 0, i32 0, !dbg !75338
  %7 = load [0 x { [0 x i8]*, i64 }]*, [0 x { [0 x i8]*, i64 }]** %6, align 8, !dbg !75338, !nonnull !23
  %8 = getelementptr { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %1, i64 0, i32 0, i32 1, !dbg !75338
  %9 = load i64, i64* %8, align 8, !dbg !75338
  %10 = getelementptr { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }, { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %1, i64 0, i32 2, i32 1, !dbg !75338
  %11 = load i64, i64* %10, align 8, !dbg !75338
  %12 = getelementptr inbounds [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %7, i64 0, i64 %9, !dbg !75339
  %13 = bitcast { [0 x i8]*, i64 }* %12 to i64*, !dbg !75356
  %14 = bitcast { [0 x i8]*, i64 }* %12 to [0 x { [0 x i8]*, i64 }]*, !dbg !75358
  %15 = icmp eq [0 x { [0 x i8]*, i64 }]* %7, %14, !dbg !75358
  br i1 %15, label %62, label %16, !dbg !75358

16:                                               ; preds = %2
  %17 = bitcast [0 x { [0 x i8]*, i64 }]* %7 to i64*, !dbg !75372
  %18 = add i64 %9, 1152921504606846975, !dbg !75358
  %19 = and i64 %18, 1152921504606846975, !dbg !75358
  %20 = add nuw nsw i64 %19, 1, !dbg !75358
  %21 = icmp ult i64 %19, 4, !dbg !75358
  br i1 %21, label %51, label %22, !dbg !75358

22:                                               ; preds = %16
  %23 = and i64 %20, 3, !dbg !75358
  %24 = icmp eq i64 %23, 0, !dbg !75358
  %25 = select i1 %24, i64 4, i64 %23, !dbg !75358
  %26 = sub nsw i64 %20, %25, !dbg !75358
  %27 = getelementptr [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %7, i64 0, i64 %26, !dbg !75358
  %28 = bitcast { [0 x i8]*, i64 }* %27 to i64*, !dbg !75358
  %29 = getelementptr [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %7, i64 0, i64 0, i32 1
  br label %30, !dbg !75358

30:                                               ; preds = %30, %22
  %31 = phi i64 [ 0, %22 ], [ %46, %30 ]
  %32 = phi <2 x i64> [ zeroinitializer, %22 ], [ %44, %30 ]
  %33 = phi <2 x i64> [ zeroinitializer, %22 ], [ %45, %30 ]
  %34 = shl i64 %31, 1
  %35 = or i64 %34, 4
  %36 = getelementptr [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %7, i64 0, i64 %31, i32 1, !dbg !75377
  %37 = getelementptr i64, i64* %29, i64 %35, !dbg !75377
  %38 = bitcast i64* %36 to <4 x i64>*, !dbg !75377
  %39 = bitcast i64* %37 to <4 x i64>*, !dbg !75377
  %40 = load <4 x i64>, <4 x i64>* %38, align 8, !dbg !75377
  %41 = load <4 x i64>, <4 x i64>* %39, align 8, !dbg !75377
  %42 = shufflevector <4 x i64> %40, <4 x i64> poison, <2 x i32> <i32 0, i32 2>, !dbg !75377
  %43 = shufflevector <4 x i64> %41, <4 x i64> poison, <2 x i32> <i32 0, i32 2>, !dbg !75377
  %44 = add <2 x i64> %42, %32, !dbg !75378
  %45 = add <2 x i64> %43, %33, !dbg !75378
  %46 = add nuw i64 %31, 4
  %47 = icmp eq i64 %46, %26
  br i1 %47, label %48, label %30, !llvm.loop !75383

48:                                               ; preds = %30
  %49 = add <2 x i64> %45, %44, !dbg !75358
  %50 = call i64 @llvm.vector.reduce.add.v2i64(<2 x i64> %49), !dbg !75358
  br label %51, !dbg !75358

51:                                               ; preds = %48, %16
  %52 = phi i64 [ 0, %16 ], [ %50, %48 ]
  %53 = phi i64* [ %17, %16 ], [ %28, %48 ]
  br label %54, !dbg !75358

54:                                               ; preds = %54, %51
  %55 = phi i64 [ %60, %54 ], [ %52, %51 ]
  %56 = phi i64* [ %57, %54 ], [ %53, %51 ]
  %57 = getelementptr inbounds i64, i64* %56, i64 2, !dbg !75384
  %58 = getelementptr i64, i64* %56, i64 1, !dbg !75377
  %59 = load i64, i64* %58, align 8, !dbg !75377
  %60 = add i64 %59, %55, !dbg !75378
  %61 = icmp eq i64* %57, %13, !dbg !75358
  br i1 %61, label %62, label %54, !dbg !75358, !llvm.loop !75393

62:                                               ; preds = %54, %2
  %63 = phi i64 [ 0, %2 ], [ %60, %54 ]
  %64 = icmp eq i64 %11, 0, !dbg !75395
  br i1 %64, label %77, label %65, !dbg !75395

65:                                               ; preds = %62
  %66 = icmp eq i64 %9, 0, !dbg !75397
  br i1 %66, label %73, label %67, !dbg !75401

67:                                               ; preds = %65
  %68 = getelementptr inbounds [0 x { [0 x i8]*, i64 }], [0 x { [0 x i8]*, i64 }]* %7, i64 0, i64 0, i32 1, !dbg !75402
  %69 = load i64, i64* %68, align 8, !dbg !75402
  %70 = icmp eq i64 %69, 0, !dbg !75403
  %71 = icmp ult i64 %63, 16
  %72 = select i1 %70, i1 %71, i1 false, !dbg !75401
  br i1 %72, label %89, label %73, !dbg !75401

73:                                               ; preds = %67, %65
  %74 = tail call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %63, i64 2) #51, !dbg !75407
  %75 = extractvalue { i64, i1 } %74, 1, !dbg !75407
  %76 = extractvalue { i64, i1 } %74, 0, !dbg !75407
  br i1 %75, label %89, label %77, !dbg !75412

77:                                               ; preds = %73, %62
  %78 = phi i64 [ %63, %62 ], [ %76, %73 ]
  %79 = icmp eq i64 %78, 0, !dbg !75413
  br i1 %79, label %89, label %80, !dbg !75425

80:                                               ; preds = %77
  %81 = xor i64 %78, -1, !dbg !75426
  %82 = lshr i64 %81, 63, !dbg !75426
  %83 = icmp slt i64 %78, 0, !dbg !75429
  br i1 %83, label %84, label %85, !dbg !75430

84:                                               ; preds = %80
; call alloc::raw_vec::capacity_overflow
  tail call void @_ZN5alloc7raw_vec17capacity_overflow17hc80d63a780181a5dE() #64, !dbg !75431
  unreachable

85:                                               ; preds = %80
  %86 = tail call i8* @__rust_alloc(i64 %78, i64 %82) #51, !dbg !75432
  %87 = icmp eq i8* %86, null, !dbg !75436
  br i1 %87, label %88, label %89, !dbg !75437

88:                                               ; preds = %85
; call alloc::alloc::handle_alloc_error
  tail call void @_ZN5alloc5alloc18handle_alloc_error17h0eb7a9e63f5042c6E(i64 %78, i64 noundef %82) #64, !dbg !75438
  unreachable

89:                                               ; preds = %85, %77, %73, %67
  %90 = phi i64 [ %78, %85 ], [ 0, %77 ], [ 0, %67 ], [ 0, %73 ]
  %91 = phi i8* [ %86, %85 ], [ inttoptr (i64 1 to i8*), %77 ], [ inttoptr (i64 1 to i8*), %67 ], [ inttoptr (i64 1 to i8*), %73 ]
  %92 = getelementptr inbounds { { { i8*, i64 }, i64 } }, { { { i8*, i64 }, i64 } }* %0, i64 0, i32 0, i32 0, i32 0, !dbg !75440
  store i8* %91, i8** %92, align 8, !dbg !75440
  %93 = getelementptr inbounds { { { i8*, i64 }, i64 } }, { { { i8*, i64 }, i64 } }* %0, i64 0, i32 0, i32 0, i32 1, !dbg !75440
  store i64 %90, i64* %93, align 8, !dbg !75440
  %94 = getelementptr inbounds { { { i8*, i64 }, i64 } }, { { { i8*, i64 }, i64 } }* %0, i64 0, i32 0, i32 1, !dbg !75440
  store i64 0, i64* %94, align 8, !dbg !75440
  %95 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %1 to i8*, !dbg !75442
  %96 = bitcast { { { i8*, i64 }, i64 } }** %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %96)
  store { { { i8*, i64 }, i64 } }* %0, { { { i8*, i64 }, i64 } }** %5, align 8, !noalias !75444
  %97 = bitcast { { { i8*, i64 }, i64 } }** %5 to {}*, !dbg !75448
  %98 = bitcast { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* %4 to i8*, !dbg !75451
  call void @llvm.lifetime.start.p0i8(i64 48, i8* nonnull %98), !dbg !75451, !noalias !75444
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* noundef nonnull align 8 dereferenceable(48) %98, i8* noundef nonnull align 8 dereferenceable(48) %95, i64 48, i1 false), !dbg !75451
; invoke core::fmt::write
  %99 = invoke noundef zeroext i1 @_ZN4core3fmt5write17hcd15d2c673b5a9c1E({}* noundef nonnull align 1 %97, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24) bitcast (<{ i8*, [16 x i8], i8*, i8*, i8* }>* @anon.cb3a820676433a993734d74257001914.1 to [3 x i64]*), { { [0 x { [0 x i8]*, i64 }]*, i64 }, { i64*, i64 }, { [0 x { i8*, i64* }]*, i64 } }* noalias nocapture noundef nonnull dereferenceable(48) %4)
          to label %102 unwind label %100, !dbg !75452

100:                                              ; preds = %104, %89
  %101 = landingpad { i8*, i32 }
          cleanup
; call core::ptr::drop_in_place<alloc::string::String>
  call fastcc void @"_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h7976e5c0f47f4c12E"({ { { i8*, i64 }, i64 } }* nonnull %0) #65, !dbg !75453
  resume { i8*, i32 } %101, !dbg !75454

102:                                              ; preds = %89
  call void @llvm.lifetime.end.p0i8(i64 48, i8* nonnull %98), !dbg !75455, !noalias !75444
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %96), !dbg !75456
  %103 = bitcast %330* %3 to i8*, !dbg !75457
  call void @llvm.lifetime.start.p0i8(i64 0, i8* nonnull %103), !dbg !75457
  br i1 %99, label %104, label %107, !dbg !75457

104:                                              ; preds = %102
  %105 = bitcast %330* %3 to {}*, !dbg !75460
; invoke core::result::unwrap_failed
  invoke void @_ZN4core6result13unwrap_failed17hff48f82f03d418aeE([0 x i8]* noalias noundef nonnull readonly align 1 bitcast (<{ [51 x i8] }>* @anon.cb3a820676433a993734d74257001914.32 to [0 x i8]*), i64 51, {}* noundef nonnull align 1 %105, [3 x i64]* noalias noundef readonly align 8 dereferenceable(24) bitcast (<{ i8*, [16 x i8], i8* }>* @anon.cb3a820676433a993734d74257001914.4 to [3 x i64]*), %73* noalias noundef readonly align 8 dereferenceable(24) bitcast (<{ i8*, [16 x i8] }>* @anon.cb3a820676433a993734d74257001914.34 to %73*)) #64
          to label %106 unwind label %100, !dbg !75462

106:                                              ; preds = %104
  unreachable

107:                                              ; preds = %102
  call void @llvm.lifetime.end.p0i8(i64 0, i8* nonnull %103), !dbg !75463
  ret void, !dbg !75464
}

; define internal void @_ZN5alloc3fmt6format12format_inner17h840d5de64fab0778E(ptr noalias nocapture noundef sret(%6) dereferenceable(24) %0, ptr noalias nocapture noundef readonly dereferenceable(48) %1) unnamed_addr #6 personality ptr @rust_eh_personality {
;   %3 = alloca %47, align 1
;   call void @llvm.vellvm.internal.throw()
;   %4 = alloca %2, align 8
;   %5 = alloca ptr, align 8
;   %6 = getelementptr %2, ptr %1, i64 0, i32 0, i32 0
;   %7 = load ptr, ptr %6, align 8, !nonnull !94
;   %8 = getelementptr %2, ptr %1, i64 0, i32 0, i32 1
;   %9 = load i64, ptr %8, align 8
;   %10 = getelementptr %2, ptr %1, i64 0, i32 2, i32 1
;   %11 = load i64, ptr %10, align 8
;   %12 = getelementptr inbounds [0 x { ptr, i64 }], ptr %7, i64 0, i64 %9
;   %13 = bitcast ptr %12 to ptr
;   %14 = bitcast ptr %12 to ptr
;   %15 = icmp eq ptr %7, %14
;   br i1 %15, label %62, label %16

; 16:                                               ; preds = %2
;   %17 = bitcast ptr %7 to ptr
;   %18 = add i64 %9, 1152921504606846975
;   %19 = and i64 %18, 1152921504606846975
;   %20 = add nuw nsw i64 %19, 1
;   %21 = icmp ult i64 %19, 4
;   br i1 %21, label %51, label %22

; 22:                                               ; preds = %16
;   %23 = and i64 %20, 3
;   %24 = icmp eq i64 %23, 0
;   %25 = select i1 %24, i64 4, i64 %23
;   %26 = sub nsw i64 %20, %25
;   %27 = getelementptr [0 x { ptr, i64 }], ptr %7, i64 0, i64 %26
;   %28 = bitcast ptr %27 to ptr
;   %29 = getelementptr [0 x { ptr, i64 }], ptr %7, i64 0, i64 0, i32 1
;   br label %30

; 30:                                               ; preds = %30, %22
;   %31 = phi i64 [ 0, %22 ], [ %46, %30 ]
;   %32 = phi <2 x i64> [ zeroinitializer, %22 ], [ %44, %30 ]
;   %33 = phi <2 x i64> [ zeroinitializer, %22 ], [ %45, %30 ]
;   %34 = shl i64 %31, 1
;   %35 = or i64 %34, 4
;   %36 = getelementptr [0 x { ptr, i64 }], ptr %7, i64 0, i64 %31, i32 1
;   %37 = getelementptr i64, ptr %29, i64 %35
;   %38 = bitcast ptr %36 to ptr
;   %39 = bitcast ptr %37 to ptr
;   %40 = load <4 x i64>, ptr %38, align 8
;   %41 = load <4 x i64>, ptr %39, align 8
;   %42 = shufflevector <4 x i64> %40, <4 x i64> poison, <2 x i32> <i32 0, i32 2>
;   %43 = shufflevector <4 x i64> %41, <4 x i64> poison, <2 x i32> <i32 0, i32 2>
;   %44 = add <2 x i64> %42, %32
;   %45 = add <2 x i64> %43, %33
;   %46 = add nuw i64 %31, 4
;   %47 = icmp eq i64 %46, %26
;   br i1 %47, label %48, label %30, !llvm.loop !17779

; 48:                                               ; preds = %30
;   %49 = add <2 x i64> %45, %44
;   %50 = call i64 @llvm.vector.reduce.add.v2i64(<2 x i64> %49)
;   br label %51

; 51:                                               ; preds = %48, %16
;   %52 = phi i64 [ 0, %16 ], [ %50, %48 ]
;   %53 = phi ptr [ %17, %16 ], [ %28, %48 ]
;   br label %54

; 54:                                               ; preds = %54, %51
;   %55 = phi i64 [ %60, %54 ], [ %52, %51 ]
;   %56 = phi ptr [ %57, %54 ], [ %53, %51 ]
;   %57 = getelementptr inbounds i64, ptr %56, i64 2
;   %58 = getelementptr i64, ptr %56, i64 1
;   %59 = load i64, ptr %58, align 8
;   %60 = add i64 %59, %55
;   %61 = icmp eq ptr %57, %13
;   br i1 %61, label %62, label %54, !llvm.loop !17780

; 62:                                               ; preds = %54, %2
;   %63 = phi i64 [ 0, %2 ], [ %60, %54 ]
;   %64 = icmp eq i64 %11, 0
;   br i1 %64, label %77, label %65

; 65:                                               ; preds = %62
;   %66 = icmp eq i64 %9, 0
;   br i1 %66, label %73, label %67

; 67:                                               ; preds = %65
;   %68 = getelementptr inbounds [0 x { ptr, i64 }], ptr %7, i64 0, i64 0, i32 1
;   %69 = load i64, ptr %68, align 8
;   %70 = icmp eq i64 %69, 0
;   %71 = icmp ult i64 %63, 16
;   %72 = select i1 %70, i1 %71, i1 false
;   br i1 %72, label %89, label %73

; 73:                                               ; preds = %67, %65
;   %74 = tail call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %63, i64 2) #47
;   %75 = extractvalue { i64, i1 } %74, 1
;   %76 = extractvalue { i64, i1 } %74, 0
;   br i1 %75, label %89, label %77

; 77:                                               ; preds = %73, %62
;   %78 = phi i64 [ %63, %62 ], [ %76, %73 ]
;   %79 = icmp eq i64 %78, 0
;   br i1 %79, label %89, label %80

; 80:                                               ; preds = %77
;   %81 = xor i64 %78, -1
;   %82 = lshr i64 %81, 63
;   %83 = icmp slt i64 %78, 0
;   br i1 %83, label %84, label %85

; 84:                                               ; preds = %80
;   tail call void @_ZN5alloc7raw_vec17capacity_overflow17hc80d63a780181a5dE() #57
;   unreachable

; 85:                                               ; preds = %80
;   %86 = tail call ptr @__rust_alloc(i64 %78, i64 %82) #47
;   %87 = icmp eq ptr %86, null
;   br i1 %87, label %88, label %89

; 88:                                               ; preds = %85
;   tail call void @_ZN5alloc5alloc18handle_alloc_error17h0eb7a9e63f5042c6E(i64 %78, i64 noundef %82) #57
;   unreachable

; 89:                                               ; preds = %85, %77, %73, %67
;   %90 = phi i64 [ %78, %85 ], [ 0, %77 ], [ 0, %67 ], [ 0, %73 ]
;   %91 = phi ptr [ %86, %85 ], [ inttoptr (i64 1 to ptr), %77 ], [ inttoptr (i64 1 to ptr), %67 ], [ inttoptr (i64 1 to ptr), %73 ]
;   %92 = getelementptr inbounds %6, ptr %0, i64 0, i32 0, i32 0, i32 0
;   store ptr %91, ptr %92, align 8
;   %93 = getelementptr inbounds %6, ptr %0, i64 0, i32 0, i32 0, i32 1
;   store i64 %90, ptr %93, align 8
;   %94 = getelementptr inbounds %6, ptr %0, i64 0, i32 0, i32 1
;   store i64 0, ptr %94, align 8
;   %95 = bitcast ptr %1 to ptr
;   %96 = bitcast ptr %5 to ptr
;   call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %96)
;   store ptr %0, ptr %5, align 8, !noalias !17781
;   %97 = bitcast ptr %5 to ptr
;   %98 = bitcast ptr %4 to ptr
;   call void @llvm.lifetime.start.p0(i64 48, ptr nonnull %98), !noalias !17781
;   call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(48) %98, ptr noundef nonnull align 8 dereferenceable(48) %95, i64 48, i1 false)
;   %99 = invoke noundef zeroext i1 @_ZN4core3fmt5write17hcd15d2c673b5a9c1E(ptr noundef nonnull align 1 %97, ptr noalias noundef readonly align 8 dereferenceable(24) @anon.cb3a820676433a993734d74257001914.1, ptr noalias nocapture noundef nonnull dereferenceable(48) %4)
;           to label %102 unwind label %100

; 100:                                              ; preds = %104, %89
;   %101 = landingpad { ptr, i32 }
;           cleanup
;   call fastcc void @"_ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h7976e5c0f47f4c12E"(ptr nonnull %0) #58
;   resume { ptr, i32 } %101

; 102:                                              ; preds = %89
;   call void @llvm.lifetime.end.p0(i64 48, ptr nonnull %98), !noalias !17781
;   call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %96)
;   %103 = bitcast ptr %3 to ptr
;   call void @llvm.lifetime.start.p0(i64 0, ptr nonnull %103)
;   br i1 %99, label %104, label %107

; 104:                                              ; preds = %102
;   %105 = bitcast ptr %3 to ptr
;   invoke void @_ZN4core6result13unwrap_failed17hff48f82f03d418aeE(ptr noalias noundef nonnull readonly align 1 @anon.cb3a820676433a993734d74257001914.32, i64 51, ptr noundef nonnull align 1 %105, ptr noalias noundef readonly align 8 dereferenceable(24) @anon.cb3a820676433a993734d74257001914.4, ptr noalias noundef readonly align 8 dereferenceable(24) @anon.cb3a820676433a993734d74257001914.34) #57
;           to label %106 unwind label %100

; 106:                                              ; preds = %104
;   unreachable

; 107:                                              ; preds = %102
;   call void @llvm.lifetime.end.p0(i64 0, ptr nonnull %103)
;   ret void
; }

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

define { i64, i1 } @llvm.usub.with.overflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %overflow = icmp ugt i64 %1, %0
  %res = sub i64 %0, %1
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %res, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define { i32, i1 } @llvm.usub.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %overflow = icmp ugt i32 %1, %0
  %res = sub i32 %0, %1
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %res, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define { i16, i1 } @llvm.usub.with.overflow.i16(i16 noundef %0, i16 noundef %1) local_unnamed_addr {
  %overflow = icmp ugt i16 %1, %0
  %res = sub i16 %0, %1
  %base = insertvalue {i16, i1} {i16 0, i1 0}, i16 %res, 0
  %fullres = insertvalue {i16, i1} %base, i1 %overflow, 1
  ret {i16, i1} %fullres
}

define { i8, i1 } @llvm.usub.with.overflow.i8(i8 noundef %0, i8 noundef %1) local_unnamed_addr {
  %overflow = icmp ugt i8 %1, %0
  %res = sub i8 %0, %1
  %base = insertvalue {i8, i1} {i8 0, i1 0}, i8 %res, 0
  %fullres = insertvalue {i8, i1} %base, i1 %overflow, 1
  ret {i8, i1} %fullres
}

define { i64, i1 } @llvm.uadd.with.overflow.i64(i64 noundef %0, i64 noundef %1) local_unnamed_addr {
  %max = sub i64 18446744073709551615, %0
  %overflow = icmp ugt i64 %1, %max
  %res = add i64 %0, %1
  %base = insertvalue {i64, i1} {i64 0, i1 0}, i64 %res, 0
  %fullres = insertvalue {i64, i1} %base, i1 %overflow, 1
  ret {i64, i1} %fullres
}

define { i32, i1 } @llvm.uadd.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %max = sub i32 4294967295, %0
  %overflow = icmp ugt i32 %1, %max
  %res = add i32 %0, %1
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %res, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}

define { i16, i1 } @llvm.uadd.with.overflow.i16(i16 noundef %0, i16 noundef %1) local_unnamed_addr {
  %max = sub i16 65535, %0
  %overflow = icmp ugt i16 %1, %max
  %res = add i16 %0, %1
  %base = insertvalue {i16, i1} {i16 0, i1 0}, i16 %res, 0
  %fullres = insertvalue {i16, i1} %base, i1 %overflow, 1
  ret {i16, i1} %fullres
}

define { i8, i1 } @llvm.uadd.with.overflow.i8(i8 noundef %0, i8 noundef %1) local_unnamed_addr {
  %max = sub i8 255, %0
  %overflow = icmp ugt i8 %1, %max
  %res = add i8 %0, %1
  %base = insertvalue {i8, i1} {i8 0, i1 0}, i8 %res, 0
  %fullres = insertvalue {i8, i1} %base, i1 %overflow, 1
  ret {i8, i1} %fullres
}

; This was LLM-generated, but was exhaustively tested.
define float @llvm.sqrt.f32(float %x) {
entry:
  %is_nan = fcmp uno float %x, %x
  br i1 %is_nan, label %silence_nan, label %chk1

chk1:
  %is_neg = fcmp olt float %x, 0.000000e+00
  br i1 %is_neg, label %ret_nan, label %chk2

chk2:
  ; covers +0.0, -0.0 (sign preserved via ret_x), and +inf
  %is_zero = fcmp oeq float %x, 0.000000e+00
  %is_inf  = fcmp oeq float %x, 0x7FF0000000000000
  %trivial = or i1 %is_zero, %is_inf
  br i1 %trivial, label %ret_x, label %compute

compute:
  ; The fast-inverse-sqrt bit trick assumes a *normalized* float (implicit
  ; leading 1 + biased exponent). Subnormals have exponent field 0 and no
  ; implicit 1, so the magic-constant seed is wildly wrong and Newton-Raphson
  ; overflows to +inf. Fix: if x is subnormal (x < 2^-126, the smallest
  ; normal), scale it up into the normalized range by 2^96, run the algorithm,
  ; then scale the result back down by 2^48 since sqrt(x*2^96) = sqrt(x)*2^48.
  %smallest_normal = bitcast i32 8388608 to float      ; 0x00800000 = 2^-126
  %is_sub    = fcmp olt float %x, %smallest_normal
  %scale_up_c   = bitcast i32 1870659584 to float      ; 0x6F800000 = 2^96
  %scale_down_c = bitcast i32 662700032 to float       ; 0x27800000 = 2^-48
  %scale_up   = select i1 %is_sub, float %scale_up_c,   float 1.000000e+00
  %scale_down = select i1 %is_sub, float %scale_down_c, float 1.000000e+00
  %xs = fmul float %x, %scale_up

  ; initial guess for 1/sqrt(xs): i = 0x5f3759df - (bits(xs) >> 1)
  %ibits  = bitcast float %xs to i32
  %ishift = lshr i32 %ibits, 1
  %iguess = sub i32 1597463007, %ishift        ; 0x5f3759df
  %y0     = bitcast i32 %iguess to float

  %half = fmul float %xs, 5.000000e-01

  ; Newton-Raphson on rsqrt, x3
  %y0sq  = fmul float %y0, %y0
  %t0    = fmul float %half, %y0sq
  %c0    = fsub float 1.500000e+00, %t0
  %y1    = fmul float %y0, %c0

  %y1sq  = fmul float %y1, %y1
  %t1    = fmul float %half, %y1sq
  %c1    = fsub float 1.500000e+00, %t1
  %y2    = fmul float %y1, %c1

  %y2sq  = fmul float %y2, %y2
  %t2    = fmul float %half, %y2sq
  %c2    = fsub float 1.500000e+00, %t2
  %y3    = fmul float %y2, %c2

  ; sqrt(xs) = xs * rsqrt(xs)
  %r0 = fmul float %xs, %y3

  ; one Newton step directly on sqrt to shave off remaining error
  %r0d   = fdiv float %xs, %r0
  %rsum  = fadd float %r0, %r0d
  %result_scaled = fmul float %rsum, 5.000000e-01

  ; undo the scaling (no-op when x was already normal: scale_down = 1.0)
  %result = fmul float %result_scaled, %scale_down
  br label %ret_val

silence_nan:
  ; quiet the NaN by setting the most-significant mantissa bit (bit 22),
  ; which silences a signaling NaN while preserving its sign and payload
  %nan_bits    = bitcast float %x to i32
  %quiet_bits  = or i32 %nan_bits, 4194304        ; 0x00400000
  %quiet_nan   = bitcast i32 %quiet_bits to float
  ret float %quiet_nan

ret_nan:
  %nan = fdiv float 0.000000e+00, 0.000000e+00   ; generate qNaN, no hex literal needed
  ret float %nan

ret_x:
  ret float %x

ret_val:
  ret float %result
}
