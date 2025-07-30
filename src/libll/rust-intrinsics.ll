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

define void @llvm.lifetime.start.p0i8(i64 %blah, i8* nonnull %foo) {
     ret void
}

define void @llvm.lifetime.end.p0i8(i64 immarg %a1, i8* nocapture %a2) {
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
