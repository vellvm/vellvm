; The boolean literals `true` and `false` in every position an i1 constant
; can be written.
;
; `true` and `false` are the i1 constants 1 and 0.  Vellvm's parser used to
; reject them as switch case values (`switch i1 %c, label %d [ i1 true, ...`),
; so this file spells an i1 constant with them everywhere one can appear:
; instruction operands, branch conditions, phi and switch arms, constant
; aggregates and vectors, indices, global initializers, constant expressions,
; the flag arguments of intrinsics, metadata, and the ASSERT lines themselves.
;
; A parse error loses every case in the file, so a new failure here shows up
; as the whole file failing rather than one assertion.
;
; Each case returns an i64 so the file can also be run natively, e.g.
;   clang -w tests/ll/bool-literals.ll -o a.out && ./a.out
; and its output compared with the ASSERTs at the bottom.
;
; Generated with tests/gen.py (print-all mode) from the functions below.

; ================================================== instruction operands

define i1 @help_ret_true() {
  ret i1 true
}

define i64 @ret_true() {
  %r = call i1 @help_ret_true()
  %z = zext i1 %r to i64
  ret i64 %z
}

define i1 @help_ret_false() {
  ret i1 false
}

define i64 @ret_false() {
  %r = call i1 @help_ret_false()
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @zext_true() {
  %z = zext i1 true to i64
  ret i64 %z
}

define i64 @sext_true() {
  %z = sext i1 true to i64
  ret i64 %z
}

define i64 @zext_false() {
  %z = zext i1 false to i64
  ret i64 %z
}

define i64 @binop_both() {
  %r = xor i1 true, false
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @binop_second() {
  %a = add i1 true, false
  %r = and i1 %a, false
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @icmp_literals() {
  %r = icmp ne i1 true, false
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @icmp_slt() {
  %r = icmp slt i1 true, false
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @select_cond_true() {
  %r = select i1 true, i64 10, i64 20
  ret i64 %r
}

define i64 @select_cond_false() {
  %r = select i1 false, i64 10, i64 20
  ret i64 %r
}

define i64 @select_arms() {
  %c = icmp eq i64 0, 0
  %r = select i1 %c, i1 true, i1 false
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @freeze_true() {
  %r = freeze i1 true
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @store_load() {
  %p = alloca i1
  store i1 true, ptr %p
  %r = load i1, ptr %p
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @store_volatile() {
  %p = alloca i1
  store volatile i1 false, ptr %p, align 1
  %r = load volatile i1, ptr %p, align 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i1 @help_not(i1 %x) {
  %r = xor i1 %x, true
  ret i1 %r
}

define i64 @call_arg() {
  %r = call i1 @help_not(i1 false)
  %z = zext i1 %r to i64
  ret i64 %z
}

define zeroext i1 @help_id(i1 zeroext %x) {
  ret i1 %x
}

define i64 @call_arg_attrs() {
  %r = call zeroext i1 @help_id(i1 zeroext true)
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @uitofp_true() {
  %f = uitofp i1 true to double
  %r = fptosi double %f to i64
  ret i64 %r
}

define i64 @sitofp_true() {
  %f = sitofp i1 true to double
  %r = fptosi double %f to i64
  ret i64 %r
}

define i64 @bitcast_true() {
  %v = bitcast i1 true to <1 x i1>
  %r = extractelement <1 x i1> %v, i32 0
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @inttoptr_true() {
  %p = inttoptr i1 true to ptr
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

; ========================================================== control flow

define i64 @br_true() {
  br i1 true, label %t, label %f
t:
  ret i64 10
f:
  ret i64 20
}

define i64 @br_false() {
  br i1 false, label %t, label %f
t:
  ret i64 10
f:
  ret i64 20
}

define i64 @phi_literals() {
entry:
  %c = icmp eq i64 0, 0
  br i1 %c, label %a, label %b
a:
  br label %join
b:
  br label %join
join:
  %r = phi i1 [ true, %a ], [ false, %b ]
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @switch_on_true() {
  switch i1 true, label %d [ i1 0, label %zero
                             i1 1, label %one ]
zero:
  ret i64 100
one:
  ret i64 101
d:
  ret i64 102
}

define i64 @switch_case_true() {
  %c = icmp eq i64 0, 0
  switch i1 %c, label %d [ i1 true, label %one ]
one:
  ret i64 101
d:
  ret i64 102
}

define i64 @switch_case_false() {
  %c = icmp eq i64 0, 0
  switch i1 %c, label %d [ i1 false, label %zero ]
zero:
  ret i64 100
d:
  ret i64 102
}

define i64 @switch_case_both() {
  %c = icmp eq i64 0, 1
  switch i1 %c, label %d [
    i1 false, label %zero
    i1 true, label %one
  ]
zero:
  ret i64 100
one:
  ret i64 101
d:
  ret i64 102
}

; ================================================ aggregates and vectors

define i64 @struct_const() {
  %r = extractvalue { i1, i1 } { i1 true, i1 false }, 0
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @struct_const_1() {
  %r = extractvalue { i1, i1 } { i1 true, i1 false }, 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @packed_struct_const() {
  %r = extractvalue <{ i8, i1 }> <{ i8 7, i1 true }>, 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @array_const() {
  %r = extractvalue [3 x i1] [i1 false, i1 true, i1 false], 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @insertvalue_true() {
  %s = insertvalue { i1, i8 } { i1 false, i8 0 }, i1 true, 0
  %r = extractvalue { i1, i8 } %s, 0
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @vector_const() {
  %r = extractelement <4 x i1> <i1 false, i1 true, i1 false, i1 true>, i32 3
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @vector_binop() {
  %v = and <2 x i1> <i1 true, i1 true>, <i1 true, i1 false>
  %r = extractelement <2 x i1> %v, i32 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @vector_splat() {
  %v = xor <4 x i1> splat (i1 true), zeroinitializer
  %r = extractelement <4 x i1> %v, i32 2
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @insertelement_true() {
  %v = insertelement <2 x i1> zeroinitializer, i1 true, i32 1
  %r = extractelement <2 x i1> %v, i32 1
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @select_vector_cond() {
  %v = select <2 x i1> <i1 true, i1 false>, <2 x i64> <i64 1, i64 2>, <2 x i64> <i64 4, i64 5>
  %a = extractelement <2 x i64> %v, i32 0
  %b = extractelement <2 x i64> %v, i32 1
  %r = add i64 %a, %b
  ret i64 %r
}

define i64 @nested_const() {
  %r = extractvalue { i8, [2 x { i1, i1 }] } { i8 0, [2 x { i1, i1 }] [{ i1, i1 } { i1 false, i1 false }, { i1, i1 } { i1 false, i1 true }] }, 1, 1, 1
  %z = zext i1 %r to i64
  ret i64 %z
}

; ========================================= literals as indices and sizes

define i64 @gep_index_true() {
  %p = getelementptr i8, ptr null, i1 true
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

define i64 @gep_index_false() {
  %p = getelementptr i8, ptr null, i1 false
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

define i64 @extractelement_index_true() {
  %e = extractelement <2 x i8> <i8 5, i8 7>, i1 true
  %r = zext i8 %e to i64
  ret i64 %r
}

define i64 @insertelement_index_false() {
  %v = insertelement <2 x i8> <i8 5, i8 7>, i8 9, i1 false
  %e = extractelement <2 x i8> %v, i32 0
  %r = zext i8 %e to i64
  ret i64 %r
}

define i64 @alloca_count_true() {
  %p = alloca i64, i1 true
  store i64 42, ptr %p
  %r = load i64, ptr %p
  ret i64 %r
}

; =============================================================== globals

@g_true = global i1 true

define i64 @global_true() {
  %r = load i1, ptr @g_true
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_false = global i1 false

define i64 @global_false() {
  %r = load i1, ptr @g_false
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_const = private unnamed_addr constant i1 true, align 1

define i64 @global_constant() {
  %r = load i1, ptr @g_const
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_arr = global [3 x i1] [i1 false, i1 false, i1 true]

define i64 @global_array() {
  %p = getelementptr [3 x i1], ptr @g_arr, i64 0, i64 2
  %r = load i1, ptr %p
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_struct = global { i32, i1 } { i32 5, i1 true }

define i64 @global_struct() {
  %p = getelementptr { i32, i1 }, ptr @g_struct, i64 0, i32 1
  %r = load i1, ptr %p
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_vec = global <4 x i1> <i1 true, i1 false, i1 true, i1 false>

define i64 @global_vector() {
  %v = load <4 x i1>, ptr @g_vec
  %i = bitcast <4 x i1> %v to i4
  %r = zext i4 %i to i64
  ret i64 %r
}

@g_splat = global <4 x i1> splat (i1 true)

define i64 @global_splat() {
  %v = load <4 x i1>, ptr @g_splat
  %r = extractelement <4 x i1> %v, i32 3
  %z = zext i1 %r to i64
  ret i64 %z
}

; ================================================== constant expressions

define i64 @constexpr_xor() {
  %z = zext i1 xor (i1 true, i1 false) to i64
  ret i64 %z
}

define i64 @constexpr_add() {
  %z = zext i1 add (i1 true, i1 true) to i64
  ret i64 %z
}

define i64 @constexpr_sub_operand() {
  %r = and i1 sub (i1 false, i1 true), true
  %z = zext i1 %r to i64
  ret i64 %z
}

define i64 @constexpr_trunc() {
  %r = xor i1 trunc (i8 2 to i1), true
  %z = zext i1 %r to i64
  ret i64 %z
}

@g_cexpr = global i1 xor (i1 true, i1 false)

define i64 @constexpr_global() {
  %r = load i1, ptr @g_cexpr
  %z = zext i1 %r to i64
  ret i64 %z
}

; ============================================== intrinsic flag arguments

declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)

define i64 @memcpy_false() {
  %a = alloca i64
  %b = alloca i64
  store i64 42, ptr %a
  call void @llvm.memcpy.p0.p0.i64(ptr %b, ptr %a, i64 8, i1 false)
  %r = load i64, ptr %b
  ret i64 %r
}

declare void @llvm.memset.p0.i64(ptr, i8, i64, i1 immarg)

define i64 @memset_false() {
  %a = alloca i64
  store i64 42, ptr %a
  call void @llvm.memset.p0.i64(ptr %a, i8 0, i64 8, i1 false)
  %r = load i64, ptr %a
  ret i64 %r
}

declare void @llvm.assume(i1)

define i64 @assume_true() {
  call void @llvm.assume(i1 true)
  ret i64 7
}

define i64 @assume_bundle() {
  %p = alloca i64
  call void @llvm.assume(i1 true) [ "nonnull"(ptr %p) ]
  ret i64 7
}

declare i1 @llvm.expect.i1(i1, i1)

define i64 @expect_true() {
  %r = call i1 @llvm.expect.i1(i1 true, i1 true)
  %z = zext i1 %r to i64
  ret i64 %z
}

; =============================================== metadata and attributes

!0 = !{i1 true, i1 false}

define i64 @md_operand() {
  %p = alloca i64, !mdbool !0
  ret i64 7
}

!llvm.module.flags = !{!1}
!1 = !{i32 1, !"bool flag", i1 true}

define i64 @md_module_flag() {
  ret i64 7
}

!llvm.dbg.cu = !{!10}
!llvm.module.flags = !{!12}
!10 = distinct !DICompileUnit(language: DW_LANG_C99, file: !11, producer: "x", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: true)
!11 = !DIFile(filename: "a.c", directory: "/")
!12 = !{i32 2, !"Debug Info Version", i32 3}
!13 = !DILocation(line: 1, column: 1, scope: !14)
!14 = distinct !DISubprogram(name: "md_named_fields", scope: !11, file: !11, line: 1, type: !15, isLocal: false, isDefinition: true, isOptimized: true, unit: !10)
!15 = !DISubroutineType(types: !16)
!16 = !{}

define i64 @md_named_fields() {
  ret i64 7, !dbg !13
}

define i1 @help_range() {
  ret i1 false
}

define i64 @range_attr() {
  %r = call range(i1 0, 1) i1 @help_range()
  %z = sext i1 %r to i64
  %n = sub i64 0, %z
  %o = add i64 %n, 1
  ret i64 %o
}

!20 = !{!"branch_weights", i32 1, i32 0}

define i64 @prof_md() {
  br i1 true, label %t, label %f, !prof !20
t:
  ret i64 10
f:
  ret i64 20
}

; ======================================================== ASSERT literals

; `true` and `false` as the arguments and expected results of assertions

define i1 @not(i1 %x) {
  %r = xor i1 %x, true
  ret i1 %r
}

define <2 x i1> @vnot(<2 x i1> %x) {
  %r = xor <2 x i1> %x, <i1 true, i1 true>
  ret <2 x i1> %r
}

define { i1, i1 } @pair(i1 %x) {
  %r = insertvalue { i1, i1 } { i1 true, i1 false }, i1 %x, 1
  ret { i1, i1 } %r
}

; ASSERT EQ: i1 true = call i1 @not(i1 false)
; ASSERT EQ: i1 false = call i1 @not(i1 true)
; ASSERT EQ: i1 1 = call i1 @not(i1 false)
; ASSERT EQ: i1 true = call i1 @not(i1 0)
; ASSERT EQ: <2 x i1> <i1 true, i1 false> = call <2 x i1> @vnot(<2 x i1> <i1 false, i1 true>)
; ASSERT EQ: { i1, i1 } { i1 true, i1 true } = call { i1, i1 } @pair(i1 true)

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_ret_true = private unnamed_addr constant [19 x i8] c"ret_true() = %lld\0A\00"
@fmt_ret_false = private unnamed_addr constant [20 x i8] c"ret_false() = %lld\0A\00"
@fmt_zext_true = private unnamed_addr constant [20 x i8] c"zext_true() = %lld\0A\00"
@fmt_sext_true = private unnamed_addr constant [20 x i8] c"sext_true() = %lld\0A\00"
@fmt_zext_false = private unnamed_addr constant [21 x i8] c"zext_false() = %lld\0A\00"
@fmt_binop_both = private unnamed_addr constant [21 x i8] c"binop_both() = %lld\0A\00"
@fmt_binop_second = private unnamed_addr constant [23 x i8] c"binop_second() = %lld\0A\00"
@fmt_icmp_literals = private unnamed_addr constant [24 x i8] c"icmp_literals() = %lld\0A\00"
@fmt_icmp_slt = private unnamed_addr constant [19 x i8] c"icmp_slt() = %lld\0A\00"
@fmt_select_cond_true = private unnamed_addr constant [27 x i8] c"select_cond_true() = %lld\0A\00"
@fmt_select_cond_false = private unnamed_addr constant [28 x i8] c"select_cond_false() = %lld\0A\00"
@fmt_select_arms = private unnamed_addr constant [22 x i8] c"select_arms() = %lld\0A\00"
@fmt_freeze_true = private unnamed_addr constant [22 x i8] c"freeze_true() = %lld\0A\00"
@fmt_store_load = private unnamed_addr constant [21 x i8] c"store_load() = %lld\0A\00"
@fmt_store_volatile = private unnamed_addr constant [25 x i8] c"store_volatile() = %lld\0A\00"
@fmt_call_arg = private unnamed_addr constant [19 x i8] c"call_arg() = %lld\0A\00"
@fmt_call_arg_attrs = private unnamed_addr constant [25 x i8] c"call_arg_attrs() = %lld\0A\00"
@fmt_uitofp_true = private unnamed_addr constant [22 x i8] c"uitofp_true() = %lld\0A\00"
@fmt_sitofp_true = private unnamed_addr constant [22 x i8] c"sitofp_true() = %lld\0A\00"
@fmt_bitcast_true = private unnamed_addr constant [23 x i8] c"bitcast_true() = %lld\0A\00"
@fmt_inttoptr_true = private unnamed_addr constant [24 x i8] c"inttoptr_true() = %lld\0A\00"
@fmt_br_true = private unnamed_addr constant [18 x i8] c"br_true() = %lld\0A\00"
@fmt_br_false = private unnamed_addr constant [19 x i8] c"br_false() = %lld\0A\00"
@fmt_phi_literals = private unnamed_addr constant [23 x i8] c"phi_literals() = %lld\0A\00"
@fmt_switch_on_true = private unnamed_addr constant [25 x i8] c"switch_on_true() = %lld\0A\00"
@fmt_switch_case_true = private unnamed_addr constant [27 x i8] c"switch_case_true() = %lld\0A\00"
@fmt_switch_case_false = private unnamed_addr constant [28 x i8] c"switch_case_false() = %lld\0A\00"
@fmt_switch_case_both = private unnamed_addr constant [27 x i8] c"switch_case_both() = %lld\0A\00"
@fmt_struct_const = private unnamed_addr constant [23 x i8] c"struct_const() = %lld\0A\00"
@fmt_struct_const_1 = private unnamed_addr constant [25 x i8] c"struct_const_1() = %lld\0A\00"
@fmt_packed_struct_const = private unnamed_addr constant [30 x i8] c"packed_struct_const() = %lld\0A\00"
@fmt_array_const = private unnamed_addr constant [22 x i8] c"array_const() = %lld\0A\00"
@fmt_insertvalue_true = private unnamed_addr constant [27 x i8] c"insertvalue_true() = %lld\0A\00"
@fmt_vector_const = private unnamed_addr constant [23 x i8] c"vector_const() = %lld\0A\00"
@fmt_vector_binop = private unnamed_addr constant [23 x i8] c"vector_binop() = %lld\0A\00"
@fmt_vector_splat = private unnamed_addr constant [23 x i8] c"vector_splat() = %lld\0A\00"
@fmt_insertelement_true = private unnamed_addr constant [29 x i8] c"insertelement_true() = %lld\0A\00"
@fmt_select_vector_cond = private unnamed_addr constant [29 x i8] c"select_vector_cond() = %lld\0A\00"
@fmt_nested_const = private unnamed_addr constant [23 x i8] c"nested_const() = %lld\0A\00"
@fmt_gep_index_true = private unnamed_addr constant [25 x i8] c"gep_index_true() = %lld\0A\00"
@fmt_gep_index_false = private unnamed_addr constant [26 x i8] c"gep_index_false() = %lld\0A\00"
@fmt_extractelement_index_true = private unnamed_addr constant [36 x i8] c"extractelement_index_true() = %lld\0A\00"
@fmt_insertelement_index_false = private unnamed_addr constant [36 x i8] c"insertelement_index_false() = %lld\0A\00"
@fmt_alloca_count_true = private unnamed_addr constant [28 x i8] c"alloca_count_true() = %lld\0A\00"
@fmt_global_true = private unnamed_addr constant [22 x i8] c"global_true() = %lld\0A\00"
@fmt_global_false = private unnamed_addr constant [23 x i8] c"global_false() = %lld\0A\00"
@fmt_global_constant = private unnamed_addr constant [26 x i8] c"global_constant() = %lld\0A\00"
@fmt_global_array = private unnamed_addr constant [23 x i8] c"global_array() = %lld\0A\00"
@fmt_global_struct = private unnamed_addr constant [24 x i8] c"global_struct() = %lld\0A\00"
@fmt_global_vector = private unnamed_addr constant [24 x i8] c"global_vector() = %lld\0A\00"
@fmt_global_splat = private unnamed_addr constant [23 x i8] c"global_splat() = %lld\0A\00"
@fmt_constexpr_xor = private unnamed_addr constant [24 x i8] c"constexpr_xor() = %lld\0A\00"
@fmt_constexpr_add = private unnamed_addr constant [24 x i8] c"constexpr_add() = %lld\0A\00"
@fmt_constexpr_sub_operand = private unnamed_addr constant [32 x i8] c"constexpr_sub_operand() = %lld\0A\00"
@fmt_constexpr_trunc = private unnamed_addr constant [26 x i8] c"constexpr_trunc() = %lld\0A\00"
@fmt_constexpr_global = private unnamed_addr constant [27 x i8] c"constexpr_global() = %lld\0A\00"
@fmt_memcpy_false = private unnamed_addr constant [23 x i8] c"memcpy_false() = %lld\0A\00"
@fmt_memset_false = private unnamed_addr constant [23 x i8] c"memset_false() = %lld\0A\00"
@fmt_assume_true = private unnamed_addr constant [22 x i8] c"assume_true() = %lld\0A\00"
@fmt_assume_bundle = private unnamed_addr constant [24 x i8] c"assume_bundle() = %lld\0A\00"
@fmt_expect_true = private unnamed_addr constant [22 x i8] c"expect_true() = %lld\0A\00"
@fmt_md_operand = private unnamed_addr constant [21 x i8] c"md_operand() = %lld\0A\00"
@fmt_md_module_flag = private unnamed_addr constant [25 x i8] c"md_module_flag() = %lld\0A\00"
@fmt_md_named_fields = private unnamed_addr constant [26 x i8] c"md_named_fields() = %lld\0A\00"
@fmt_range_attr = private unnamed_addr constant [21 x i8] c"range_attr() = %lld\0A\00"
@fmt_prof_md = private unnamed_addr constant [18 x i8] c"prof_md() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @ret_true()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_ret_true, i64 %v0)
  %v1 = call i64 @ret_false()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_ret_false, i64 %v1)
  %v2 = call i64 @zext_true()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_zext_true, i64 %v2)
  %v3 = call i64 @sext_true()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_sext_true, i64 %v3)
  %v4 = call i64 @zext_false()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_zext_false, i64 %v4)
  %v5 = call i64 @binop_both()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_binop_both, i64 %v5)
  %v6 = call i64 @binop_second()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_binop_second, i64 %v6)
  %v7 = call i64 @icmp_literals()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_icmp_literals, i64 %v7)
  %v8 = call i64 @icmp_slt()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_icmp_slt, i64 %v8)
  %v9 = call i64 @select_cond_true()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_select_cond_true, i64 %v9)
  %v10 = call i64 @select_cond_false()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_select_cond_false, i64 %v10)
  %v11 = call i64 @select_arms()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_select_arms, i64 %v11)
  %v12 = call i64 @freeze_true()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_freeze_true, i64 %v12)
  %v13 = call i64 @store_load()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_store_load, i64 %v13)
  %v14 = call i64 @store_volatile()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_store_volatile, i64 %v14)
  %v15 = call i64 @call_arg()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_call_arg, i64 %v15)
  %v16 = call i64 @call_arg_attrs()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_call_arg_attrs, i64 %v16)
  %v17 = call i64 @uitofp_true()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_uitofp_true, i64 %v17)
  %v18 = call i64 @sitofp_true()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_sitofp_true, i64 %v18)
  %v19 = call i64 @bitcast_true()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_bitcast_true, i64 %v19)
  %v20 = call i64 @inttoptr_true()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_inttoptr_true, i64 %v20)
  %v21 = call i64 @br_true()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_br_true, i64 %v21)
  %v22 = call i64 @br_false()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_br_false, i64 %v22)
  %v23 = call i64 @phi_literals()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_phi_literals, i64 %v23)
  %v24 = call i64 @switch_on_true()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_switch_on_true, i64 %v24)
  %v25 = call i64 @switch_case_true()
  %p25 = call i32 (ptr, ...) @printf(ptr @fmt_switch_case_true, i64 %v25)
  %v26 = call i64 @switch_case_false()
  %p26 = call i32 (ptr, ...) @printf(ptr @fmt_switch_case_false, i64 %v26)
  %v27 = call i64 @switch_case_both()
  %p27 = call i32 (ptr, ...) @printf(ptr @fmt_switch_case_both, i64 %v27)
  %v28 = call i64 @struct_const()
  %p28 = call i32 (ptr, ...) @printf(ptr @fmt_struct_const, i64 %v28)
  %v29 = call i64 @struct_const_1()
  %p29 = call i32 (ptr, ...) @printf(ptr @fmt_struct_const_1, i64 %v29)
  %v30 = call i64 @packed_struct_const()
  %p30 = call i32 (ptr, ...) @printf(ptr @fmt_packed_struct_const, i64 %v30)
  %v31 = call i64 @array_const()
  %p31 = call i32 (ptr, ...) @printf(ptr @fmt_array_const, i64 %v31)
  %v32 = call i64 @insertvalue_true()
  %p32 = call i32 (ptr, ...) @printf(ptr @fmt_insertvalue_true, i64 %v32)
  %v33 = call i64 @vector_const()
  %p33 = call i32 (ptr, ...) @printf(ptr @fmt_vector_const, i64 %v33)
  %v34 = call i64 @vector_binop()
  %p34 = call i32 (ptr, ...) @printf(ptr @fmt_vector_binop, i64 %v34)
  %v35 = call i64 @vector_splat()
  %p35 = call i32 (ptr, ...) @printf(ptr @fmt_vector_splat, i64 %v35)
  %v36 = call i64 @insertelement_true()
  %p36 = call i32 (ptr, ...) @printf(ptr @fmt_insertelement_true, i64 %v36)
  %v37 = call i64 @select_vector_cond()
  %p37 = call i32 (ptr, ...) @printf(ptr @fmt_select_vector_cond, i64 %v37)
  %v38 = call i64 @nested_const()
  %p38 = call i32 (ptr, ...) @printf(ptr @fmt_nested_const, i64 %v38)
  %v39 = call i64 @gep_index_true()
  %p39 = call i32 (ptr, ...) @printf(ptr @fmt_gep_index_true, i64 %v39)
  %v40 = call i64 @gep_index_false()
  %p40 = call i32 (ptr, ...) @printf(ptr @fmt_gep_index_false, i64 %v40)
  %v41 = call i64 @extractelement_index_true()
  %p41 = call i32 (ptr, ...) @printf(ptr @fmt_extractelement_index_true, i64 %v41)
  %v42 = call i64 @insertelement_index_false()
  %p42 = call i32 (ptr, ...) @printf(ptr @fmt_insertelement_index_false, i64 %v42)
  %v43 = call i64 @alloca_count_true()
  %p43 = call i32 (ptr, ...) @printf(ptr @fmt_alloca_count_true, i64 %v43)
  %v44 = call i64 @global_true()
  %p44 = call i32 (ptr, ...) @printf(ptr @fmt_global_true, i64 %v44)
  %v45 = call i64 @global_false()
  %p45 = call i32 (ptr, ...) @printf(ptr @fmt_global_false, i64 %v45)
  %v46 = call i64 @global_constant()
  %p46 = call i32 (ptr, ...) @printf(ptr @fmt_global_constant, i64 %v46)
  %v47 = call i64 @global_array()
  %p47 = call i32 (ptr, ...) @printf(ptr @fmt_global_array, i64 %v47)
  %v48 = call i64 @global_struct()
  %p48 = call i32 (ptr, ...) @printf(ptr @fmt_global_struct, i64 %v48)
  %v49 = call i64 @global_vector()
  %p49 = call i32 (ptr, ...) @printf(ptr @fmt_global_vector, i64 %v49)
  %v50 = call i64 @global_splat()
  %p50 = call i32 (ptr, ...) @printf(ptr @fmt_global_splat, i64 %v50)
  %v51 = call i64 @constexpr_xor()
  %p51 = call i32 (ptr, ...) @printf(ptr @fmt_constexpr_xor, i64 %v51)
  %v52 = call i64 @constexpr_add()
  %p52 = call i32 (ptr, ...) @printf(ptr @fmt_constexpr_add, i64 %v52)
  %v53 = call i64 @constexpr_sub_operand()
  %p53 = call i32 (ptr, ...) @printf(ptr @fmt_constexpr_sub_operand, i64 %v53)
  %v54 = call i64 @constexpr_trunc()
  %p54 = call i32 (ptr, ...) @printf(ptr @fmt_constexpr_trunc, i64 %v54)
  %v55 = call i64 @constexpr_global()
  %p55 = call i32 (ptr, ...) @printf(ptr @fmt_constexpr_global, i64 %v55)
  %v56 = call i64 @memcpy_false()
  %p56 = call i32 (ptr, ...) @printf(ptr @fmt_memcpy_false, i64 %v56)
  %v57 = call i64 @memset_false()
  %p57 = call i32 (ptr, ...) @printf(ptr @fmt_memset_false, i64 %v57)
  %v58 = call i64 @assume_true()
  %p58 = call i32 (ptr, ...) @printf(ptr @fmt_assume_true, i64 %v58)
  %v59 = call i64 @assume_bundle()
  %p59 = call i32 (ptr, ...) @printf(ptr @fmt_assume_bundle, i64 %v59)
  %v60 = call i64 @expect_true()
  %p60 = call i32 (ptr, ...) @printf(ptr @fmt_expect_true, i64 %v60)
  %v61 = call i64 @md_operand()
  %p61 = call i32 (ptr, ...) @printf(ptr @fmt_md_operand, i64 %v61)
  %v62 = call i64 @md_module_flag()
  %p62 = call i32 (ptr, ...) @printf(ptr @fmt_md_module_flag, i64 %v62)
  %v63 = call i64 @md_named_fields()
  %p63 = call i32 (ptr, ...) @printf(ptr @fmt_md_named_fields, i64 %v63)
  %v64 = call i64 @range_attr()
  %p64 = call i32 (ptr, ...) @printf(ptr @fmt_range_attr, i64 %v64)
  %v65 = call i64 @prof_md()
  %p65 = call i32 (ptr, ...) @printf(ptr @fmt_prof_md, i64 %v65)
  ret i32 0
}

; ASSERT EQ: i64 1   = call i64 @ret_true()
; ASSERT EQ: i64 0   = call i64 @ret_false()
; ASSERT EQ: i64 1   = call i64 @zext_true()
; ASSERT EQ: i64 -1  = call i64 @sext_true()
; ASSERT EQ: i64 0   = call i64 @zext_false()
; ASSERT EQ: i64 1   = call i64 @binop_both()
; ASSERT EQ: i64 0   = call i64 @binop_second()
; ASSERT EQ: i64 1   = call i64 @icmp_literals()
; ASSERT EQ: i64 1   = call i64 @icmp_slt()
; ASSERT EQ: i64 10  = call i64 @select_cond_true()
; ASSERT EQ: i64 20  = call i64 @select_cond_false()
; ASSERT EQ: i64 1   = call i64 @select_arms()
; ASSERT EQ: i64 1   = call i64 @freeze_true()
; ASSERT EQ: i64 1   = call i64 @store_load()
; ASSERT EQ: i64 0   = call i64 @store_volatile()
; ASSERT EQ: i64 1   = call i64 @call_arg()
; ASSERT EQ: i64 1   = call i64 @call_arg_attrs()
; ASSERT EQ: i64 1   = call i64 @uitofp_true()
; ASSERT EQ: i64 -1  = call i64 @sitofp_true()
; ASSERT EQ: i64 1   = call i64 @bitcast_true()
; ASSERT EQ: i64 1   = call i64 @inttoptr_true()
; ASSERT EQ: i64 10  = call i64 @br_true()
; ASSERT EQ: i64 20  = call i64 @br_false()
; ASSERT EQ: i64 1   = call i64 @phi_literals()
; ASSERT EQ: i64 101 = call i64 @switch_on_true()
; ASSERT EQ: i64 101 = call i64 @switch_case_true()
; ASSERT EQ: i64 102 = call i64 @switch_case_false()
; ASSERT EQ: i64 100 = call i64 @switch_case_both()
; ASSERT EQ: i64 1   = call i64 @struct_const()
; ASSERT EQ: i64 0   = call i64 @struct_const_1()
; ASSERT EQ: i64 1   = call i64 @packed_struct_const()
; ASSERT EQ: i64 1   = call i64 @array_const()
; ASSERT EQ: i64 1   = call i64 @insertvalue_true()
; ASSERT EQ: i64 1   = call i64 @vector_const()
; ASSERT EQ: i64 0   = call i64 @vector_binop()
; ASSERT EQ: i64 1   = call i64 @vector_splat()
; ASSERT EQ: i64 1   = call i64 @insertelement_true()
; ASSERT EQ: i64 6   = call i64 @select_vector_cond()
; ASSERT EQ: i64 1   = call i64 @nested_const()
; ASSERT EQ: i64 -1  = call i64 @gep_index_true()
; ASSERT EQ: i64 0   = call i64 @gep_index_false()
; ASSERT EQ: i64 7   = call i64 @extractelement_index_true()
; ASSERT EQ: i64 9   = call i64 @insertelement_index_false()
; ASSERT EQ: i64 42  = call i64 @alloca_count_true()
; ASSERT EQ: i64 1   = call i64 @global_true()
; ASSERT EQ: i64 0   = call i64 @global_false()
; ASSERT EQ: i64 1   = call i64 @global_constant()
; ASSERT EQ: i64 1   = call i64 @global_array()
; ASSERT EQ: i64 1   = call i64 @global_struct()
; ASSERT EQ: i64 5   = call i64 @global_vector()
; ASSERT EQ: i64 1   = call i64 @global_splat()
; ASSERT EQ: i64 1   = call i64 @constexpr_xor()
; ASSERT EQ: i64 0   = call i64 @constexpr_add()
; ASSERT EQ: i64 1   = call i64 @constexpr_sub_operand()
; ASSERT EQ: i64 1   = call i64 @constexpr_trunc()
; ASSERT EQ: i64 1   = call i64 @constexpr_global()
; ASSERT EQ: i64 42  = call i64 @memcpy_false()
; ASSERT EQ: i64 0   = call i64 @memset_false()
; ASSERT EQ: i64 7   = call i64 @assume_true()
; ASSERT EQ: i64 7   = call i64 @assume_bundle()
; ASSERT EQ: i64 1   = call i64 @expect_true()
; ASSERT EQ: i64 7   = call i64 @md_operand()
; ASSERT EQ: i64 7   = call i64 @md_module_flag()
; ASSERT EQ: i64 7   = call i64 @md_named_fields()
; ASSERT EQ: i64 1   = call i64 @range_attr()
; ASSERT EQ: i64 10  = call i64 @prof_md()
