; Variadic arguments whose type cannot be read off their value.
;
; A callee lays its variadic arguments out by the types the call site passes
; them at.  It used to recompute those types from the values, which fails for
; a value that does not determine its type: poison (any type) and empty
; aggregates.  A call that merely *passes* such an argument, without reading
; it, raised an error.
;
; Each function skips over the odd argument with va_arg and returns one that
; follows it, so getting the odd argument's size wrong would also show.
;
; Generated tail: python3 tests/gen.py (print-all mode).

declare void @llvm.va_start(ptr)
declare void @llvm.va_end(ptr)

; the second variadic argument, after skipping an i64
define i64 @after_i64(i32 %n, ...) {
  %ap = alloca ptr
  call void @llvm.va_start(ptr %ap)
  %skipped = va_arg ptr %ap, i64
  %r = va_arg ptr %ap, i64
  call void @llvm.va_end(ptr %ap)
  ret i64 %r
}

; the second variadic argument, after skipping an i32
define i64 @after_i32(i32 %n, ...) {
  %ap = alloca ptr
  call void @llvm.va_start(ptr %ap)
  %skipped = va_arg ptr %ap, i32
  %r = va_arg ptr %ap, i64
  call void @llvm.va_end(ptr %ap)
  ret i64 %r
}

; the first variadic argument; whatever follows it is never read
define i64 @first(i32 %n, ...) {
  %ap = alloca ptr
  call void @llvm.va_start(ptr %ap)
  %r = va_arg ptr %ap, i64
  call void @llvm.va_end(ptr %ap)
  ret i64 %r
}

; baseline: nothing odd
define i64 @plain() {
  %r = call i64 (i32, ...) @after_i64(i32 0, i64 1, i64 42)
  ret i64 %r
}

; a poison argument that is skipped
define i64 @poison_i64_skipped() {
  %r = call i64 (i32, ...) @after_i64(i32 0, i64 poison, i64 43)
  ret i64 %r
}

; ... at a type narrower than the argument that follows
define i64 @poison_i32_skipped() {
  %r = call i64 (i32, ...) @after_i32(i32 0, i32 poison, i64 44)
  ret i64 %r
}

; a poison argument that is never reached
define i64 @poison_trailing() {
  %r = call i64 (i32, ...) @first(i32 0, i64 45, double poison)
  ret i64 %r
}

; a poison aggregate that is never reached
define i64 @poison_struct_trailing() {
  %r = call i64 (i32, ...) @first(i32 0, i64 46, {i32, i64} poison)
  ret i64 %r
}

; an empty array that is never reached
define i64 @empty_array_trailing() {
  %r = call i64 (i32, ...) @first(i32 0, i64 47, [0 x i32] zeroinitializer)
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_plain = private unnamed_addr constant [16 x i8] c"plain() = %lld\0A\00"
@fmt_poison_i64_skipped = private unnamed_addr constant [29 x i8] c"poison_i64_skipped() = %lld\0A\00"
@fmt_poison_i32_skipped = private unnamed_addr constant [29 x i8] c"poison_i32_skipped() = %lld\0A\00"
@fmt_poison_trailing = private unnamed_addr constant [26 x i8] c"poison_trailing() = %lld\0A\00"
@fmt_poison_struct_trailing = private unnamed_addr constant [33 x i8] c"poison_struct_trailing() = %lld\0A\00"
@fmt_empty_array_trailing = private unnamed_addr constant [31 x i8] c"empty_array_trailing() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @plain()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_plain, i64 %v0)
  %v1 = call i64 @poison_i64_skipped()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_poison_i64_skipped, i64 %v1)
  %v2 = call i64 @poison_i32_skipped()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_poison_i32_skipped, i64 %v2)
  %v3 = call i64 @poison_trailing()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_poison_trailing, i64 %v3)
  %v4 = call i64 @poison_struct_trailing()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_poison_struct_trailing, i64 %v4)
  %v5 = call i64 @empty_array_trailing()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_empty_array_trailing, i64 %v5)
  ret i32 0
}

; ASSERT EQ: i64 42 = call i64 @plain()
; ASSERT EQ: i64 43 = call i64 @poison_i64_skipped()
; ASSERT EQ: i64 44 = call i64 @poison_i32_skipped()
; ASSERT EQ: i64 45 = call i64 @poison_trailing()
; ASSERT EQ: i64 46 = call i64 @poison_struct_trailing()
; ASSERT EQ: i64 47 = call i64 @empty_array_trailing()
