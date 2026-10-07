; ptrtoint of poison.
;
; LangRef: poison propagates through ptrtoint -- `ptrtoint ptr poison to
; iN` is poison, not undefined behavior.  Vellvm used to raise UB ("Invalid
; PTOI conversion") on any non-pointer operand, poison included.
;
; A poison result's value is arbitrary, so these tests only observe that the
; instruction does not trap: they either discard the result or freeze it and
; mask every bit away, keeping the output comparable with a native run.

; the poison result, frozen and masked to a fixed value
define i64 @ptrtoint_poison_i64() {
  %i = ptrtoint ptr poison to i64
  %f = freeze i64 %i
  %z = and i64 %f, 0
  ret i64 %z
}

; same at a narrower integer type
define i64 @ptrtoint_poison_i32() {
  %i = ptrtoint ptr poison to i32
  %f = freeze i32 %i
  %z = and i32 %f, 0
  %r = zext i32 %z to i64
  ret i64 %r
}

; a poison pointer read back from uninitialized memory
define i64 @ptrtoint_uninit_load() {
  %s = alloca ptr
  %p = load ptr, ptr %s
  %i = ptrtoint ptr %p to i64
  ret i64 0
}

; per lane in a vector
define i64 @ptrtoint_poison_vector() {
  %x = alloca i64
  %v0 = insertelement <2 x ptr> poison, ptr %x, i32 0
  %vi = ptrtoint <2 x ptr> %v0 to <2 x i64>
  %e = extractelement <2 x i64> %vi, i32 0
  %xi = ptrtoint ptr %x to i64
  %eq = icmp eq i64 %e, %xi
  %r = zext i1 %eq to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_ptrtoint_poison_i64 = private unnamed_addr constant [30 x i8] c"ptrtoint_poison_i64() = %lld\0A\00"
@fmt_ptrtoint_poison_i32 = private unnamed_addr constant [30 x i8] c"ptrtoint_poison_i32() = %lld\0A\00"
@fmt_ptrtoint_uninit_load = private unnamed_addr constant [31 x i8] c"ptrtoint_uninit_load() = %lld\0A\00"
@fmt_ptrtoint_poison_vector = private unnamed_addr constant [33 x i8] c"ptrtoint_poison_vector() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @ptrtoint_poison_i64()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_ptrtoint_poison_i64, i64 %v0)
  %v1 = call i64 @ptrtoint_poison_i32()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_ptrtoint_poison_i32, i64 %v1)
  %v2 = call i64 @ptrtoint_uninit_load()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_ptrtoint_uninit_load, i64 %v2)
  %v3 = call i64 @ptrtoint_poison_vector()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_ptrtoint_poison_vector, i64 %v3)
  ret i32 0
}

; ASSERT EQ: i64 0 = call i64 @ptrtoint_poison_i64()
; ASSERT EQ: i64 0 = call i64 @ptrtoint_poison_i32()
; ASSERT EQ: i64 0 = call i64 @ptrtoint_uninit_load()
; ASSERT EQ: i64 1 = call i64 @ptrtoint_poison_vector()
