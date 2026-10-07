; inttoptr of poison.
;
; LangRef: poison propagates through inttoptr -- `inttoptr iN poison to ptr`
; is poison.  Vellvm used to read the poison operand as the integer 0 and
; return a (non-poison) pointer at address 0 with wildcard provenance.
;
; That old answer is one of the values a frozen poison pointer may take, so
; no deterministic output tells the two apart.  These tests check that the
; poison flows through without trapping, and they discard or mask the
; arbitrary bits so the output stays comparable with a native run.

; the poison result, frozen, converted back, and masked to a fixed value
define i64 @inttoptr_poison() {
  %p = inttoptr i64 poison to ptr
  %f = freeze ptr %p
  %i = ptrtoint ptr %f to i64
  %z = and i64 %i, 0
  ret i64 %z
}

; poison survives the round trip back through ptrtoint
define i64 @inttoptr_ptrtoint_poison() {
  %p = inttoptr i32 poison to ptr
  %i = ptrtoint ptr %p to i64
  %f = freeze i64 %i
  %z = and i64 %f, 0
  ret i64 %z
}

; per lane in a vector: the defined lane is unaffected by the poison one
define i64 @inttoptr_poison_vector() {
  %v = insertelement <2 x i64> poison, i64 4096, i32 0
  %vp = inttoptr <2 x i64> %v to <2 x ptr>
  %e = extractelement <2 x ptr> %vp, i32 0
  %r = ptrtoint ptr %e to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_inttoptr_poison = private unnamed_addr constant [26 x i8] c"inttoptr_poison() = %lld\0A\00"
@fmt_inttoptr_ptrtoint_poison = private unnamed_addr constant [35 x i8] c"inttoptr_ptrtoint_poison() = %lld\0A\00"
@fmt_inttoptr_poison_vector = private unnamed_addr constant [33 x i8] c"inttoptr_poison_vector() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @inttoptr_poison()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_inttoptr_poison, i64 %v0)
  %v1 = call i64 @inttoptr_ptrtoint_poison()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_inttoptr_ptrtoint_poison, i64 %v1)
  %v2 = call i64 @inttoptr_poison_vector()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_inttoptr_poison_vector, i64 %v2)
  ret i32 0
}

; ASSERT EQ: i64 0    = call i64 @inttoptr_poison()
; ASSERT EQ: i64 0    = call i64 @inttoptr_ptrtoint_poison()
; ASSERT EQ: i64 4096 = call i64 @inttoptr_poison_vector()
