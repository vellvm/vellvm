; icmp on pointers.
;
; LangRef ('icmp'): "If the operands are pointer typed, the pointer values
; are compared as if they were integers" -- i.e. their addresses, at the
; pointer's address width (64 bits here).  So every predicate is defined on
; pointers:
;   - eq/ne compare addresses, ignoring provenance;
;   - ult/ule/ugt/uge read the address as an unsigned 64-bit integer;
;   - slt/sle/sgt/sge read it as a signed 64-bit integer, so an address with
;     the top bit set orders *below* null;
;   - samesign gives poison when the addresses' sign bits differ.
;
; Every expected value here is independent of where the allocator puts
; things, so the file can be run natively and diffed against clang: operands
; are either the same object at known offsets, null, or addresses made up
; with inttoptr (never dereferenced).  The one layout assumption is that real
; objects live at addresses that are non-zero and have the top bit clear,
; which holds for user space on every 64-bit target.
;
; Results are packed in decimal so a wrong one can be read off:
;   @eq2       eq ne            e.g.   10 = equal
;   @unsigned4 ult ule ugt uge  e.g. 1100 = below,  11 = above, 101 = equal
;   @signed4   slt sle sgt sge  (the same)

@g = global [4 x i64] zeroinitializer
@h = global i64 0

define i64 @eq2(ptr %a, ptr %b) {
  %eq = icmp eq ptr %a, %b
  %ne = icmp ne ptr %a, %b
  %eq.z = zext i1 %eq to i64
  %ne.z = zext i1 %ne to i64
  %t = mul i64 %eq.z, 10
  %r = add i64 %t, %ne.z
  ret i64 %r
}

define i64 @unsigned4(ptr %a, ptr %b) {
  %lt = icmp ult ptr %a, %b
  %le = icmp ule ptr %a, %b
  %gt = icmp ugt ptr %a, %b
  %ge = icmp uge ptr %a, %b
  %lt.z = zext i1 %lt to i64
  %le.z = zext i1 %le to i64
  %gt.z = zext i1 %gt to i64
  %ge.z = zext i1 %ge to i64
  %t0 = mul i64 %lt.z, 1000
  %t1 = mul i64 %le.z, 100
  %t2 = mul i64 %gt.z, 10
  %s0 = add i64 %t0, %t1
  %s1 = add i64 %s0, %t2
  %r = add i64 %s1, %ge.z
  ret i64 %r
}

define i64 @signed4(ptr %a, ptr %b) {
  %lt = icmp slt ptr %a, %b
  %le = icmp sle ptr %a, %b
  %gt = icmp sgt ptr %a, %b
  %ge = icmp sge ptr %a, %b
  %lt.z = zext i1 %lt to i64
  %le.z = zext i1 %le to i64
  %gt.z = zext i1 %gt to i64
  %ge.z = zext i1 %ge to i64
  %t0 = mul i64 %lt.z, 1000
  %t1 = mul i64 %le.z, 100
  %t2 = mul i64 %gt.z, 10
  %s0 = add i64 %t0, %t1
  %s1 = add i64 %s0, %t2
  %r = add i64 %s1, %ge.z
  ret i64 %r
}

; ---------------------------------------------------------------- equality

; a pointer equals itself
define i64 @eq_same_alloca() {
  %p = alloca i64
  %r = call i64 @eq2(ptr %p, ptr %p)
  ret i64 %r
}

; two live allocations are at different addresses
define i64 @eq_distinct_allocas() {
  %p = alloca i64
  %q = alloca i64
  %r = call i64 @eq2(ptr %p, ptr %q)
  ret i64 %r
}

define i64 @eq_null_null() {
  %r = call i64 @eq2(ptr null, ptr null)
  ret i64 %r
}

; no allocation is at address 0
define i64 @eq_alloca_null() {
  %p = alloca i64
  %r = call i64 @eq2(ptr %p, ptr null)
  ret i64 %r
}

define i64 @eq_global_null() {
  %r = call i64 @eq2(ptr @g, ptr null)
  ret i64 %r
}

define i64 @eq_distinct_globals() {
  %r = call i64 @eq2(ptr @g, ptr @h)
  ret i64 %r
}

define i64 @eq_global_alloca() {
  %p = alloca i64
  %r = call i64 @eq2(ptr @h, ptr %p)
  ret i64 %r
}

; two different routes to the same element
define i64 @eq_same_element() {
  %a = getelementptr [4 x i64], ptr @g, i64 0, i64 2
  %b = getelementptr i8, ptr @g, i64 16
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @eq_different_elements() {
  %a = getelementptr [4 x i64], ptr @g, i64 0, i64 2
  %b = getelementptr [4 x i64], ptr @g, i64 0, i64 3
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @eq_function_same() {
  %r = call i64 @eq2(ptr @eq2, ptr @eq2)
  ret i64 %r
}

define i64 @eq_function_distinct() {
  %r = call i64 @eq2(ptr @eq2, ptr @signed4)
  ret i64 %r
}

define i64 @eq_function_null() {
  %r = call i64 @eq2(ptr @eq2, ptr null)
  ret i64 %r
}

; equality is on the address: a pointer rebuilt from its integer address
; compares equal to the original
define i64 @eq_int_round_trip() {
  %p = alloca i64
  %i = ptrtoint ptr %p to i64
  %q = inttoptr i64 %i to ptr
  %r = call i64 @eq2(ptr %p, ptr %q)
  ret i64 %r
}

; ... and so does one that went through memory
define i64 @eq_through_memory() {
  %p = alloca i64
  %s = alloca ptr
  store ptr %p, ptr %s
  %q = load ptr, ptr %s
  %r = call i64 @eq2(ptr %p, ptr %q)
  ret i64 %r
}

define i64 @eq_inttoptr_same() {
  %a = inttoptr i64 4096 to ptr
  %b = inttoptr i64 4096 to ptr
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @eq_inttoptr_distinct() {
  %a = inttoptr i64 4096 to ptr
  %b = inttoptr i64 4097 to ptr
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

; inttoptr 0 is the null address
define i64 @eq_inttoptr_zero_null() {
  %a = inttoptr i64 0 to ptr
  %r = call i64 @eq2(ptr %a, ptr null)
  ret i64 %r
}

; -------------------------------------------- ordering within one object
; Addresses here are small-and-positive as far as the sign bit goes, so the
; signed and unsigned orders agree.

define i64 @unsigned_same() {
  %p = alloca i64
  %r = call i64 @unsigned4(ptr %p, ptr %p)
  ret i64 %r
}

define i64 @signed_same() {
  %p = alloca i64
  %r = call i64 @signed4(ptr %p, ptr %p)
  ret i64 %r
}

define i64 @unsigned_below_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %r = call i64 @unsigned4(ptr %p, ptr %q)
  ret i64 %r
}

define i64 @unsigned_above_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %r = call i64 @unsigned4(ptr %q, ptr %p)
  ret i64 %r
}

define i64 @signed_below_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %r = call i64 @signed4(ptr %p, ptr %q)
  ret i64 %r
}

define i64 @signed_above_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %r = call i64 @signed4(ptr %q, ptr %p)
  ret i64 %r
}

; adjacent bytes
define i64 @unsigned_below_in_global() {
  %a = getelementptr i8, ptr @g, i64 7
  %b = getelementptr i8, ptr @g, i64 8
  %r = call i64 @unsigned4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @signed_below_in_global() {
  %a = getelementptr i8, ptr @g, i64 7
  %b = getelementptr i8, ptr @g, i64 8
  %r = call i64 @signed4(ptr %a, ptr %b)
  ret i64 %r
}

; the one-past-the-end pointer is above every element
define i64 @unsigned_one_past_end() {
  %p = alloca [4 x i64]
  %last = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %end = getelementptr [4 x i64], ptr %p, i64 1
  %r = call i64 @unsigned4(ptr %end, ptr %last)
  ret i64 %r
}

define i64 @signed_one_past_end() {
  %p = alloca [4 x i64]
  %last = getelementptr [4 x i64], ptr %p, i64 0, i64 3
  %end = getelementptr [4 x i64], ptr %p, i64 1
  %r = call i64 @signed4(ptr %end, ptr %last)
  ret i64 %r
}

; a (non-inbounds) pointer below the object is below it
define i64 @unsigned_before_start() {
  %p = alloca i64
  %q = getelementptr i8, ptr %p, i64 -1
  %r = call i64 @unsigned4(ptr %q, ptr %p)
  ret i64 %r
}

define i64 @signed_before_start() {
  %p = alloca i64
  %q = getelementptr i8, ptr %p, i64 -1
  %r = call i64 @signed4(ptr %q, ptr %p)
  ret i64 %r
}

; ------------------------------------------------------ ordering vs. null

define i64 @unsigned_null_null() {
  %r = call i64 @unsigned4(ptr null, ptr null)
  ret i64 %r
}

define i64 @signed_null_null() {
  %r = call i64 @signed4(ptr null, ptr null)
  ret i64 %r
}

define i64 @unsigned_null_alloca() {
  %p = alloca i64
  %r = call i64 @unsigned4(ptr null, ptr %p)
  ret i64 %r
}

define i64 @signed_null_alloca() {
  %p = alloca i64
  %r = call i64 @signed4(ptr null, ptr %p)
  ret i64 %r
}

define i64 @unsigned_global_null() {
  %r = call i64 @unsigned4(ptr @g, ptr null)
  ret i64 %r
}

define i64 @signed_global_null() {
  %r = call i64 @signed4(ptr @g, ptr null)
  ret i64 %r
}

; ------------------------------------------- ordering of made-up addresses
; Here the two orders come apart.

define i64 @unsigned_small() {
  %a = inttoptr i64 1 to ptr
  %b = inttoptr i64 2 to ptr
  %r = call i64 @unsigned4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @signed_small() {
  %a = inttoptr i64 1 to ptr
  %b = inttoptr i64 2 to ptr
  %r = call i64 @signed4(ptr %a, ptr %b)
  ret i64 %r
}

; address 2^64-1 is the largest unsigned ...
define i64 @unsigned_max_vs_one() {
  %a = inttoptr i64 -1 to ptr
  %b = inttoptr i64 1 to ptr
  %r = call i64 @unsigned4(ptr %a, ptr %b)
  ret i64 %r
}

; ... and, read as -1, below 1
define i64 @signed_max_vs_one() {
  %a = inttoptr i64 -1 to ptr
  %b = inttoptr i64 1 to ptr
  %r = call i64 @signed4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @unsigned_max_vs_null() {
  %a = inttoptr i64 -1 to ptr
  %r = call i64 @unsigned4(ptr %a, ptr null)
  ret i64 %r
}

define i64 @signed_max_vs_null() {
  %a = inttoptr i64 -1 to ptr
  %r = call i64 @signed4(ptr %a, ptr null)
  ret i64 %r
}

; the sign boundary: 2^63 against 2^63-1
define i64 @unsigned_sign_boundary() {
  %a = inttoptr i64 9223372036854775808 to ptr
  %b = inttoptr i64 9223372036854775807 to ptr
  %r = call i64 @unsigned4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @signed_sign_boundary() {
  %a = inttoptr i64 9223372036854775808 to ptr
  %b = inttoptr i64 9223372036854775807 to ptr
  %r = call i64 @signed4(ptr %a, ptr %b)
  ret i64 %r
}

; both with the top bit set: the orders agree again
define i64 @unsigned_both_high() {
  %a = inttoptr i64 -1 to ptr
  %b = inttoptr i64 -2 to ptr
  %r = call i64 @unsigned4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @signed_both_high() {
  %a = inttoptr i64 -1 to ptr
  %b = inttoptr i64 -2 to ptr
  %r = call i64 @signed4(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @eq_max_vs_max() {
  %a = inttoptr i64 -1 to ptr
  %b = inttoptr i64 18446744073709551615 to ptr
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

; a real object against a top-bit-set address
define i64 @unsigned_alloca_vs_high() {
  %p = alloca i64
  %b = inttoptr i64 -4096 to ptr
  %r = call i64 @unsigned4(ptr %p, ptr %b)
  ret i64 %r
}

define i64 @signed_alloca_vs_high() {
  %p = alloca i64
  %b = inttoptr i64 -4096 to ptr
  %r = call i64 @signed4(ptr %p, ptr %b)
  ret i64 %r
}

; getelementptr (without inbounds/nuw) wraps at the address width: null - 1
; is address 2^64-1
define i64 @eq_gep_wraps_below_null() {
  %a = getelementptr i8, ptr null, i64 -1
  %b = inttoptr i64 -1 to ptr
  %r = call i64 @eq2(ptr %a, ptr %b)
  ret i64 %r
}

define i64 @unsigned_gep_wraps_below_null() {
  %a = getelementptr i8, ptr null, i64 -1
  %r = call i64 @unsigned4(ptr %a, ptr null)
  ret i64 %r
}

define i64 @signed_gep_wraps_below_null() {
  %a = getelementptr i8, ptr null, i64 -1
  %r = call i64 @signed4(ptr %a, ptr null)
  ret i64 %r
}

; ... and 2^64-1 + 1 wraps back to null
define i64 @eq_gep_wraps_to_null() {
  %a = inttoptr i64 -1 to ptr
  %b = getelementptr i8, ptr %a, i64 1
  %r = call i64 @eq2(ptr %b, ptr null)
  ret i64 %r
}

; --------------------------------------------------------------- samesign

define i1 @samesign_ult(i64 %x, i64 %y) {
  %a = inttoptr i64 %x to ptr
  %b = inttoptr i64 %y to ptr
  %r = icmp samesign ult ptr %a, %b
  ret i1 %r
}

define i1 @samesign_slt(i64 %x, i64 %y) {
  %a = inttoptr i64 %x to ptr
  %b = inttoptr i64 %y to ptr
  %r = icmp samesign slt ptr %a, %b
  ret i1 %r
}

define i1 @samesign_eq(i64 %x, i64 %y) {
  %a = inttoptr i64 %x to ptr
  %b = inttoptr i64 %y to ptr
  %r = icmp samesign eq ptr %a, %b
  ret i1 %r
}

; equal signs: samesign changes nothing
define i64 @samesign_ult_both_low() {
  %c = call i1 @samesign_ult(i64 1, i64 2)
  %r = zext i1 %c to i64
  ret i64 %r
}

define i64 @samesign_ult_both_high() {
  %c = call i1 @samesign_ult(i64 -2, i64 -1)
  %r = zext i1 %c to i64
  ret i64 %r
}

define i64 @samesign_slt_both_high() {
  %c = call i1 @samesign_slt(i64 -2, i64 -1)
  %r = zext i1 %c to i64
  ret i64 %r
}

define i64 @samesign_eq_both_high() {
  %c = call i1 @samesign_eq(i64 -1, i64 -1)
  %r = zext i1 %c to i64
  ret i64 %r
}

; real objects and null all have the sign bit clear
define i64 @samesign_ult_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 1
  %c = icmp samesign ult ptr %p, %q
  %r = zext i1 %c to i64
  ret i64 %r
}

define i64 @samesign_ugt_alloca_null() {
  %p = alloca i64
  %c = icmp samesign ugt ptr %p, null
  %r = zext i1 %c to i64
  ret i64 %r
}

; different signs: poison (not run natively -- there is nothing to print)
; ASSERT EQ: i1 poison = call i1 @samesign_ult(i64 -1, i64 1)
; ASSERT EQ: i1 poison = call i1 @samesign_ult(i64 1, i64 -1)
; ASSERT EQ: i1 poison = call i1 @samesign_slt(i64 -1, i64 1)
; ASSERT EQ: i1 poison = call i1 @samesign_eq(i64 -1, i64 1)
; ASSERT EQ: i1 poison = call i1 @samesign_eq(i64 9223372036854775807, i64 9223372036854775808)
; ASSERT EQ: i1 1 = call i1 @samesign_ult(i64 0, i64 9223372036854775807)
; ASSERT EQ: i1 0 = call i1 @samesign_slt(i64 -1, i64 -9223372036854775808)

; ----------------------------------------------------------------- poison

define i1 @poison_eq() {
  %p = alloca i64
  %r = icmp eq ptr %p, poison
  ret i1 %r
}

define i1 @poison_ult() {
  %r = icmp ult ptr poison, null
  ret i1 %r
}

define i1 @poison_slt() {
  %r = icmp slt ptr null, poison
  ret i1 %r
}

; ASSERT EQ: i1 poison = call i1 @poison_eq()
; ASSERT EQ: i1 poison = call i1 @poison_ult()
; ASSERT EQ: i1 poison = call i1 @poison_slt()

; ---------------------------------------------------------------- vectors
; lane by lane; lane 0 is the high decimal digit

define i64 @pack2(<2 x i1> %c) {
  %c0 = extractelement <2 x i1> %c, i32 0
  %c1 = extractelement <2 x i1> %c, i32 1
  %z0 = zext i1 %c0 to i64
  %z1 = zext i1 %c1 to i64
  %t = mul i64 %z0, 10
  %r = add i64 %t, %z1
  ret i64 %r
}

define i64 @vector_eq() {
  %p = alloca i64
  %a0 = insertelement <2 x ptr> poison, ptr %p, i32 0
  %a = insertelement <2 x ptr> %a0, ptr %p, i32 1
  %b0 = insertelement <2 x ptr> poison, ptr %p, i32 0
  %b = insertelement <2 x ptr> %b0, ptr null, i32 1
  %c = icmp eq <2 x ptr> %a, %b
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

define i64 @vector_ult() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 1
  %a0 = insertelement <2 x ptr> poison, ptr %p, i32 0
  %a = insertelement <2 x ptr> %a0, ptr %q, i32 1
  %b0 = insertelement <2 x ptr> poison, ptr %q, i32 0
  %b = insertelement <2 x ptr> %b0, ptr %p, i32 1
  %c = icmp ult <2 x ptr> %a, %b
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

; lane 0: -1 vs 1; lane 1: 1 vs -1
define i64 @vector_ugt_high() {
  %a = inttoptr <2 x i64> <i64 -1, i64 1> to <2 x ptr>
  %b = inttoptr <2 x i64> <i64 1, i64 -1> to <2 x ptr>
  %c = icmp ugt <2 x ptr> %a, %b
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

define i64 @vector_sgt_high() {
  %a = inttoptr <2 x i64> <i64 -1, i64 1> to <2 x ptr>
  %b = inttoptr <2 x i64> <i64 1, i64 -1> to <2 x ptr>
  %c = icmp sgt <2 x ptr> %a, %b
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

define i64 @vector_slt_in_alloca() {
  %p = alloca [4 x i64]
  %q = getelementptr [4 x i64], ptr %p, i64 0, i64 1
  %a0 = insertelement <2 x ptr> poison, ptr %p, i32 0
  %a = insertelement <2 x ptr> %a0, ptr %q, i32 1
  %b0 = insertelement <2 x ptr> poison, ptr %q, i32 0
  %b = insertelement <2 x ptr> %b0, ptr %p, i32 1
  %c = icmp slt <2 x ptr> %a, %b
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

; a constant null vector
define i64 @vector_ne_zeroinitializer() {
  %p = alloca i64
  %a0 = insertelement <2 x ptr> poison, ptr %p, i32 0
  %a = insertelement <2 x ptr> %a0, ptr null, i32 1
  %c = icmp ne <2 x ptr> %a, zeroinitializer
  %r = call i64 @pack2(<2 x i1> %c)
  ret i64 %r
}

; ------------------------------------------------- comparisons in control
; the idiomatic uses: a cursor walked to an end pointer

define i64 @loop_ne_end() {
entry:
  %arr = alloca [4 x i64]
  store [4 x i64] [i64 1, i64 2, i64 3, i64 4], ptr %arr
  %end = getelementptr [4 x i64], ptr %arr, i64 1
  br label %loop
loop:
  %cur = phi ptr [ %arr, %entry ], [ %next, %loop ]
  %acc = phi i64 [ 0, %entry ], [ %acc1, %loop ]
  %v = load i64, ptr %cur
  %acc1 = add i64 %acc, %v
  %next = getelementptr i64, ptr %cur, i64 1
  %more = icmp ne ptr %next, %end
  br i1 %more, label %loop, label %done
done:
  ret i64 %acc1
}

define i64 @loop_ult_end() {
entry:
  %arr = alloca [4 x i64]
  store [4 x i64] [i64 1, i64 2, i64 3, i64 4], ptr %arr
  %end = getelementptr [4 x i64], ptr %arr, i64 1
  br label %loop
loop:
  %cur = phi ptr [ %arr, %entry ], [ %next, %loop ]
  %acc = phi i64 [ 0, %entry ], [ %acc1, %loop ]
  %v = load i64, ptr %cur
  %acc1 = add i64 %acc, %v
  %next = getelementptr i64, ptr %cur, i64 1
  %more = icmp ult ptr %next, %end
  br i1 %more, label %loop, label %done
done:
  ret i64 %acc1
}

; walking down with a signed comparison
define i64 @loop_sge_start() {
entry:
  %arr = alloca [4 x i64]
  store [4 x i64] [i64 1, i64 2, i64 3, i64 4], ptr %arr
  %last = getelementptr [4 x i64], ptr %arr, i64 0, i64 3
  br label %loop
loop:
  %cur = phi ptr [ %last, %entry ], [ %prev, %loop ]
  %acc = phi i64 [ 0, %entry ], [ %acc1, %loop ]
  %v = load i64, ptr %cur
  %acc1 = add i64 %acc, %v
  %prev = getelementptr i64, ptr %cur, i64 -1
  %more = icmp sge ptr %prev, %arr
  br i1 %more, label %loop, label %done
done:
  ret i64 %acc1
}

; select the lower of two pointers and read through it
define i64 @select_min_pointer() {
  %arr = alloca [2 x i64]
  store [2 x i64] [i64 7, i64 9], ptr %arr
  %hi = getelementptr [2 x i64], ptr %arr, i64 0, i64 1
  %c = icmp ult ptr %hi, %arr
  %m = select i1 %c, ptr %hi, ptr %arr
  %r = load i64, ptr %m
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_eq_same_alloca = private unnamed_addr constant [25 x i8] c"eq_same_alloca() = %lld\0A\00"
@fmt_eq_distinct_allocas = private unnamed_addr constant [30 x i8] c"eq_distinct_allocas() = %lld\0A\00"
@fmt_eq_null_null = private unnamed_addr constant [23 x i8] c"eq_null_null() = %lld\0A\00"
@fmt_eq_alloca_null = private unnamed_addr constant [25 x i8] c"eq_alloca_null() = %lld\0A\00"
@fmt_eq_global_null = private unnamed_addr constant [25 x i8] c"eq_global_null() = %lld\0A\00"
@fmt_eq_distinct_globals = private unnamed_addr constant [30 x i8] c"eq_distinct_globals() = %lld\0A\00"
@fmt_eq_global_alloca = private unnamed_addr constant [27 x i8] c"eq_global_alloca() = %lld\0A\00"
@fmt_eq_same_element = private unnamed_addr constant [26 x i8] c"eq_same_element() = %lld\0A\00"
@fmt_eq_different_elements = private unnamed_addr constant [32 x i8] c"eq_different_elements() = %lld\0A\00"
@fmt_eq_function_same = private unnamed_addr constant [27 x i8] c"eq_function_same() = %lld\0A\00"
@fmt_eq_function_distinct = private unnamed_addr constant [31 x i8] c"eq_function_distinct() = %lld\0A\00"
@fmt_eq_function_null = private unnamed_addr constant [27 x i8] c"eq_function_null() = %lld\0A\00"
@fmt_eq_int_round_trip = private unnamed_addr constant [28 x i8] c"eq_int_round_trip() = %lld\0A\00"
@fmt_eq_through_memory = private unnamed_addr constant [28 x i8] c"eq_through_memory() = %lld\0A\00"
@fmt_eq_inttoptr_same = private unnamed_addr constant [27 x i8] c"eq_inttoptr_same() = %lld\0A\00"
@fmt_eq_inttoptr_distinct = private unnamed_addr constant [31 x i8] c"eq_inttoptr_distinct() = %lld\0A\00"
@fmt_eq_inttoptr_zero_null = private unnamed_addr constant [32 x i8] c"eq_inttoptr_zero_null() = %lld\0A\00"
@fmt_unsigned_same = private unnamed_addr constant [24 x i8] c"unsigned_same() = %lld\0A\00"
@fmt_signed_same = private unnamed_addr constant [22 x i8] c"signed_same() = %lld\0A\00"
@fmt_unsigned_below_in_alloca = private unnamed_addr constant [35 x i8] c"unsigned_below_in_alloca() = %lld\0A\00"
@fmt_unsigned_above_in_alloca = private unnamed_addr constant [35 x i8] c"unsigned_above_in_alloca() = %lld\0A\00"
@fmt_signed_below_in_alloca = private unnamed_addr constant [33 x i8] c"signed_below_in_alloca() = %lld\0A\00"
@fmt_signed_above_in_alloca = private unnamed_addr constant [33 x i8] c"signed_above_in_alloca() = %lld\0A\00"
@fmt_unsigned_below_in_global = private unnamed_addr constant [35 x i8] c"unsigned_below_in_global() = %lld\0A\00"
@fmt_signed_below_in_global = private unnamed_addr constant [33 x i8] c"signed_below_in_global() = %lld\0A\00"
@fmt_unsigned_one_past_end = private unnamed_addr constant [32 x i8] c"unsigned_one_past_end() = %lld\0A\00"
@fmt_signed_one_past_end = private unnamed_addr constant [30 x i8] c"signed_one_past_end() = %lld\0A\00"
@fmt_unsigned_before_start = private unnamed_addr constant [32 x i8] c"unsigned_before_start() = %lld\0A\00"
@fmt_signed_before_start = private unnamed_addr constant [30 x i8] c"signed_before_start() = %lld\0A\00"
@fmt_unsigned_null_null = private unnamed_addr constant [29 x i8] c"unsigned_null_null() = %lld\0A\00"
@fmt_signed_null_null = private unnamed_addr constant [27 x i8] c"signed_null_null() = %lld\0A\00"
@fmt_unsigned_null_alloca = private unnamed_addr constant [31 x i8] c"unsigned_null_alloca() = %lld\0A\00"
@fmt_signed_null_alloca = private unnamed_addr constant [29 x i8] c"signed_null_alloca() = %lld\0A\00"
@fmt_unsigned_global_null = private unnamed_addr constant [31 x i8] c"unsigned_global_null() = %lld\0A\00"
@fmt_signed_global_null = private unnamed_addr constant [29 x i8] c"signed_global_null() = %lld\0A\00"
@fmt_unsigned_small = private unnamed_addr constant [25 x i8] c"unsigned_small() = %lld\0A\00"
@fmt_signed_small = private unnamed_addr constant [23 x i8] c"signed_small() = %lld\0A\00"
@fmt_unsigned_max_vs_one = private unnamed_addr constant [30 x i8] c"unsigned_max_vs_one() = %lld\0A\00"
@fmt_signed_max_vs_one = private unnamed_addr constant [28 x i8] c"signed_max_vs_one() = %lld\0A\00"
@fmt_unsigned_max_vs_null = private unnamed_addr constant [31 x i8] c"unsigned_max_vs_null() = %lld\0A\00"
@fmt_signed_max_vs_null = private unnamed_addr constant [29 x i8] c"signed_max_vs_null() = %lld\0A\00"
@fmt_unsigned_sign_boundary = private unnamed_addr constant [33 x i8] c"unsigned_sign_boundary() = %lld\0A\00"
@fmt_signed_sign_boundary = private unnamed_addr constant [31 x i8] c"signed_sign_boundary() = %lld\0A\00"
@fmt_unsigned_both_high = private unnamed_addr constant [29 x i8] c"unsigned_both_high() = %lld\0A\00"
@fmt_signed_both_high = private unnamed_addr constant [27 x i8] c"signed_both_high() = %lld\0A\00"
@fmt_eq_max_vs_max = private unnamed_addr constant [24 x i8] c"eq_max_vs_max() = %lld\0A\00"
@fmt_unsigned_alloca_vs_high = private unnamed_addr constant [34 x i8] c"unsigned_alloca_vs_high() = %lld\0A\00"
@fmt_signed_alloca_vs_high = private unnamed_addr constant [32 x i8] c"signed_alloca_vs_high() = %lld\0A\00"
@fmt_eq_gep_wraps_below_null = private unnamed_addr constant [34 x i8] c"eq_gep_wraps_below_null() = %lld\0A\00"
@fmt_unsigned_gep_wraps_below_null = private unnamed_addr constant [40 x i8] c"unsigned_gep_wraps_below_null() = %lld\0A\00"
@fmt_signed_gep_wraps_below_null = private unnamed_addr constant [38 x i8] c"signed_gep_wraps_below_null() = %lld\0A\00"
@fmt_eq_gep_wraps_to_null = private unnamed_addr constant [31 x i8] c"eq_gep_wraps_to_null() = %lld\0A\00"
@fmt_samesign_ult_both_low = private unnamed_addr constant [32 x i8] c"samesign_ult_both_low() = %lld\0A\00"
@fmt_samesign_ult_both_high = private unnamed_addr constant [33 x i8] c"samesign_ult_both_high() = %lld\0A\00"
@fmt_samesign_slt_both_high = private unnamed_addr constant [33 x i8] c"samesign_slt_both_high() = %lld\0A\00"
@fmt_samesign_eq_both_high = private unnamed_addr constant [32 x i8] c"samesign_eq_both_high() = %lld\0A\00"
@fmt_samesign_ult_in_alloca = private unnamed_addr constant [33 x i8] c"samesign_ult_in_alloca() = %lld\0A\00"
@fmt_samesign_ugt_alloca_null = private unnamed_addr constant [35 x i8] c"samesign_ugt_alloca_null() = %lld\0A\00"
@fmt_vector_eq = private unnamed_addr constant [20 x i8] c"vector_eq() = %lld\0A\00"
@fmt_vector_ult = private unnamed_addr constant [21 x i8] c"vector_ult() = %lld\0A\00"
@fmt_vector_ugt_high = private unnamed_addr constant [26 x i8] c"vector_ugt_high() = %lld\0A\00"
@fmt_vector_sgt_high = private unnamed_addr constant [26 x i8] c"vector_sgt_high() = %lld\0A\00"
@fmt_vector_slt_in_alloca = private unnamed_addr constant [31 x i8] c"vector_slt_in_alloca() = %lld\0A\00"
@fmt_vector_ne_zeroinitializer = private unnamed_addr constant [36 x i8] c"vector_ne_zeroinitializer() = %lld\0A\00"
@fmt_loop_ne_end = private unnamed_addr constant [22 x i8] c"loop_ne_end() = %lld\0A\00"
@fmt_loop_ult_end = private unnamed_addr constant [23 x i8] c"loop_ult_end() = %lld\0A\00"
@fmt_loop_sge_start = private unnamed_addr constant [25 x i8] c"loop_sge_start() = %lld\0A\00"
@fmt_select_min_pointer = private unnamed_addr constant [29 x i8] c"select_min_pointer() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @eq_same_alloca()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_eq_same_alloca, i64 %v0)
  %v1 = call i64 @eq_distinct_allocas()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_eq_distinct_allocas, i64 %v1)
  %v2 = call i64 @eq_null_null()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_eq_null_null, i64 %v2)
  %v3 = call i64 @eq_alloca_null()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_eq_alloca_null, i64 %v3)
  %v4 = call i64 @eq_global_null()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_eq_global_null, i64 %v4)
  %v5 = call i64 @eq_distinct_globals()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_eq_distinct_globals, i64 %v5)
  %v6 = call i64 @eq_global_alloca()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_eq_global_alloca, i64 %v6)
  %v7 = call i64 @eq_same_element()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_eq_same_element, i64 %v7)
  %v8 = call i64 @eq_different_elements()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_eq_different_elements, i64 %v8)
  %v9 = call i64 @eq_function_same()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_eq_function_same, i64 %v9)
  %v10 = call i64 @eq_function_distinct()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_eq_function_distinct, i64 %v10)
  %v11 = call i64 @eq_function_null()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_eq_function_null, i64 %v11)
  %v12 = call i64 @eq_int_round_trip()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_eq_int_round_trip, i64 %v12)
  %v13 = call i64 @eq_through_memory()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_eq_through_memory, i64 %v13)
  %v14 = call i64 @eq_inttoptr_same()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_eq_inttoptr_same, i64 %v14)
  %v15 = call i64 @eq_inttoptr_distinct()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_eq_inttoptr_distinct, i64 %v15)
  %v16 = call i64 @eq_inttoptr_zero_null()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_eq_inttoptr_zero_null, i64 %v16)
  %v17 = call i64 @unsigned_same()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_same, i64 %v17)
  %v18 = call i64 @signed_same()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_signed_same, i64 %v18)
  %v19 = call i64 @unsigned_below_in_alloca()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_below_in_alloca, i64 %v19)
  %v20 = call i64 @unsigned_above_in_alloca()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_above_in_alloca, i64 %v20)
  %v21 = call i64 @signed_below_in_alloca()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_signed_below_in_alloca, i64 %v21)
  %v22 = call i64 @signed_above_in_alloca()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_signed_above_in_alloca, i64 %v22)
  %v23 = call i64 @unsigned_below_in_global()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_below_in_global, i64 %v23)
  %v24 = call i64 @signed_below_in_global()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_signed_below_in_global, i64 %v24)
  %v25 = call i64 @unsigned_one_past_end()
  %p25 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_one_past_end, i64 %v25)
  %v26 = call i64 @signed_one_past_end()
  %p26 = call i32 (ptr, ...) @printf(ptr @fmt_signed_one_past_end, i64 %v26)
  %v27 = call i64 @unsigned_before_start()
  %p27 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_before_start, i64 %v27)
  %v28 = call i64 @signed_before_start()
  %p28 = call i32 (ptr, ...) @printf(ptr @fmt_signed_before_start, i64 %v28)
  %v29 = call i64 @unsigned_null_null()
  %p29 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_null_null, i64 %v29)
  %v30 = call i64 @signed_null_null()
  %p30 = call i32 (ptr, ...) @printf(ptr @fmt_signed_null_null, i64 %v30)
  %v31 = call i64 @unsigned_null_alloca()
  %p31 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_null_alloca, i64 %v31)
  %v32 = call i64 @signed_null_alloca()
  %p32 = call i32 (ptr, ...) @printf(ptr @fmt_signed_null_alloca, i64 %v32)
  %v33 = call i64 @unsigned_global_null()
  %p33 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_global_null, i64 %v33)
  %v34 = call i64 @signed_global_null()
  %p34 = call i32 (ptr, ...) @printf(ptr @fmt_signed_global_null, i64 %v34)
  %v35 = call i64 @unsigned_small()
  %p35 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_small, i64 %v35)
  %v36 = call i64 @signed_small()
  %p36 = call i32 (ptr, ...) @printf(ptr @fmt_signed_small, i64 %v36)
  %v37 = call i64 @unsigned_max_vs_one()
  %p37 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_max_vs_one, i64 %v37)
  %v38 = call i64 @signed_max_vs_one()
  %p38 = call i32 (ptr, ...) @printf(ptr @fmt_signed_max_vs_one, i64 %v38)
  %v39 = call i64 @unsigned_max_vs_null()
  %p39 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_max_vs_null, i64 %v39)
  %v40 = call i64 @signed_max_vs_null()
  %p40 = call i32 (ptr, ...) @printf(ptr @fmt_signed_max_vs_null, i64 %v40)
  %v41 = call i64 @unsigned_sign_boundary()
  %p41 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_sign_boundary, i64 %v41)
  %v42 = call i64 @signed_sign_boundary()
  %p42 = call i32 (ptr, ...) @printf(ptr @fmt_signed_sign_boundary, i64 %v42)
  %v43 = call i64 @unsigned_both_high()
  %p43 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_both_high, i64 %v43)
  %v44 = call i64 @signed_both_high()
  %p44 = call i32 (ptr, ...) @printf(ptr @fmt_signed_both_high, i64 %v44)
  %v45 = call i64 @eq_max_vs_max()
  %p45 = call i32 (ptr, ...) @printf(ptr @fmt_eq_max_vs_max, i64 %v45)
  %v46 = call i64 @unsigned_alloca_vs_high()
  %p46 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_alloca_vs_high, i64 %v46)
  %v47 = call i64 @signed_alloca_vs_high()
  %p47 = call i32 (ptr, ...) @printf(ptr @fmt_signed_alloca_vs_high, i64 %v47)
  %v48 = call i64 @eq_gep_wraps_below_null()
  %p48 = call i32 (ptr, ...) @printf(ptr @fmt_eq_gep_wraps_below_null, i64 %v48)
  %v49 = call i64 @unsigned_gep_wraps_below_null()
  %p49 = call i32 (ptr, ...) @printf(ptr @fmt_unsigned_gep_wraps_below_null, i64 %v49)
  %v50 = call i64 @signed_gep_wraps_below_null()
  %p50 = call i32 (ptr, ...) @printf(ptr @fmt_signed_gep_wraps_below_null, i64 %v50)
  %v51 = call i64 @eq_gep_wraps_to_null()
  %p51 = call i32 (ptr, ...) @printf(ptr @fmt_eq_gep_wraps_to_null, i64 %v51)
  %v52 = call i64 @samesign_ult_both_low()
  %p52 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_ult_both_low, i64 %v52)
  %v53 = call i64 @samesign_ult_both_high()
  %p53 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_ult_both_high, i64 %v53)
  %v54 = call i64 @samesign_slt_both_high()
  %p54 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_slt_both_high, i64 %v54)
  %v55 = call i64 @samesign_eq_both_high()
  %p55 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_eq_both_high, i64 %v55)
  %v56 = call i64 @samesign_ult_in_alloca()
  %p56 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_ult_in_alloca, i64 %v56)
  %v57 = call i64 @samesign_ugt_alloca_null()
  %p57 = call i32 (ptr, ...) @printf(ptr @fmt_samesign_ugt_alloca_null, i64 %v57)
  %v58 = call i64 @vector_eq()
  %p58 = call i32 (ptr, ...) @printf(ptr @fmt_vector_eq, i64 %v58)
  %v59 = call i64 @vector_ult()
  %p59 = call i32 (ptr, ...) @printf(ptr @fmt_vector_ult, i64 %v59)
  %v60 = call i64 @vector_ugt_high()
  %p60 = call i32 (ptr, ...) @printf(ptr @fmt_vector_ugt_high, i64 %v60)
  %v61 = call i64 @vector_sgt_high()
  %p61 = call i32 (ptr, ...) @printf(ptr @fmt_vector_sgt_high, i64 %v61)
  %v62 = call i64 @vector_slt_in_alloca()
  %p62 = call i32 (ptr, ...) @printf(ptr @fmt_vector_slt_in_alloca, i64 %v62)
  %v63 = call i64 @vector_ne_zeroinitializer()
  %p63 = call i32 (ptr, ...) @printf(ptr @fmt_vector_ne_zeroinitializer, i64 %v63)
  %v64 = call i64 @loop_ne_end()
  %p64 = call i32 (ptr, ...) @printf(ptr @fmt_loop_ne_end, i64 %v64)
  %v65 = call i64 @loop_ult_end()
  %p65 = call i32 (ptr, ...) @printf(ptr @fmt_loop_ult_end, i64 %v65)
  %v66 = call i64 @loop_sge_start()
  %p66 = call i32 (ptr, ...) @printf(ptr @fmt_loop_sge_start, i64 %v66)
  %v67 = call i64 @select_min_pointer()
  %p67 = call i32 (ptr, ...) @printf(ptr @fmt_select_min_pointer, i64 %v67)
  ret i32 0
}

; ASSERT EQ: i64 10   = call i64 @eq_same_alloca()
; ASSERT EQ: i64 1    = call i64 @eq_distinct_allocas()
; ASSERT EQ: i64 10   = call i64 @eq_null_null()
; ASSERT EQ: i64 1    = call i64 @eq_alloca_null()
; ASSERT EQ: i64 1    = call i64 @eq_global_null()
; ASSERT EQ: i64 1    = call i64 @eq_distinct_globals()
; ASSERT EQ: i64 1    = call i64 @eq_global_alloca()
; ASSERT EQ: i64 10   = call i64 @eq_same_element()
; ASSERT EQ: i64 1    = call i64 @eq_different_elements()
; ASSERT EQ: i64 10   = call i64 @eq_function_same()
; ASSERT EQ: i64 1    = call i64 @eq_function_distinct()
; ASSERT EQ: i64 1    = call i64 @eq_function_null()
; ASSERT EQ: i64 10   = call i64 @eq_int_round_trip()
; ASSERT EQ: i64 10   = call i64 @eq_through_memory()
; ASSERT EQ: i64 10   = call i64 @eq_inttoptr_same()
; ASSERT EQ: i64 1    = call i64 @eq_inttoptr_distinct()
; ASSERT EQ: i64 10   = call i64 @eq_inttoptr_zero_null()
; ASSERT EQ: i64 101  = call i64 @unsigned_same()
; ASSERT EQ: i64 101  = call i64 @signed_same()
; ASSERT EQ: i64 1100 = call i64 @unsigned_below_in_alloca()
; ASSERT EQ: i64 11   = call i64 @unsigned_above_in_alloca()
; ASSERT EQ: i64 1100 = call i64 @signed_below_in_alloca()
; ASSERT EQ: i64 11   = call i64 @signed_above_in_alloca()
; ASSERT EQ: i64 1100 = call i64 @unsigned_below_in_global()
; ASSERT EQ: i64 1100 = call i64 @signed_below_in_global()
; ASSERT EQ: i64 11   = call i64 @unsigned_one_past_end()
; ASSERT EQ: i64 11   = call i64 @signed_one_past_end()
; ASSERT EQ: i64 1100 = call i64 @unsigned_before_start()
; ASSERT EQ: i64 1100 = call i64 @signed_before_start()
; ASSERT EQ: i64 101  = call i64 @unsigned_null_null()
; ASSERT EQ: i64 101  = call i64 @signed_null_null()
; ASSERT EQ: i64 1100 = call i64 @unsigned_null_alloca()
; ASSERT EQ: i64 1100 = call i64 @signed_null_alloca()
; ASSERT EQ: i64 11   = call i64 @unsigned_global_null()
; ASSERT EQ: i64 11   = call i64 @signed_global_null()
; ASSERT EQ: i64 1100 = call i64 @unsigned_small()
; ASSERT EQ: i64 1100 = call i64 @signed_small()
; ASSERT EQ: i64 11   = call i64 @unsigned_max_vs_one()
; ASSERT EQ: i64 1100 = call i64 @signed_max_vs_one()
; ASSERT EQ: i64 11   = call i64 @unsigned_max_vs_null()
; ASSERT EQ: i64 1100 = call i64 @signed_max_vs_null()
; ASSERT EQ: i64 11   = call i64 @unsigned_sign_boundary()
; ASSERT EQ: i64 1100 = call i64 @signed_sign_boundary()
; ASSERT EQ: i64 11   = call i64 @unsigned_both_high()
; ASSERT EQ: i64 11   = call i64 @signed_both_high()
; ASSERT EQ: i64 10   = call i64 @eq_max_vs_max()
; ASSERT EQ: i64 1100 = call i64 @unsigned_alloca_vs_high()
; ASSERT EQ: i64 11   = call i64 @signed_alloca_vs_high()
; ASSERT EQ: i64 10   = call i64 @eq_gep_wraps_below_null()
; ASSERT EQ: i64 11   = call i64 @unsigned_gep_wraps_below_null()
; ASSERT EQ: i64 1100 = call i64 @signed_gep_wraps_below_null()
; ASSERT EQ: i64 10   = call i64 @eq_gep_wraps_to_null()
; ASSERT EQ: i64 1    = call i64 @samesign_ult_both_low()
; ASSERT EQ: i64 1    = call i64 @samesign_ult_both_high()
; ASSERT EQ: i64 1    = call i64 @samesign_slt_both_high()
; ASSERT EQ: i64 1    = call i64 @samesign_eq_both_high()
; ASSERT EQ: i64 1    = call i64 @samesign_ult_in_alloca()
; ASSERT EQ: i64 1    = call i64 @samesign_ugt_alloca_null()
; ASSERT EQ: i64 10   = call i64 @vector_eq()
; ASSERT EQ: i64 10   = call i64 @vector_ult()
; ASSERT EQ: i64 10   = call i64 @vector_ugt_high()
; ASSERT EQ: i64 1    = call i64 @vector_sgt_high()
; ASSERT EQ: i64 10   = call i64 @vector_slt_in_alloca()
; ASSERT EQ: i64 10   = call i64 @vector_ne_zeroinitializer()
; ASSERT EQ: i64 10   = call i64 @loop_ne_end()
; ASSERT EQ: i64 10   = call i64 @loop_ult_end()
; ASSERT EQ: i64 10   = call i64 @loop_sge_start()
; ASSERT EQ: i64 7    = call i64 @select_min_pointer()
