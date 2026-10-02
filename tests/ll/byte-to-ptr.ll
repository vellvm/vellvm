; Converting bytes that are not a pointer to a pointer.
;
; LangRef ('bitcast', value of byte type, ty2 a pointer type):
;   - if at least one bit of the value is poison, the result is poison;
;   - if all bits are from the same pointer, correctly ordered, the result
;     is that pointer;
;   - otherwise, the result is a pointer with the address given by the
;     integer value of the input, and without provenance.
; A load at a type other than the one stored follows the same rules
; ('load': "described in the bitcast section").
;
; Vellvm returns poison in the third case: [memory_bytes_to_pointer]
; (Semantics/MemoryBytes.v) falls back to [Pois], and [valid_pointer_bits]
; treats an integer bit like a poison bit.  The address-only tests below
; fail for that reason (the poison pointer then reaches ptrtoint); the
; round trip is a guard for the fix.
;
; None of these dereference a provenance-less pointer: they only observe
; its address.

; integer bytes, bitcast to a pointer, give a pointer at that address
define i64 @int_bytes_to_ptr() {
  %b = bitcast i64 4096 to b64
  %p = bitcast b64 %b to ptr
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

; the same through memory: integer bytes loaded at pointer type
define i64 @load_ptr_from_int_bytes() {
  %s = alloca i64
  store i64 4096, ptr %s
  %p = load ptr, ptr %s
  %r = ptrtoint ptr %p to i64
  ret i64 %r
}

; pointer bytes and integer bytes mixed: the low half of the slot keeps
; %x's pointer bytes, the high half is overwritten with integers carrying
; the same bits.  They are no longer all bytes of one pointer, so the
; result has no provenance -- but its address is still %x's.
define i64 @mixed_bytes_to_ptr_address() {
  %x = alloca i64
  %s = alloca ptr
  store ptr %x, ptr %s
  %xi = ptrtoint ptr %x to i64
  %hi64 = lshr i64 %xi, 32
  %hi = trunc i64 %hi64 to i32
  %s4 = getelementptr i8, ptr %s, i64 4
  store i32 %hi, ptr %s4
  %b = load b64, ptr %s
  %p = bitcast b64 %b to ptr
  %pi = ptrtoint ptr %p to i64
  %eq = icmp eq i64 %pi, %xi
  %r = zext i1 %eq to i64
  ret i64 %r
}

; guard: all bytes of one pointer, in order, give back that pointer with
; its provenance, so it can be loaded through
define i64 @ptr_bytes_round_trip() {
  %x = alloca i64
  store i64 42, ptr %x
  %s = alloca ptr
  store ptr %x, ptr %s
  %b = load b64, ptr %s
  %p = bitcast b64 %b to ptr
  %r = load i64, ptr %p
  ret i64 %r
}

; guard: pointer bits keep their provenance when they share a byte value with
; integer bits.  The b128 holds %x's pointer bits and then the integer 5;
; slicing it into lanes gives back all of %x's bits, in order, in lane 0.
; (Vellvm used to read any poison-free, non-pointer byte value as an
; integer, dropping the pointer's provenance, so the load below was UB.)
define i64 @ptr_int_bytes_keep_provenance() {
  %x = alloca i64
  store i64 42, ptr %x
  %s = alloca [2 x i64]
  store ptr %x, ptr %s
  %s1 = getelementptr i64, ptr %s, i64 1
  store i64 5, ptr %s1
  %b = load b128, ptr %s
  %v = bitcast b128 %b to <2 x b64>
  %e = extractelement <2 x b64> %v, i32 0
  %q = bitcast b64 %e to ptr
  %r = load i64, ptr %q
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_int_bytes_to_ptr = private unnamed_addr constant [27 x i8] c"int_bytes_to_ptr() = %lld\0A\00"
@fmt_load_ptr_from_int_bytes = private unnamed_addr constant [34 x i8] c"load_ptr_from_int_bytes() = %lld\0A\00"
@fmt_mixed_bytes_to_ptr_address = private unnamed_addr constant [37 x i8] c"mixed_bytes_to_ptr_address() = %lld\0A\00"
@fmt_ptr_bytes_round_trip = private unnamed_addr constant [31 x i8] c"ptr_bytes_round_trip() = %lld\0A\00"
@fmt_ptr_int_bytes_keep_provenance = private unnamed_addr constant [40 x i8] c"ptr_int_bytes_keep_provenance() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @int_bytes_to_ptr()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_int_bytes_to_ptr, i64 %v0)
  %v1 = call i64 @load_ptr_from_int_bytes()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_load_ptr_from_int_bytes, i64 %v1)
  %v2 = call i64 @mixed_bytes_to_ptr_address()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_mixed_bytes_to_ptr_address, i64 %v2)
  %v3 = call i64 @ptr_bytes_round_trip()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_ptr_bytes_round_trip, i64 %v3)
  %v4 = call i64 @ptr_int_bytes_keep_provenance()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_ptr_int_bytes_keep_provenance, i64 %v4)
  ret i32 0
}

; ASSERT EQ: i64 4096 = call i64 @int_bytes_to_ptr()
; ASSERT EQ: i64 4096 = call i64 @load_ptr_from_int_bytes()
; ASSERT EQ: i64 1    = call i64 @mixed_bytes_to_ptr_address()
; ASSERT EQ: i64 42   = call i64 @ptr_bytes_round_trip()
; ASSERT EQ: i64 42   = call i64 @ptr_int_bytes_keep_provenance()
