; Loading and storing halves.
;
; [memory_bytes_to_dvalue] used to raise "unsupported half" for
; [DTYPE_FP FP_half], so a half could not survive a round trip through memory
; even though Sizeof.v already gave it its correct 2-byte size and alignment.
;
; These also exercise the serialization path from the other side: bitcast is
; implemented as store-then-load through [dvalue_to_memory_bytes], so a bug in
; either direction shows up here as well as in half_conv.ll.

define i16 @store_load() {
  %p = alloca half
  store half 0xH3C00, ptr %p
  %v = load half, ptr %p
  %a = bitcast half %v to i16
  ret i16 %a
}

; Signed zero must not be normalised away by a memory round trip.
define i16 @store_load_neg_zero() {
  %p = alloca half
  store half 0xH8000, ptr %p
  %v = load half, ptr %p
  %a = bitcast half %v to i16
  ret i16 %a
}

; Nor must a signaling NaN be quieted by one.
define i16 @store_load_snan() {
  %p = alloca half
  store half 0xH7C01, ptr %p
  %v = load half, ptr %p
  %a = bitcast half %v to i16
  ret i16 %a
}

; A half is 2 bytes, so consecutive elements must not overlap: if the size were
; wrong, the second store would clobber the first.
define i16 @array_element() {
  %p = alloca [4 x half]
  %p0 = getelementptr [4 x half], ptr %p, i32 0, i32 0
  %p1 = getelementptr [4 x half], ptr %p, i32 0, i32 1
  %p2 = getelementptr [4 x half], ptr %p, i32 0, i32 2
  store half 0xH3C00, ptr %p0
  store half 0xH4000, ptr %p1
  store half 0xH4200, ptr %p2
  %v = load half, ptr %p1
  %a = bitcast half %v to i16
  ret i16 %a
}

; Read a stored half back through an i16 pointer: the two must agree on the
; in-memory representation.
define i16 @reinterpret_as_i16() {
  %p = alloca half
  store half 0xH7BFF, ptr %p
  %v = load i16, ptr %p
  ret i16 %v
}

; ... and the other way around.
define i16 @stored_as_i16() {
  %p = alloca half
  store i16 15360, ptr %p
  %v = load half, ptr %p
  %a = bitcast half %v to i16
  ret i16 %a
}

; Arithmetic on values that went through memory.
define i16 @add_after_round_trip() {
  %p = alloca half
  %q = alloca half
  store half 0xH3C00, ptr %p
  store half 0xH4000, ptr %q
  %x = load half, ptr %p
  %y = load half, ptr %q
  %r = fadd half %x, %y
  %a = bitcast half %r to i16
  ret i16 %a
}

; ASSERT EQ: i16 15360 = call i16 @store_load()
; ASSERT EQ: i16 32768 = call i16 @store_load_neg_zero()
; ASSERT EQ: i16 31745 = call i16 @store_load_snan()
; ASSERT EQ: i16 16384 = call i16 @array_element()
; ASSERT EQ: i16 31743 = call i16 @reinterpret_as_i16()
; ASSERT EQ: i16 15360 = call i16 @stored_as_i16()
; ASSERT EQ: i16 16896 = call i16 @add_after_round_trip()
