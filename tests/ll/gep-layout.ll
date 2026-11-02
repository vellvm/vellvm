; getelementptr, alignment and padding: packed (sub-byte) vectors, and
; structs / arrays / vectors nested inside one another.
;
; Two kinds of case:
;
; - offset cases compute `ptrtoint (getelementptr T, ptr null, ...)`, i.e.
;   the byte offset LLVM's DataLayout assigns to a field or element, or (with
;   a single index 1) the alloc size of T.  These pin down the layout itself.
;
; - memory cases store through one GEP path and load through another, so
;   that a wrong offset, a wrong store size (writing too many or too few
;   bytes), or a wrong padding decision shows up as a wrong value.
;
; Layout rules exercised (default datalayout, little endian):
; - a vector <N x iM> occupies ceil(N*M/8) bytes (its elements are packed);
;   its alignment is that size rounded up to a power of two.
; - GEP *into* a vector steps by the element's *store* size (the vector's
;   elements are contiguous), unlike an array, which steps by the alloc
;   size: element 2 of <3 x i24> is at byte 6, of [3 x i24] at byte 8.
;   That is only meaningful when the elements are byte-addressable: LLVM's
;   verifier (as of LLVM 23) rejects a GEP into <N x i1>, <N x i12>, ... with
;   "GEP into vector with non-byte-addressable element type", so this file
;   never does that.  Bytes inside a packed vector are addressed with an
;   i8 GEP instead.
; - struct fields are placed at their alignment and advance by their alloc
;   size; a packed struct skips the alignment but still advances by the
;   alloc size; a struct's size is padded to its alignment.
;
; Each case returns an i64 so the file can also be run natively, e.g.
;   clang -w tests/ll/gep-layout.ll -o a.out && ./a.out
; and its output compared with the ASSERTs at the bottom.
;
; Generated with tests/gen.py (print-all mode) from the functions below.

%s_v16i1   = type { i8, <16 x i1>, i8 }           ; 0, 2, 4; size 6
%s_v4i1    = type { i1, <4 x i1>, i32 }           ; 0, 1, 4; size 8
%s_v3i12   = type { i8, <3 x i12> }               ; 0, 8; size 16
%p_v3i12   = type <{ i8, <3 x i12>, i8 }>         ; 0, 1, 9; size 10
%inner     = type { i16, <3 x i1> }               ; 0, 2; size 4
%outer     = type { i8, [2 x %inner], i64 }       ; 0, 2, 16; size 24
%s_i24     = type { i8, i24, i8 }                 ; 0, 4, 8; size 12
%s_v2i64   = type { i8, <2 x i64> }               ; 0, 16; size 32
%s_v2ptr   = type { i8, <2 x ptr> }               ; 0, 16; size 32
%deep      = type { i16, [2 x <3 x i12>], i8 }    ; 0, 8, 24; size 32
%p_inner   = type <{ i8, i32 }>                   ; size 5, align 1
%s_pinner  = type { i8, [3 x %p_inner], i16 }     ; 0, 1, 16; size 18
%nest3     = type { i8, { i8, { i8, <2 x i4> } }, [2 x { i32, <5 x i1> }] }

; ======================================================== offsets / sizes

; ---------------------------------------------- alloc sizes of vectors

define i64 @size_v8i1() {
  %p = getelementptr <8 x i1>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 5 bits: 1 byte
define i64 @size_v5i1() {
  %p = getelementptr <5 x i1>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 17 bits: 3 bytes, aligned to 4
define i64 @size_v17i1() {
  %p = getelementptr <17 x i1>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 36 bits: 5 bytes, aligned to 8
define i64 @size_v3i12() {
  %p = getelementptr <3 x i12>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 24 bits: 3 bytes, aligned to 4
define i64 @size_v4i6() {
  %p = getelementptr <4 x i6>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 12 bytes, aligned to 16
define i64 @size_v3i32() {
  %p = getelementptr <3 x i32>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; 9 bytes (3 x i24 packed), aligned to 16
define i64 @size_v3i24() {
  %p = getelementptr <3 x i24>, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; ------------------------------------------ GEP into a vector: element stride

; element 2 of <3 x i24> is at byte 6, where its bits are: GEP into a
; vector steps by the element's store size (3), not its alloc size (4)
define i64 @gep_v3i24_elt2() {
  %p = getelementptr <3 x i24>, ptr null, i64 0, i64 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; ------------------------------------------------- arrays of packed vectors

define i64 @gep_arr_v8i1() {
  %p = getelementptr [4 x <8 x i1>], ptr null, i64 0, i64 3
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @gep_arr_v5i1() {
  %p = getelementptr [4 x <5 x i1>], ptr null, i64 0, i64 3
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; stride 4: <4 x i6> is 3 bytes but 4-aligned
define i64 @gep_arr_v4i6() {
  %p = getelementptr [3 x <4 x i6>], ptr null, i64 0, i64 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; stride 8: <3 x i12> is 5 bytes but 8-aligned
define i64 @gep_arr_v3i12() {
  %p = getelementptr [4 x <3 x i12>], ptr null, i64 0, i64 3
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; stride 16: <3 x i32> is 12 bytes but 16-aligned
define i64 @gep_arr_v3i32() {
  %p = getelementptr [2 x <3 x i32>], ptr null, i64 0, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; arrays of i1 are byte-strided, like vectors of i1
define i64 @gep_arr_i1() {
  %p = getelementptr [8 x i1], ptr null, i64 0, i64 5
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; stride 4 for i24 (contrast gep_v3i24_elt2)
define i64 @gep_arr_i24() {
  %p = getelementptr [3 x i24], ptr null, i64 0, i64 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; a pointer-typed GEP index steps by whole arrays of vectors
define i64 @gep_arr_v5i1_outer() {
  %p = getelementptr [3 x <5 x i1>], ptr null, i64 2, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; ------------------------------------------ structs containing packed vectors

define i64 @off_s_v16i1_f2() {
  %p = getelementptr %s_v16i1, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_s_v16i1() {
  %p = getelementptr %s_v16i1, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_s_v4i1_f1() {
  %p = getelementptr %s_v4i1, ptr null, i64 0, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_s_v4i1_f2() {
  %p = getelementptr %s_v4i1, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_s_v3i12_f1() {
  %p = getelementptr %s_v3i12, ptr null, i64 0, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_s_v3i12() {
  %p = getelementptr %s_v3i12, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; packed struct: no alignment for the vector, but the next field comes after
; the vector's *alloc* size (8), not its 5-byte store size
define i64 @off_p_v3i12_f2() {
  %p = getelementptr %p_v3i12, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_p_v3i12() {
  %p = getelementptr %p_v3i12, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; ------------------------------------------------------ nested aggregates

; outer.1[1].1 = 2 + 4 + 2
define i64 @off_outer_deep() {
  %p = getelementptr %outer, ptr null, i64 0, i32 1, i64 1, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_outer_f2() {
  %p = getelementptr %outer, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_outer() {
  %p = getelementptr %outer, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_s_i24_f2() {
  %p = getelementptr %s_i24, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_s_i24() {
  %p = getelementptr %s_i24, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_s_v2i64_f1() {
  %p = getelementptr %s_v2i64, ptr null, i64 0, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; element 1 of the <2 x ptr> field
define i64 @off_s_v2ptr_elt1() {
  %p = getelementptr %s_v2ptr, ptr null, i64 0, i32 1, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; deep.1[1] = 8 + 8, deep.2 = 24
define i64 @off_deep_arr1() {
  %p = getelementptr %deep, ptr null, i64 0, i32 1, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_deep_f2() {
  %p = getelementptr %deep, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_deep() {
  %p = getelementptr %deep, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; a packed struct inside an unpacked one: the array of packed structs is
; 1-aligned with stride 5, so the i16 after it lands at 16
define i64 @off_pinner_arr2_f1() {
  %p = getelementptr %s_pinner, ptr null, i64 0, i32 1, i64 2, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_pinner_f2() {
  %p = getelementptr %s_pinner, ptr null, i64 0, i32 2
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; three levels of nesting:
;   { i8, { i8, { i8, <2 x i4> } }, [2 x { i32, <5 x i1> }] }
; the <2 x i4> is at 1+1+1 = 3; the array is 4-aligned at 4, stride 8, and
; the <5 x i1> of element 1 is at 4 + 8 + 4
define i64 @off_nest3_v2i4() {
  %p = getelementptr %nest3, ptr null, i64 0, i32 1, i32 1, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @off_nest3_v5i1() {
  %p = getelementptr %nest3, ptr null, i64 0, i32 2, i64 1, i32 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

define i64 @size_nest3() {
  %p = getelementptr %nest3, ptr null, i64 1
  %i = ptrtoint ptr %p to i64
  ret i64 %i
}

; ================================================================= memory

; a <16 x i1> stored into its field does not touch the i8s around it
define i64 @mem_s_v16i1_neighbors() {
  %s = alloca %s_v16i1
  %f0 = getelementptr %s_v16i1, ptr %s, i64 0, i32 0
  %f1 = getelementptr %s_v16i1, ptr %s, i64 0, i32 1
  %f2 = getelementptr %s_v16i1, ptr %s, i64 0, i32 2
  store i8 11, ptr %f0
  store i8 22, ptr %f2
  store <16 x i1> <i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1,
                   i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1>, ptr %f1
  %a = load i8, ptr %f0
  %b = load i8, ptr %f2
  %xa = zext i8 %a to i64
  %xb = zext i8 %b to i64
  %ya = mul i64 %xa, 100
  %s1 = add i64 %ya, %xb
  ret i64 %s1
}

; ... and reads back as the packed integer
define i64 @mem_s_v16i1_as_i16() {
  %s = alloca %s_v16i1
  %f1 = getelementptr %s_v16i1, ptr %s, i64 0, i32 1
  store <16 x i1> <i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                   i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1>, ptr %f1
  %v = load i16, ptr %f1
  %r = zext i16 %v to i64
  ret i64 %r
}

; storing the whole struct lays the vector out at offset 2
define i64 @mem_s_v16i1_whole() {
  %s = alloca %s_v16i1
  store %s_v16i1 { i8 1, <16 x i1> <i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                                    i1 1, i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0>,
                   i8 3 }, ptr %s
  %q = getelementptr i8, ptr %s, i64 3
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; byte 1 of a <16 x i1> holds elements 8..15
define i64 @mem_byte_of_v16i1() {
  %p = alloca <16 x i1>
  store <16 x i1> <i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0,
                   i1 1, i1 0, i1 1, i1 0, i1 0, i1 0, i1 0, i1 1>, ptr %p
  %q = getelementptr i8, ptr %p, i64 1
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; a field after a <4 x i1>: the struct's i32 survives a store of the vector
define i64 @mem_s_v4i1() {
  %s = alloca %s_v4i1
  %f1 = getelementptr %s_v4i1, ptr %s, i64 0, i32 1
  %f2 = getelementptr %s_v4i1, ptr %s, i64 0, i32 2
  store i32 123456, ptr %f2
  store <4 x i1> <i1 1, i1 0, i1 1, i1 1>, ptr %f1
  %v = load <4 x i1>, ptr %f1
  %i = bitcast <4 x i1> %v to i4
  %x = zext i4 %i to i64
  %n = load i32, ptr %f2
  %y = zext i32 %n to i64
  %y10 = mul i64 %y, 100
  %r = add i64 %y10, %x
  ret i64 %r
}

; array of <5 x i1>: write each element through a GEP, read one back
define i64 @mem_arr_v5i1() {
  %a = alloca [4 x <5 x i1>]
  %e0 = getelementptr [4 x <5 x i1>], ptr %a, i64 0, i64 0
  %e1 = getelementptr [4 x <5 x i1>], ptr %a, i64 0, i64 1
  %e2 = getelementptr [4 x <5 x i1>], ptr %a, i64 0, i64 2
  %e3 = getelementptr [4 x <5 x i1>], ptr %a, i64 0, i64 3
  store <5 x i1> <i1 1, i1 0, i1 0, i1 0, i1 0>, ptr %e0
  store <5 x i1> <i1 0, i1 1, i1 0, i1 0, i1 0>, ptr %e1
  store <5 x i1> <i1 0, i1 0, i1 1, i1 1, i1 0>, ptr %e2
  store <5 x i1> <i1 1, i1 1, i1 1, i1 1, i1 1>, ptr %e3
  %v = load <5 x i1>, ptr %e2
  %i = bitcast <5 x i1> %v to i5
  %r = zext i5 %i to i64
  ret i64 %r
}

; sum of the elements of an array of <8 x i1>, indexed by a loop variable
define i64 @mem_arr_v8i1_loop() {
entry:
  %a = alloca [4 x <8 x i1>]
  store [4 x <8 x i1>] [<8 x i1> <i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0>,
                        <8 x i1> <i1 0, i1 1, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0>,
                        <8 x i1> <i1 0, i1 0, i1 1, i1 0, i1 0, i1 0, i1 0, i1 0>,
                        <8 x i1> <i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1>], ptr %a
  br label %loop
loop:
  %k = phi i64 [ 0, %entry ], [ %k1, %loop ]
  %acc = phi i64 [ 0, %entry ], [ %acc1, %loop ]
  %p = getelementptr [4 x <8 x i1>], ptr %a, i64 0, i64 %k
  %v = load <8 x i1>, ptr %p
  %b = bitcast <8 x i1> %v to i8
  %x = zext i8 %b to i64
  %acc1 = add i64 %acc, %x
  %k1 = add i64 %k, 1
  %done = icmp eq i64 %k1, 4
  br i1 %done, label %exit, label %loop
exit:
  ret i64 %acc1
}

; a <4 x i6> (3 bytes) in a 4-byte slot leaves the slot's last byte alone
define i64 @mem_arr_v4i6_slot() {
  %a = alloca [3 x <4 x i6>]
  %e1 = getelementptr [3 x <4 x i6>], ptr %a, i64 0, i64 1
  store i32 -1, ptr %e1
  store <4 x i6> <i6 1, i6 2, i6 3, i6 4>, ptr %e1
  %i = load i32, ptr %e1
  %r = zext i32 %i to i64
  ret i64 %r
}

; nested: deep.1[1] is a <3 x i12> at offset 16; deep.2 (offset 24) survives
define i64 @mem_deep() {
  %d = alloca %deep
  %f2 = getelementptr %deep, ptr %d, i64 0, i32 2
  store i8 77, ptr %f2
  %e = getelementptr %deep, ptr %d, i64 0, i32 1, i64 1
  store <3 x i12> <i12 2424, i12 3258, i12 4095>, ptr %e
  ; byte 2 of the vector holds bits 16..23, the top 8 bits of element 1
  ; (0xCBA) -> 0xCB
  %q = getelementptr i8, ptr %d, i64 18
  %b = load i8, ptr %q
  %c = load i8, ptr %f2
  %xb = zext i8 %b to i64
  %xc = zext i8 %c to i64
  %yb = mul i64 %xb, 1000
  %r = add i64 %yb, %xc
  ret i64 %r
}

; store a whole nested struct, then pick an element out of the vector with
; a load + extractvalue + extractelement
define i64 @mem_deep_whole() {
  %d = alloca %deep
  store %deep { i16 5,
                [2 x <3 x i12>] [<3 x i12> <i12 1, i12 2, i12 3>,
                                 <3 x i12> <i12 4, i12 5, i12 6>],
                i8 9 }, ptr %d
  %v = load %deep, ptr %d
  %arr = extractvalue %deep %v, 1
  %vec = extractvalue [2 x <3 x i12>] %arr, 1
  %e = extractelement <3 x i12> %vec, i32 2
  %x = zext i12 %e to i64
  %last = extractvalue %deep %v, 2
  %y = zext i8 %last to i64
  %y10 = mul i64 %y, 10
  %r = add i64 %y10, %x
  ret i64 %r
}

; the fields of a struct stored one at a time read back as a whole
define i64 @mem_outer_fields() {
  %o = alloca %outer
  %f0 = getelementptr %outer, ptr %o, i64 0, i32 0
  %a0 = getelementptr %outer, ptr %o, i64 0, i32 1, i64 0, i32 1
  %a1 = getelementptr %outer, ptr %o, i64 0, i32 1, i64 1, i32 1
  %h1 = getelementptr %outer, ptr %o, i64 0, i32 1, i64 1, i32 0
  %h0 = getelementptr %outer, ptr %o, i64 0, i32 1, i64 0, i32 0
  %f2 = getelementptr %outer, ptr %o, i64 0, i32 2
  store i8 1, ptr %f0
  store i16 2, ptr %h0
  store <3 x i1> <i1 1, i1 0, i1 0>, ptr %a0
  store i16 3, ptr %h1
  store <3 x i1> <i1 0, i1 1, i1 1>, ptr %a1
  store i64 4, ptr %f2
  %v = load %outer, ptr %o
  %x0 = extractvalue %outer %v, 0
  %x1 = extractvalue %outer %v, 1, 1, 0
  %x2 = extractvalue %outer %v, 1, 1, 1
  %x3 = extractvalue %outer %v, 2
  %b2 = bitcast <3 x i1> %x2 to i3
  %y0 = zext i8 %x0 to i64
  %y1 = zext i16 %x1 to i64
  %y2 = zext i3 %b2 to i64
  ; 1000*x0 + 100*x1 + 10*bits(x2) + x3
  %z0 = mul i64 %y0, 1000
  %z1 = mul i64 %y1, 100
  %z2 = mul i64 %y2, 10
  %s0 = add i64 %z0, %z1
  %s1 = add i64 %s0, %z2
  %s2 = add i64 %s1, %x3
  ret i64 %s2
}

; packed struct: the trailing i8 is at 9, past the vector's alloc size
define i64 @mem_p_v3i12() {
  %s = alloca %p_v3i12
  store %p_v3i12 <{ i8 1, <3 x i12> <i12 0, i12 0, i12 0>, i8 42 }>, ptr %s
  %q = getelementptr i8, ptr %s, i64 9
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; packed structs in an array, inside an unpacked struct: the i32 of
; element 2 is at the unaligned offset 1 + 2*5 + 1 = 12
define i64 @mem_pinner() {
  %s = alloca %s_pinner
  %p = getelementptr %s_pinner, ptr %s, i64 0, i32 1, i64 2, i32 1
  store i32 305419896, ptr %p                ; 0x12345678
  %q = getelementptr i8, ptr %s, i64 13
  %b = load i8, ptr %q
  %r = zext i8 %b to i64
  ret i64 %r
}

; i24 fields are 4-aligned and store only 3 bytes
define i64 @mem_s_i24() {
  %s = alloca %s_i24
  %f1 = getelementptr %s_i24, ptr %s, i64 0, i32 1
  %pad = getelementptr i8, ptr %s, i64 7
  store i8 99, ptr %pad
  store i24 -1, ptr %f1
  %b = load i8, ptr %pad
  %r = zext i8 %b to i64
  ret i64 %r
}

; three levels deep: write the <2 x i4> and the second <5 x i1> through
; GEPs, read them back with one load of the whole struct
define i64 @mem_nest3() {
  %s = alloca %nest3
  %v4 = getelementptr %nest3, ptr %s, i64 0, i32 1, i32 1, i32 1
  %v5 = getelementptr %nest3, ptr %s, i64 0, i32 2, i64 1, i32 1
  %n1 = getelementptr %nest3, ptr %s, i64 0, i32 2, i64 1, i32 0
  store <2 x i4> <i4 3, i4 12>, ptr %v4
  store <5 x i1> <i1 1, i1 1, i1 0, i1 0, i1 1>, ptr %v5
  store i32 7, ptr %n1
  %w = load %nest3, ptr %s
  %a = extractvalue %nest3 %w, 1, 1, 1
  %b = extractvalue %nest3 %w, 2, 1, 1
  %c = extractvalue %nest3 %w, 2, 1, 0
  %ai = bitcast <2 x i4> %a to i8
  %bi = bitcast <5 x i1> %b to i5
  %xa = zext i8 %ai to i64
  %xb = zext i5 %bi to i64
  %xc = zext i32 %c to i64
  ; 10000*bits(a) + 100*bits(b) + c
  %ya = mul i64 %xa, 10000
  %yb = mul i64 %xb, 100
  %s0 = add i64 %ya, %yb
  %s1 = add i64 %s0, %xc
  ret i64 %s1
}

; copying a struct with packed-vector fields byte by byte preserves it
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)

define i64 @mem_memcpy_nest3() {
  %s = alloca %nest3
  %t = alloca %nest3
  store %nest3 { i8 1, { i8, { i8, <2 x i4> } } { i8 2, { i8, <2 x i4> } { i8 3, <2 x i4> <i4 5, i4 6> } },
                 [2 x { i32, <5 x i1> }] [{ i32, <5 x i1> } { i32 8, <5 x i1> <i1 1, i1 0, i1 0, i1 0, i1 0> },
                                          { i32, <5 x i1> } { i32 9, <5 x i1> <i1 0, i1 0, i1 0, i1 0, i1 1> }] },
        ptr %s
  call void @llvm.memcpy.p0.p0.i64(ptr %t, ptr %s, i64 20, i1 false)
  %v4 = getelementptr %nest3, ptr %t, i64 0, i32 1, i32 1, i32 1
  %v5 = getelementptr %nest3, ptr %t, i64 0, i32 2, i64 1, i32 1
  %a = load i8, ptr %v4
  %b = load <5 x i1>, ptr %v5
  %bi = bitcast <5 x i1> %b to i5
  %xa = zext i8 %a to i64
  %xb = zext i5 %bi to i64
  %ya = mul i64 %xa, 100
  %r = add i64 %ya, %xb
  ret i64 %r
}

; a pointer stored in a <2 x ptr> field, loaded back through a GEP to the
; element, still points at the right thing
define i64 @mem_s_v2ptr() {
  %x = alloca i64
  store i64 31337, ptr %x
  %s = alloca %s_v2ptr
  %v0 = insertelement <2 x ptr> zeroinitializer, ptr %x, i32 1
  %f1 = getelementptr %s_v2ptr, ptr %s, i64 0, i32 1
  store <2 x ptr> %v0, ptr %f1
  %e1 = getelementptr %s_v2ptr, ptr %s, i64 0, i32 1, i64 1
  %p = load ptr, ptr %e1
  %r = load i64, ptr %p
  ret i64 %r
}

; a store through a GEP into a byte-sized vector changes just that element
define i64 @mem_gep_into_v4i8() {
  %p = alloca <4 x i8>
  store <4 x i8> <i8 1, i8 2, i8 3, i8 4>, ptr %p
  %q = getelementptr <4 x i8>, ptr %p, i64 0, i64 2
  store i8 9, ptr %q
  %v = load <4 x i8>, ptr %p
  %i = bitcast <4 x i8> %v to i32
  %r = zext i32 %i to i64
  ret i64 %r
}

; negative GEP index: back from element 3 to element 1 of an array of
; <4 x i6> slots
define i64 @mem_neg_index() {
  %a = alloca [4 x <4 x i6>]
  %e1 = getelementptr [4 x <4 x i6>], ptr %a, i64 0, i64 1
  store <4 x i6> <i6 63, i6 0, i6 0, i6 0>, ptr %e1
  %e3 = getelementptr [4 x <4 x i6>], ptr %a, i64 0, i64 3
  %back = getelementptr <4 x i6>, ptr %e3, i64 -2
  %v = load <4 x i6>, ptr %back
  %e = extractelement <4 x i6> %v, i32 0
  %r = zext i6 %e to i64
  ret i64 %r
}

; --- executable form: print each result so the file can be run and
; --- its output diffed against clang/llc.

@fmt_size_v8i1 = private unnamed_addr constant [20 x i8] c"size_v8i1() = %lld\0A\00"
@fmt_size_v5i1 = private unnamed_addr constant [20 x i8] c"size_v5i1() = %lld\0A\00"
@fmt_size_v17i1 = private unnamed_addr constant [21 x i8] c"size_v17i1() = %lld\0A\00"
@fmt_size_v3i12 = private unnamed_addr constant [21 x i8] c"size_v3i12() = %lld\0A\00"
@fmt_size_v4i6 = private unnamed_addr constant [20 x i8] c"size_v4i6() = %lld\0A\00"
@fmt_size_v3i32 = private unnamed_addr constant [21 x i8] c"size_v3i32() = %lld\0A\00"
@fmt_size_v3i24 = private unnamed_addr constant [21 x i8] c"size_v3i24() = %lld\0A\00"
@fmt_gep_v3i24_elt2 = private unnamed_addr constant [25 x i8] c"gep_v3i24_elt2() = %lld\0A\00"
@fmt_gep_arr_v8i1 = private unnamed_addr constant [23 x i8] c"gep_arr_v8i1() = %lld\0A\00"
@fmt_gep_arr_v5i1 = private unnamed_addr constant [23 x i8] c"gep_arr_v5i1() = %lld\0A\00"
@fmt_gep_arr_v4i6 = private unnamed_addr constant [23 x i8] c"gep_arr_v4i6() = %lld\0A\00"
@fmt_gep_arr_v3i12 = private unnamed_addr constant [24 x i8] c"gep_arr_v3i12() = %lld\0A\00"
@fmt_gep_arr_v3i32 = private unnamed_addr constant [24 x i8] c"gep_arr_v3i32() = %lld\0A\00"
@fmt_gep_arr_i1 = private unnamed_addr constant [21 x i8] c"gep_arr_i1() = %lld\0A\00"
@fmt_gep_arr_i24 = private unnamed_addr constant [22 x i8] c"gep_arr_i24() = %lld\0A\00"
@fmt_gep_arr_v5i1_outer = private unnamed_addr constant [29 x i8] c"gep_arr_v5i1_outer() = %lld\0A\00"
@fmt_off_s_v16i1_f2 = private unnamed_addr constant [25 x i8] c"off_s_v16i1_f2() = %lld\0A\00"
@fmt_size_s_v16i1 = private unnamed_addr constant [23 x i8] c"size_s_v16i1() = %lld\0A\00"
@fmt_off_s_v4i1_f1 = private unnamed_addr constant [24 x i8] c"off_s_v4i1_f1() = %lld\0A\00"
@fmt_off_s_v4i1_f2 = private unnamed_addr constant [24 x i8] c"off_s_v4i1_f2() = %lld\0A\00"
@fmt_off_s_v3i12_f1 = private unnamed_addr constant [25 x i8] c"off_s_v3i12_f1() = %lld\0A\00"
@fmt_size_s_v3i12 = private unnamed_addr constant [23 x i8] c"size_s_v3i12() = %lld\0A\00"
@fmt_off_p_v3i12_f2 = private unnamed_addr constant [25 x i8] c"off_p_v3i12_f2() = %lld\0A\00"
@fmt_size_p_v3i12 = private unnamed_addr constant [23 x i8] c"size_p_v3i12() = %lld\0A\00"
@fmt_off_outer_deep = private unnamed_addr constant [25 x i8] c"off_outer_deep() = %lld\0A\00"
@fmt_off_outer_f2 = private unnamed_addr constant [23 x i8] c"off_outer_f2() = %lld\0A\00"
@fmt_size_outer = private unnamed_addr constant [21 x i8] c"size_outer() = %lld\0A\00"
@fmt_off_s_i24_f2 = private unnamed_addr constant [23 x i8] c"off_s_i24_f2() = %lld\0A\00"
@fmt_size_s_i24 = private unnamed_addr constant [21 x i8] c"size_s_i24() = %lld\0A\00"
@fmt_off_s_v2i64_f1 = private unnamed_addr constant [25 x i8] c"off_s_v2i64_f1() = %lld\0A\00"
@fmt_off_s_v2ptr_elt1 = private unnamed_addr constant [27 x i8] c"off_s_v2ptr_elt1() = %lld\0A\00"
@fmt_off_deep_arr1 = private unnamed_addr constant [24 x i8] c"off_deep_arr1() = %lld\0A\00"
@fmt_off_deep_f2 = private unnamed_addr constant [22 x i8] c"off_deep_f2() = %lld\0A\00"
@fmt_size_deep = private unnamed_addr constant [20 x i8] c"size_deep() = %lld\0A\00"
@fmt_off_pinner_arr2_f1 = private unnamed_addr constant [29 x i8] c"off_pinner_arr2_f1() = %lld\0A\00"
@fmt_off_pinner_f2 = private unnamed_addr constant [24 x i8] c"off_pinner_f2() = %lld\0A\00"
@fmt_off_nest3_v2i4 = private unnamed_addr constant [25 x i8] c"off_nest3_v2i4() = %lld\0A\00"
@fmt_off_nest3_v5i1 = private unnamed_addr constant [25 x i8] c"off_nest3_v5i1() = %lld\0A\00"
@fmt_size_nest3 = private unnamed_addr constant [21 x i8] c"size_nest3() = %lld\0A\00"
@fmt_mem_s_v16i1_neighbors = private unnamed_addr constant [32 x i8] c"mem_s_v16i1_neighbors() = %lld\0A\00"
@fmt_mem_s_v16i1_as_i16 = private unnamed_addr constant [29 x i8] c"mem_s_v16i1_as_i16() = %lld\0A\00"
@fmt_mem_s_v16i1_whole = private unnamed_addr constant [28 x i8] c"mem_s_v16i1_whole() = %lld\0A\00"
@fmt_mem_byte_of_v16i1 = private unnamed_addr constant [28 x i8] c"mem_byte_of_v16i1() = %lld\0A\00"
@fmt_mem_s_v4i1 = private unnamed_addr constant [21 x i8] c"mem_s_v4i1() = %lld\0A\00"
@fmt_mem_arr_v5i1 = private unnamed_addr constant [23 x i8] c"mem_arr_v5i1() = %lld\0A\00"
@fmt_mem_arr_v8i1_loop = private unnamed_addr constant [28 x i8] c"mem_arr_v8i1_loop() = %lld\0A\00"
@fmt_mem_arr_v4i6_slot = private unnamed_addr constant [28 x i8] c"mem_arr_v4i6_slot() = %lld\0A\00"
@fmt_mem_deep = private unnamed_addr constant [19 x i8] c"mem_deep() = %lld\0A\00"
@fmt_mem_deep_whole = private unnamed_addr constant [25 x i8] c"mem_deep_whole() = %lld\0A\00"
@fmt_mem_outer_fields = private unnamed_addr constant [27 x i8] c"mem_outer_fields() = %lld\0A\00"
@fmt_mem_p_v3i12 = private unnamed_addr constant [22 x i8] c"mem_p_v3i12() = %lld\0A\00"
@fmt_mem_pinner = private unnamed_addr constant [21 x i8] c"mem_pinner() = %lld\0A\00"
@fmt_mem_s_i24 = private unnamed_addr constant [20 x i8] c"mem_s_i24() = %lld\0A\00"
@fmt_mem_nest3 = private unnamed_addr constant [20 x i8] c"mem_nest3() = %lld\0A\00"
@fmt_mem_memcpy_nest3 = private unnamed_addr constant [27 x i8] c"mem_memcpy_nest3() = %lld\0A\00"
@fmt_mem_s_v2ptr = private unnamed_addr constant [22 x i8] c"mem_s_v2ptr() = %lld\0A\00"
@fmt_mem_gep_into_v4i8 = private unnamed_addr constant [28 x i8] c"mem_gep_into_v4i8() = %lld\0A\00"
@fmt_mem_neg_index = private unnamed_addr constant [24 x i8] c"mem_neg_index() = %lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %v0 = call i64 @size_v8i1()
  %p0 = call i32 (ptr, ...) @printf(ptr @fmt_size_v8i1, i64 %v0)
  %v1 = call i64 @size_v5i1()
  %p1 = call i32 (ptr, ...) @printf(ptr @fmt_size_v5i1, i64 %v1)
  %v2 = call i64 @size_v17i1()
  %p2 = call i32 (ptr, ...) @printf(ptr @fmt_size_v17i1, i64 %v2)
  %v3 = call i64 @size_v3i12()
  %p3 = call i32 (ptr, ...) @printf(ptr @fmt_size_v3i12, i64 %v3)
  %v4 = call i64 @size_v4i6()
  %p4 = call i32 (ptr, ...) @printf(ptr @fmt_size_v4i6, i64 %v4)
  %v5 = call i64 @size_v3i32()
  %p5 = call i32 (ptr, ...) @printf(ptr @fmt_size_v3i32, i64 %v5)
  %v6 = call i64 @size_v3i24()
  %p6 = call i32 (ptr, ...) @printf(ptr @fmt_size_v3i24, i64 %v6)
  %v7 = call i64 @gep_v3i24_elt2()
  %p7 = call i32 (ptr, ...) @printf(ptr @fmt_gep_v3i24_elt2, i64 %v7)
  %v8 = call i64 @gep_arr_v8i1()
  %p8 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v8i1, i64 %v8)
  %v9 = call i64 @gep_arr_v5i1()
  %p9 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v5i1, i64 %v9)
  %v10 = call i64 @gep_arr_v4i6()
  %p10 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v4i6, i64 %v10)
  %v11 = call i64 @gep_arr_v3i12()
  %p11 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v3i12, i64 %v11)
  %v12 = call i64 @gep_arr_v3i32()
  %p12 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v3i32, i64 %v12)
  %v13 = call i64 @gep_arr_i1()
  %p13 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_i1, i64 %v13)
  %v14 = call i64 @gep_arr_i24()
  %p14 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_i24, i64 %v14)
  %v15 = call i64 @gep_arr_v5i1_outer()
  %p15 = call i32 (ptr, ...) @printf(ptr @fmt_gep_arr_v5i1_outer, i64 %v15)
  %v16 = call i64 @off_s_v16i1_f2()
  %p16 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v16i1_f2, i64 %v16)
  %v17 = call i64 @size_s_v16i1()
  %p17 = call i32 (ptr, ...) @printf(ptr @fmt_size_s_v16i1, i64 %v17)
  %v18 = call i64 @off_s_v4i1_f1()
  %p18 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v4i1_f1, i64 %v18)
  %v19 = call i64 @off_s_v4i1_f2()
  %p19 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v4i1_f2, i64 %v19)
  %v20 = call i64 @off_s_v3i12_f1()
  %p20 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v3i12_f1, i64 %v20)
  %v21 = call i64 @size_s_v3i12()
  %p21 = call i32 (ptr, ...) @printf(ptr @fmt_size_s_v3i12, i64 %v21)
  %v22 = call i64 @off_p_v3i12_f2()
  %p22 = call i32 (ptr, ...) @printf(ptr @fmt_off_p_v3i12_f2, i64 %v22)
  %v23 = call i64 @size_p_v3i12()
  %p23 = call i32 (ptr, ...) @printf(ptr @fmt_size_p_v3i12, i64 %v23)
  %v24 = call i64 @off_outer_deep()
  %p24 = call i32 (ptr, ...) @printf(ptr @fmt_off_outer_deep, i64 %v24)
  %v25 = call i64 @off_outer_f2()
  %p25 = call i32 (ptr, ...) @printf(ptr @fmt_off_outer_f2, i64 %v25)
  %v26 = call i64 @size_outer()
  %p26 = call i32 (ptr, ...) @printf(ptr @fmt_size_outer, i64 %v26)
  %v27 = call i64 @off_s_i24_f2()
  %p27 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_i24_f2, i64 %v27)
  %v28 = call i64 @size_s_i24()
  %p28 = call i32 (ptr, ...) @printf(ptr @fmt_size_s_i24, i64 %v28)
  %v29 = call i64 @off_s_v2i64_f1()
  %p29 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v2i64_f1, i64 %v29)
  %v30 = call i64 @off_s_v2ptr_elt1()
  %p30 = call i32 (ptr, ...) @printf(ptr @fmt_off_s_v2ptr_elt1, i64 %v30)
  %v31 = call i64 @off_deep_arr1()
  %p31 = call i32 (ptr, ...) @printf(ptr @fmt_off_deep_arr1, i64 %v31)
  %v32 = call i64 @off_deep_f2()
  %p32 = call i32 (ptr, ...) @printf(ptr @fmt_off_deep_f2, i64 %v32)
  %v33 = call i64 @size_deep()
  %p33 = call i32 (ptr, ...) @printf(ptr @fmt_size_deep, i64 %v33)
  %v34 = call i64 @off_pinner_arr2_f1()
  %p34 = call i32 (ptr, ...) @printf(ptr @fmt_off_pinner_arr2_f1, i64 %v34)
  %v35 = call i64 @off_pinner_f2()
  %p35 = call i32 (ptr, ...) @printf(ptr @fmt_off_pinner_f2, i64 %v35)
  %v36 = call i64 @off_nest3_v2i4()
  %p36 = call i32 (ptr, ...) @printf(ptr @fmt_off_nest3_v2i4, i64 %v36)
  %v37 = call i64 @off_nest3_v5i1()
  %p37 = call i32 (ptr, ...) @printf(ptr @fmt_off_nest3_v5i1, i64 %v37)
  %v38 = call i64 @size_nest3()
  %p38 = call i32 (ptr, ...) @printf(ptr @fmt_size_nest3, i64 %v38)
  %v39 = call i64 @mem_s_v16i1_neighbors()
  %p39 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_v16i1_neighbors, i64 %v39)
  %v40 = call i64 @mem_s_v16i1_as_i16()
  %p40 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_v16i1_as_i16, i64 %v40)
  %v41 = call i64 @mem_s_v16i1_whole()
  %p41 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_v16i1_whole, i64 %v41)
  %v42 = call i64 @mem_byte_of_v16i1()
  %p42 = call i32 (ptr, ...) @printf(ptr @fmt_mem_byte_of_v16i1, i64 %v42)
  %v43 = call i64 @mem_s_v4i1()
  %p43 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_v4i1, i64 %v43)
  %v44 = call i64 @mem_arr_v5i1()
  %p44 = call i32 (ptr, ...) @printf(ptr @fmt_mem_arr_v5i1, i64 %v44)
  %v45 = call i64 @mem_arr_v8i1_loop()
  %p45 = call i32 (ptr, ...) @printf(ptr @fmt_mem_arr_v8i1_loop, i64 %v45)
  %v46 = call i64 @mem_arr_v4i6_slot()
  %p46 = call i32 (ptr, ...) @printf(ptr @fmt_mem_arr_v4i6_slot, i64 %v46)
  %v47 = call i64 @mem_deep()
  %p47 = call i32 (ptr, ...) @printf(ptr @fmt_mem_deep, i64 %v47)
  %v48 = call i64 @mem_deep_whole()
  %p48 = call i32 (ptr, ...) @printf(ptr @fmt_mem_deep_whole, i64 %v48)
  %v49 = call i64 @mem_outer_fields()
  %p49 = call i32 (ptr, ...) @printf(ptr @fmt_mem_outer_fields, i64 %v49)
  %v50 = call i64 @mem_p_v3i12()
  %p50 = call i32 (ptr, ...) @printf(ptr @fmt_mem_p_v3i12, i64 %v50)
  %v51 = call i64 @mem_pinner()
  %p51 = call i32 (ptr, ...) @printf(ptr @fmt_mem_pinner, i64 %v51)
  %v52 = call i64 @mem_s_i24()
  %p52 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_i24, i64 %v52)
  %v53 = call i64 @mem_nest3()
  %p53 = call i32 (ptr, ...) @printf(ptr @fmt_mem_nest3, i64 %v53)
  %v54 = call i64 @mem_memcpy_nest3()
  %p54 = call i32 (ptr, ...) @printf(ptr @fmt_mem_memcpy_nest3, i64 %v54)
  %v55 = call i64 @mem_s_v2ptr()
  %p55 = call i32 (ptr, ...) @printf(ptr @fmt_mem_s_v2ptr, i64 %v55)
  %v56 = call i64 @mem_gep_into_v4i8()
  %p56 = call i32 (ptr, ...) @printf(ptr @fmt_mem_gep_into_v4i8, i64 %v56)
  %v57 = call i64 @mem_neg_index()
  %p57 = call i32 (ptr, ...) @printf(ptr @fmt_mem_neg_index, i64 %v57)
  ret i32 0
}

; ASSERT EQ: i64 1          = call i64 @size_v8i1()
; ASSERT EQ: i64 1          = call i64 @size_v5i1()
; ASSERT EQ: i64 4          = call i64 @size_v17i1()
; ASSERT EQ: i64 8          = call i64 @size_v3i12()
; ASSERT EQ: i64 4          = call i64 @size_v4i6()
; ASSERT EQ: i64 16         = call i64 @size_v3i32()
; ASSERT EQ: i64 16         = call i64 @size_v3i24()
; ASSERT EQ: i64 6          = call i64 @gep_v3i24_elt2()
; ASSERT EQ: i64 3          = call i64 @gep_arr_v8i1()
; ASSERT EQ: i64 3          = call i64 @gep_arr_v5i1()
; ASSERT EQ: i64 8          = call i64 @gep_arr_v4i6()
; ASSERT EQ: i64 24         = call i64 @gep_arr_v3i12()
; ASSERT EQ: i64 16         = call i64 @gep_arr_v3i32()
; ASSERT EQ: i64 5          = call i64 @gep_arr_i1()
; ASSERT EQ: i64 8          = call i64 @gep_arr_i24()
; ASSERT EQ: i64 7          = call i64 @gep_arr_v5i1_outer()
; ASSERT EQ: i64 4          = call i64 @off_s_v16i1_f2()
; ASSERT EQ: i64 6          = call i64 @size_s_v16i1()
; ASSERT EQ: i64 1          = call i64 @off_s_v4i1_f1()
; ASSERT EQ: i64 4          = call i64 @off_s_v4i1_f2()
; ASSERT EQ: i64 8          = call i64 @off_s_v3i12_f1()
; ASSERT EQ: i64 16         = call i64 @size_s_v3i12()
; ASSERT EQ: i64 9          = call i64 @off_p_v3i12_f2()
; ASSERT EQ: i64 10         = call i64 @size_p_v3i12()
; ASSERT EQ: i64 8          = call i64 @off_outer_deep()
; ASSERT EQ: i64 16         = call i64 @off_outer_f2()
; ASSERT EQ: i64 24         = call i64 @size_outer()
; ASSERT EQ: i64 8          = call i64 @off_s_i24_f2()
; ASSERT EQ: i64 12         = call i64 @size_s_i24()
; ASSERT EQ: i64 16         = call i64 @off_s_v2i64_f1()
; ASSERT EQ: i64 24         = call i64 @off_s_v2ptr_elt1()
; ASSERT EQ: i64 16         = call i64 @off_deep_arr1()
; ASSERT EQ: i64 24         = call i64 @off_deep_f2()
; ASSERT EQ: i64 32         = call i64 @size_deep()
; ASSERT EQ: i64 12         = call i64 @off_pinner_arr2_f1()
; ASSERT EQ: i64 16         = call i64 @off_pinner_f2()
; ASSERT EQ: i64 3          = call i64 @off_nest3_v2i4()
; ASSERT EQ: i64 16         = call i64 @off_nest3_v5i1()
; ASSERT EQ: i64 20         = call i64 @size_nest3()
; ASSERT EQ: i64 1122       = call i64 @mem_s_v16i1_neighbors()
; ASSERT EQ: i64 32769      = call i64 @mem_s_v16i1_as_i16()
; ASSERT EQ: i64 3          = call i64 @mem_s_v16i1_whole()
; ASSERT EQ: i64 133        = call i64 @mem_byte_of_v16i1()
; ASSERT EQ: i64 12345613   = call i64 @mem_s_v4i1()
; ASSERT EQ: i64 12         = call i64 @mem_arr_v5i1()
; ASSERT EQ: i64 135        = call i64 @mem_arr_v8i1_loop()
; ASSERT EQ: i64 4279251073 = call i64 @mem_arr_v4i6_slot()
; ASSERT EQ: i64 203077     = call i64 @mem_deep()
; ASSERT EQ: i64 96         = call i64 @mem_deep_whole()
; ASSERT EQ: i64 1364       = call i64 @mem_outer_fields()
; ASSERT EQ: i64 42         = call i64 @mem_p_v3i12()
; ASSERT EQ: i64 86         = call i64 @mem_pinner()
; ASSERT EQ: i64 99         = call i64 @mem_s_i24()
; ASSERT EQ: i64 1951907    = call i64 @mem_nest3()
; ASSERT EQ: i64 10116      = call i64 @mem_memcpy_nest3()
; ASSERT EQ: i64 31337      = call i64 @mem_s_v2ptr()
; ASSERT EQ: i64 67699201   = call i64 @mem_gep_into_v4i8()
; ASSERT EQ: i64 63         = call i64 @mem_neg_index()
