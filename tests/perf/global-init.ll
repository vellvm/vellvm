; PERF: startup initialization of a large constant global.
; A [65536 x i64] zeroinitializer global and a single load: all the time
; is interpreter startup — denoting the zero-initialized aggregate and
; serializing its 512 KiB through the byte-level write path into the
; memory map.
;
; This size used to crash: initialization went through four separate
; non-tail-recursive list operations on the allocate/write path
; (generate_num_poison_bytes_h's [N.recursion], IntMaps.add_all_index,
; Implementations/Memory.v's memory_bytes_to_bytes's [map], and
; List.concat via allocate_dtyp — plus memS_bind's eager [Mput], the one
; non-closure-wrapped case in the memS free monad), each hitting an OCaml
; native stack overflow around ~32768 elements. All five are now
; accumulator-based / closure-wrapped tail-safe rewrites; this file
; guards the regression. Scaling above this size is now purely a
; performance question (confirmed up to 524288 elements/34s), not a
; correctness one.
;
; Tune: change the array size (type + GEP bound). Result is 0 (a zero
; element read back).

@g = global [65536 x i64] zeroinitializer

define i64 @main(i64 %argc, i8** %argv) {
  %p = getelementptr [65536 x i64], [65536 x i64]* @g, i64 0, i64 123
  %v = load i64, i64* %p
  ret i64 %v
}

; ASSERT EQ: i64 0 = call i64 @main(i64 0, i8** null)
