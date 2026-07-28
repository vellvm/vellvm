; PERF: startup initialization of a large constant global.
; A [16384 x i64] zeroinitializer global and a single load: all the time
; is interpreter startup — denoting the zero-initialized aggregate and
; serializing its 128 KiB through the byte-level write path into the
; memory map. ~68 us per element at this size.
;
; CAUTION: initialization is not stack-safe — at [32768 x i64] the
; interpreter dies with an OCaml stack overflow (somewhere in the
; non-tail-recursive aggregate denotation/serialization). Keep the size
; under that until fixed; this file also serves as a canary for the
; overflow threshold moving.
;
; Tune: change the array size (type + GEP bound). Result is 0 (a zero
; element read back).

@g = global [16384 x i64] zeroinitializer

define i64 @main(i64 %argc, i8** %argv) {
  %p = getelementptr [16384 x i64], [16384 x i64]* @g, i64 0, i64 123
  %v = load i64, i64* %p
  ret i64 %v
}

; ASSERT EQ: i64 0 = call i64 @main(i64 0, i8** null)
