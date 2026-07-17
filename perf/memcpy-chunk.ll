; PERF: bulk memory copy (the byte-level READ path).
; 100 memcpys of an 8 KiB buffer. Guards the linearity of bulk reads:
; read_bytes used to collect its result with the value-collecting
; map_monad, whose pending bind continuations made the copy quadratic in
; its size (100 copies of 8 KiB ran 72 s); it now uses the accumulator
; fold map_monad_acc and scales linearly. What remains is the per-byte
; AVL-map traffic (one map entry per byte) — compare against
; memset-chunk.ll, the write-only floor.
;
; Tune: change the buffer size (in the array types, the GEP indices, and
; the memcpy length) or the loop bound. Result is the sentinel byte (42)
; copied into the destination's last position.

declare void @llvm.memcpy.p0i8.p0i8.i64(i8*, i8*, i64, i1)

define i64 @main(i64 %argc, i8** %argv) {
entry:
  %a = alloca [8192 x i8]
  %b = alloca [8192 x i8]
  %pa = bitcast [8192 x i8]* %a to i8*
  %pb = bitcast [8192 x i8]* %b to i8*
  %lasta = getelementptr [8192 x i8], [8192 x i8]* %a, i64 0, i64 8191
  store i8 42, i8* %lasta
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %c = icmp eq i64 %i, 100
  br i1 %c, label %exit, label %body

body:
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %pb, i8* %pa, i64 8192, i1 false)
  %i.next = add i64 %i, 1
  br label %header

exit:
  %lastb = getelementptr [8192 x i8], [8192 x i8]* %b, i64 0, i64 8191
  %v = load i8, i8* %lastb
  %r = zext i8 %v to i64
  ret i64 %r
}

; ASSERT EQ: i64 42 = call i64 @main(i64 0, i8** null)
