; PERF: bulk memory write (the byte-level WRITE path).
; 100 memsets of an 8 KiB buffer. write_bytes sequences its writes with
; loop_monad, so this scales linearly in the buffer size — but still pays
; the per-byte representation (one boxed MByte in an AVL map per byte,
; ~2-3 us/byte). The memcpy-chunk.ll / memset-chunk.ll pair isolates the
; read path: memcpy adds a value-collecting read of the same bytes and is
; quadratic in size, memset is the write-only floor.
;
; Tune: change the buffer size (array type, GEP index, memset length) or
; the loop bound. Result is the fill byte (7) read back from the last
; position.

declare void @llvm.memset.p0i8.i64(i8*, i8, i64, i1)

define i64 @main(i64 %argc, i8** %argv) {
entry:
  %a = alloca [8192 x i8]
  %pa = bitcast [8192 x i8]* %a to i8*
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %c = icmp eq i64 %i, 100
  br i1 %c, label %exit, label %body

body:
  call void @llvm.memset.p0i8.i64(i8* %pa, i8 7, i64 8192, i1 false)
  %i.next = add i64 %i, 1
  br label %header

exit:
  %last = getelementptr [8192 x i8], [8192 x i8]* %a, i64 0, i64 8191
  %v = load i8, i8* %last
  %r = zext i8 %v to i64
  ret i64 %r
}

; ASSERT EQ: i64 7 = call i64 @main(i64 0, i8** null)
