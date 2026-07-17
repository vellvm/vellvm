; PERF: large-object stack allocation and frame teardown.
; 200 calls to a function that allocas a 4 KiB buffer: allocation writes
; one undef byte per address into the memory map AND registers every
; byte's pointer in the frame; returning frees them back out one AVL
; delete at a time. ~13 ms per call at 4 KiB — all of it per-byte
; bookkeeping. Complements alloca-churn.ll (many tiny allocas, frames
; never popped until the end): this one stresses object size and the
; push/pop cycle.
;
; Tune: change the buffer size (array type) or the call count. Result is
; the call count (each call returns 1).

define i64 @frame() {
entry:
  %buf = alloca [4096 x i8]
  %p = getelementptr [4096 x i8], [4096 x i8]* %buf, i64 0, i64 0
  store i8 7, i8* %p
  ret i64 1
}

define i64 @main(i64 %argc, i8** %argv) {
entry:
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %c = icmp eq i64 %i, 200
  br i1 %c, label %exit, label %body

body:
  %r = call i64 @frame()
  %acc.next = add i64 %acc, %r
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

; ASSERT EQ: i64 200 = call i64 @main(i64 0, i8** null)
