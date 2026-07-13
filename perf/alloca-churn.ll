; PERF: allocation machinery.
; Performs one alloca per loop iteration (plus a store/load pair to
; make it observable), so the function's frame keeps growing. Stresses
; fresh-address generation, provenance allocation, and the frame-stack
; bookkeeping of the memory model, and shows whether costs degrade as
; the number of live allocations grows.
;
; Tune: %n in @main. Result is sum 0..(n-1) = n*(n-1)/2.

define i64 @churn(i64 %n) {
entry:
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %c = icmp slt i64 %i, %n
  br i1 %c, label %body, label %exit

body:
  %cell = alloca i64
  store i64 %i, i64* %cell
  %v = load i64, i64* %cell
  %acc.next = add i64 %acc, %v
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @churn(i64 10000)
  ret i64 %r
}

; ASSERT EQ: i64 49995000 = call i64 @main(i64 0, i8** null)
