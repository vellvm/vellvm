; PERF: baseline control-flow + arithmetic throughput.
; A tight counted loop with two phi nodes and pure i64 arithmetic.
; Measures the per-iteration cost of block denotation, branching,
; phi resolution, and local-environment reads/writes, with no memory
; events at all.
;
; Tune: change %n in @main. Result is sum 0..(n-1) = n*(n-1)/2.

define i64 @loop(i64 %n) {
entry:
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %cond = icmp slt i64 %i, %n
  br i1 %cond, label %body, label %exit

body:
  %acc.next = add i64 %acc, %i
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @loop(i64 100000)
  ret i64 %r
}

; ASSERT EQ: i64 4999950000 = call i64 @main(i64 0, i8** null)
