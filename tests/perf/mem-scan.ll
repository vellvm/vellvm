; PERF: memory read/write throughput on scalars.
; Allocates an i64 array, fills it with GEP+store, then sums it with
; GEP+load. Each store serializes a dvalue to bytes and each load
; deserializes, so this measures the byte-level memory model
; (serialize_sbytes / read_bytes) plus GEP handling, against a fixed
; small amount of arithmetic.
;
; Tune: %n in @main and the array type must agree.
; Result is sum 0..(n-1) = n*(n-1)/2.

define i64 @scan(i64 %n) {
entry:
  %buf = alloca [16384 x i64]
  br label %fill

fill:
  %i = phi i64 [ 0, %entry ], [ %i.next, %fill.body ]
  %c = icmp slt i64 %i, %n
  br i1 %c, label %fill.body, label %sum.pre

fill.body:
  %p = getelementptr [16384 x i64], [16384 x i64]* %buf, i64 0, i64 %i
  store i64 %i, i64* %p
  %i.next = add i64 %i, 1
  br label %fill

sum.pre:
  br label %sum

sum:
  %j = phi i64 [ 0, %sum.pre ], [ %j.next, %sum.body ]
  %acc = phi i64 [ 0, %sum.pre ], [ %acc.next, %sum.body ]
  %c2 = icmp slt i64 %j, %n
  br i1 %c2, label %sum.body, label %exit

sum.body:
  %q = getelementptr [16384 x i64], [16384 x i64]* %buf, i64 0, i64 %j
  %v = load i64, i64* %q
  %acc.next = add i64 %acc, %v
  %j.next = add i64 %j, 1
  br label %sum

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @scan(i64 16384)
  ret i64 %r
}

; ASSERT EQ: i64 134209536 = call i64 @main(i64 0, i8** null)
