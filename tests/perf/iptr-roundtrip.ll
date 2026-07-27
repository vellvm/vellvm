; PERF: integer/pointer cast machinery.
; Each iteration does a ptrtoint / arithmetic / inttoptr round trip and
; a load through the recovered pointer. Stresses the ITOP/PTOI handlers
; and the provenance side of the memory model, which are entirely
; skipped by the other memory tests.
;
; Tune: %n in @main. Result is n * (10 + 20) = 30 * n.

define i64 @roundtrip(i64 %n) {
entry:
  %buf = alloca [2 x i64]
  %p0 = getelementptr [2 x i64], [2 x i64]* %buf, i64 0, i64 0
  %p1 = getelementptr [2 x i64], [2 x i64]* %buf, i64 0, i64 1
  store i64 10, i64* %p0
  store i64 20, i64* %p1
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %c = icmp slt i64 %i, %n
  br i1 %c, label %body, label %exit

body:
  %base = ptrtoint i64* %p0 to iptr
  %off = add iptr %base, 8
  %q1 = inttoptr iptr %off to i64*
  %q0 = inttoptr iptr %base to i64*
  %v0 = load i64, i64* %q0
  %v1 = load i64, i64* %q1
  %s = add i64 %v0, %v1
  %acc.next = add i64 %acc, %s
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @roundtrip(i64 20000)
  ret i64 %r
}

; ASSERT EQ: i64 600000 = call i64 @main(i64 0, i8** null)
