; PERF: serialization of structured values.
; Each iteration builds a mixed struct (with padding-relevant fields:
; i64/i32/i8 and a nested array) via an insertvalue chain, stores the
; whole aggregate, loads it back, and extracts fields. Stresses
; serialize_sbytes / deserialization on non-scalar dvalues, struct
; offset computation, and insertvalue/extractvalue.
;
; Tune: %n in @main.
; Per iteration the accumulator gains i + i + i + 2*i = 5*i,
; so the result is 5*n*(n-1)/2.

%pack = type { i64, i32, [4 x i64], i8 }

define i64 @churn(i64 %n) {
entry:
  %slot = alloca %pack
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %c = icmp slt i64 %i, %n
  br i1 %c, label %body, label %exit

body:
  %i32v = trunc i64 %i to i32
  %twice = add i64 %i, %i
  %v0 = insertvalue %pack zeroinitializer, i64 %i, 0
  %v1 = insertvalue %pack %v0, i32 %i32v, 1
  %v2 = insertvalue %pack %v1, i64 %i, 2, 1
  %v3 = insertvalue %pack %v2, i64 %twice, 2, 3
  %v4 = insertvalue %pack %v3, i8 7, 3
  store %pack %v4, %pack* %slot
  %r = load %pack, %pack* %slot
  %f0 = extractvalue %pack %r, 0
  %f1 = extractvalue %pack %r, 1
  %f1w = zext i32 %f1 to i64
  %f21 = extractvalue %pack %r, 2, 1
  %f23 = extractvalue %pack %r, 2, 3
  %s0 = add i64 %f0, %f1w
  %s1 = add i64 %f21, %f23
  %s = add i64 %s0, %s1
  %acc.next = add i64 %acc, %s
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @churn(i64 5000)
  ret i64 %r
}

; ASSERT EQ: i64 62487500 = call i64 @main(i64 0, i8** null)
