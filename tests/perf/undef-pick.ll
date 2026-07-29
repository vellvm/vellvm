; PERF: uvalue manipulation and concretization.
; Each iteration builds a value that stays symbolic (undef combined
; with arithmetic and select), stores it (forcing serialization of
; symbolic bytes), reloads it, and branches on a comparison against it
; (forcing a Pick / concretization). Stresses the uvalue side of the
; semantics: symbolic byte serialization and the concretization
; pipeline, which the fully-defined tests never touch.
;
; Tune: %n in @main. `and undef, 0` concretizes to 0, so the selected
; value is always %i and the result is sum 0..(n-1) = n*(n-1)/2.

define i64 @churn(i64 %n) {
entry:
  %slot = alloca i64
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %c = icmp slt i64 %i, %n
  br i1 %c, label %body, label %exit

body:
  %masked = and i64 undef, 0
  store i64 %masked, i64* %slot
  %back = load i64, i64* %slot
  %iszero = icmp eq i64 %back, 0
  %v = select i1 %iszero, i64 %i, i64 0
  %acc.next = add i64 %acc, %v
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @churn(i64 20000)
  ret i64 %r
}

; ASSERT EQ: i64 199990000 = call i64 @main(i64 0, i8** null)
