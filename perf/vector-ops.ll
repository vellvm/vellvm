; PERF: vector element access.
; A loop-carried <64 x i64> vector with one insertelement + one
; extractelement per iteration. Vectors are lists of dvalues, so lane
; access is a linear splice/walk and the whole vector is rebuilt on every
; insert; per-iteration cost grows with the vector width. (shufflevector
; is unimplemented in the semantics and cannot be tested yet.)
;
; Tune: change the loop bound, or the vector width (type + the urem
; modulus). Result is sum 0..(K-1) = K*(K-1)/2.

define i64 @main(i64 %argc, i8** %argv) {
entry:
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %acc.next, %body ]
  %v = phi <64 x i64> [ zeroinitializer, %entry ], [ %v.next, %body ]
  %c = icmp eq i64 %i, 20000
  br i1 %c, label %exit, label %body

body:
  %lane = urem i64 %i, 64
  %v.next = insertelement <64 x i64> %v, i64 %i, i64 %lane
  %x = extractelement <64 x i64> %v.next, i64 %lane
  %acc.next = add i64 %acc, %x
  %i.next = add i64 %i, 1
  br label %header

exit:
  ret i64 %acc
}

; ASSERT EQ: i64 199990000 = call i64 @main(i64 0, i8** null)
