; PERF: wide-integer (i128) arithmetic throughput.
; The same tight loop shape as loop-phi-arith.ll, but every value is an
; i128 kept genuinely wider than 64 bits (the shift pushes work into the
; high limb) and each iteration includes a full-width multiplication.
; With width-indexed integers this stresses the per-width machinery
; (modulus / natwordsize recomputation, Z normalization on multi-limb
; values) that the 64-bit tests never exercise.
;
; Tune: %n in @main. Per iteration acc += (i << 64) + i*i, so the
; result is S1*2^64 + S2 with S1 = n*(n-1)/2 and S2 = n*(n-1)*(2n-1)/6
; (no overflow for n up to ~10^9).

define i128 @wide(i128 %n) {
entry:
  br label %header

header:
  %i = phi i128 [ 0, %entry ], [ %i.next, %body ]
  %acc = phi i128 [ 0, %entry ], [ %acc.next, %body ]
  %cond = icmp slt i128 %i, %n
  br i1 %cond, label %body, label %exit

body:
  %hi = shl i128 %i, 64
  %sq = mul i128 %i, %i
  %step = add i128 %hi, %sq
  %acc.next = add i128 %acc, %step
  %i.next = add i128 %i, 1
  br label %header

exit:
  ret i128 %acc
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i128 @wide(i128 20000)
  %lo = trunc i128 %r to i64
  ret i64 %lo
}

; ASSERT EQ: i128 3689164347301175894150510000 = call i128 @wide(i128 20000)
; ASSERT EQ: i64 2666466670000 = call i64 @main(i64 0, i8** null)
