; PERF: per-bit freeze of a partly poisoned byte value.
; A wide byte value (b512) with only its low byte defined --- 8 integer
; bits, 504 poison bits --- is loaded once, then frozen on every
; iteration of a tight counted loop.  Freezing a [BYTE_Mixed] draws one
; integer of the byte's width and replaces each poison bit with the
; corresponding bit of it ([freeze_mixed_bits]), so the cost of a freeze
; is one [Draw] plus a pass over the bits.  (A variant with one
; [DrawBool] event per poison bit, kept on the freeze-drawbool branch,
; was ~3-4x slower here, and quadratic in the poison-bit count until its
; bit loop used [map_monad_acc].)
;
; The input is never itself frozen (each iteration freezes %b, not the
; previous result, which would have no poison left), and the result is
; only bitcast once, after the loop, so the loop body is the freeze plus
; the [loop-phi-arith.ll] overhead.  Only the defined low byte is
; observed, so the result is deterministic.
;
; Tune: change %n in @main, or the width (b512/i512, keeping one defined
; byte). Result is the defined low byte, 7.

define i64 @loop(i64 %n) {
entry:
  %p = alloca b512
  store i8 7, ptr %p
  %b = load b512, ptr %p
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %last = phi b512 [ %b, %entry ], [ %f, %body ]
  %cond = icmp slt i64 %i, %n
  br i1 %cond, label %body, label %exit

body:
  %f = freeze b512 %b
  %i.next = add i64 %i, 1
  br label %header

exit:
  %v = bitcast b512 %last to i512
  %lo = trunc i512 %v to i8
  %r = zext i8 %lo to i64
  ret i64 %r
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @loop(i64 20000)
  ret i64 %r
}

; ASSERT EQ: i64 7 = call i64 @main(i64 0, i8** null)
