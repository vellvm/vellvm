; Examples from the LLVM LangRef's 'phi' Instruction section.
; langref: phi-instruction sha1=19eb220c1d218ec3837796ad71e64f7328f5f771
;
; LangRef 24.0.0git gives the following example(s):
;
; Loop:       ; Infinite loop that counts from 0 on up...
;   %indvar = phi i32 [ 0, %LoopHeader ], [ %nextindvar, %Loop ]
;   %nextindvar = add i32 %indvar, 1
;   br label %Loop

; LangRef's example is an infinite counting loop, so it cannot be asserted on
; directly. This keeps its shape -- an induction variable whose incoming value
; is 0 from the header and %nextindvar from the latch -- but exits at %n.
define i32 @count_to(i32 %n) {
LoopHeader:
  br label %Loop
Loop:
  %indvar = phi i32 [ 0, %LoopHeader ], [ %nextindvar, %Loop ]
  %nextindvar = add i32 %indvar, 1
  %done = icmp eq i32 %nextindvar, %n
  br i1 %done, label %Exit, label %Loop
Exit:
  ret i32 %nextindvar
}

; ASSERT EQ: i32 1 = call i32 @count_to(i32 1)
; ASSERT EQ: i32 10 = call i32 @count_to(i32 10)
