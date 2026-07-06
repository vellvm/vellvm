; A landingpad must only be reached via the unwind edge of an invoke, which
; always parks a fresh payload in the frame (StackRaise). This program breaks
; that rule: after catching in %pad1, it branches *normally* into a second
; landingpad block. (The LLVM verifier rejects this IR; our parser does not,
; so the semantics must catch it at runtime.)
;
; The expected behavior is the defensive error "landingpad reached with no
; in-flight exception". If the frame's payload slot is not cleared when a
; landingpad consumes it, the stale payload from %pad1 masks the error and
; @run silently returns 1.

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %ver, i32 %act, i64 %cls, i8* %exc, i8* %ctx) {
  ret i64 0
}

define void @do_panic() {
  call void @llvm.vellvm.internal.throw()
  ret void
}

define i64 @run()
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
  invoke void @do_panic() to label %ok unwind label %pad1
ok:
  ret i64 0
pad1:
  %lp1 = landingpad { ptr, i64 } catch ptr null
  br label %pad2                                  ; invalid: normal edge into a landingpad block
pad2:
  %lp2 = landingpad { ptr, i64 } catch ptr null   ; no in-flight exception here
  ret i64 1
}

; ASSERT FAILS: call i64 @run()
