; Minimal illustration of LLVM IR exception handling (Itanium/Linux model),
; the subset needed to compile Rust's `panic = unwind`.
;
;   invoke      - call a function that may unwind; two successors
;   landingpad  - unwind target; binds the in-flight exception payload
;   resume      - re-raise the payload to keep unwinding up the stack
;
; This exercises a two-frame unwind:
;   - @do_panic raises (via the vellvm internal throw intrinsic)
;   - @with_cleanup catches it in a `cleanup` landingpad, then `resume`s
;     (mirrors a Rust frame running drop glue, then re-raising)
;   - @run catches it in a catch-all landingpad and stops the unwind
;     (mirrors a `catch_unwind` boundary)
;
; NOTE: not yet runnable — depends on exception semantics that are still TODO.
; Kept here so the unwind path is exercised once that support lands.

declare void @llvm.vellvm.internal.throw()

define i64 @personality(i32 %ver, i32 %act, i64 %cls, i8* %exc, i8* %ctx) {
  ret i64 0
}

; leaf frame: actually raises
define void @do_panic() {
  call void @llvm.vellvm.internal.throw()
  ret void
}

; middle frame: cleanup landingpad, then re-raise (keeps unwinding)
define void @with_cleanup()
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
  invoke void @do_panic() to label %ok unwind label %cleanup
ok:
  ret void
cleanup:
  %lp = landingpad { ptr, i64 } cleanup
  resume { ptr, i64 } %lp
}

; outer frame: catch-all landingpad, stops the unwind
define i64 @run()
    personality i64 (i32, i32, i64, i8*, i8*)* @personality {
  invoke void @with_cleanup() to label %normal unwind label %caught
normal:
  ret i64 0
caught:
  %lp = landingpad { ptr, i64 } catch ptr null
  ret i64 42
}

; ASSERT EQ: i64 42 = call i64 @run()
