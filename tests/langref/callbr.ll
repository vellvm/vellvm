; Examples from the LLVM LangRef's 'callbr' Instruction section.
; langref: callbr-instruction sha1=7fbb759a358e1da543c7c3ed5eecbed5f6e83871
;
; LangRef 24.0.0git gives the following example(s):
;
; ; "asm goto" without output constraints.
; callbr void asm "", "r,!i"(i32 %x)
;             to label %fallthrough [label %indirect]
;
; ; "asm goto" with output constraints.
; <result> = callbr i32 asm "", "=r,r,!i"(i32 %x)
;             to label %fallthrough [label %indirect]
;
; ; intrinsic which should be followed by unreachable (the order of the
; ; blocks after the callbr instruction doesn't matter)
;   callbr void @llvm.amdgcn.kill(i1 %c) to label %cont [label %kill]
; cont:
;   ...
; kill:
;   unreachable

; NOT SUPPORTED by Vellvm: inline asm / asm goto not modelled
