; Examples from the LLVM LangRef's 'indirectbr' Instruction section.
; langref: indirectbr-instruction sha1=9ad404ddbbfc5a47c16cbd464f19165ec6c6d2ea
;
; LangRef 24.0.0git gives the following example(s):
;
; indirectbr ptr %Addr, [ label %bb1, label %bb2, label %bb3 ]

; NOT SUPPORTED by Vellvm: no indirect branch
