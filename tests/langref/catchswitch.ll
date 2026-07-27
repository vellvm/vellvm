; Examples from the LLVM LangRef's 'catchswitch' Instruction section.
; langref: catchswitch-instruction sha1=f6fd8077e0752b5226c5bbf15864a8850de725df
;
; LangRef 24.0.0git gives the following example(s):
;
; dispatch1:
;   %cs1 = catchswitch within none [label %handler0, label %handler1] unwind to caller
; dispatch2:
;   %cs2 = catchswitch within %parenthandler [label %handler0] unwind label %cleanup

; NOT SUPPORTED by Vellvm: exception handling not modelled
