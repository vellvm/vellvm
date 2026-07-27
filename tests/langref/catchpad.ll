; Examples from the LLVM LangRef's 'catchpad' Instruction section.
; langref: catchpad-instruction sha1=feb9efbba14ef8664285ad72e0e8a9307f4fc60d
;
; LangRef 24.0.0git gives the following example(s):
;
; dispatch:
;   %cs = catchswitch within none [label %handler0] unwind to caller
;   ;; A catch block which can catch an integer.
; handler0:
;   %tok = catchpad within %cs [ptr @_ZTIi]

; NOT SUPPORTED by Vellvm: exception handling not modelled
