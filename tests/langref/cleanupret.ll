; Examples from the LLVM LangRef's 'cleanupret' Instruction section.
; langref: cleanupret-instruction sha1=65ff51f408eab7b58a2c98bd08bd2690605e43fd
;
; LangRef 24.0.0git gives the following example(s):
;
; cleanupret from %cleanup unwind to caller
; cleanupret from %cleanup unwind label %continue

; NOT SUPPORTED by Vellvm: exception handling not modelled
