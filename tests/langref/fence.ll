; Examples from the LLVM LangRef's 'fence' Instruction section.
; langref: fence-instruction sha1=50786a88e560b449dfcf207137fa85a1ff44a0ee
;
; LangRef 24.0.0git gives the following example(s):
;
; fence acquire                                        ; yields void
; fence syncscope("singlethread") seq_cst              ; yields void
; fence syncscope("agent") seq_cst                     ; yields void

; NOT SUPPORTED by Vellvm: no concurrency / memory ordering
