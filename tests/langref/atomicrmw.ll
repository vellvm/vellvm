; Examples from the LLVM LangRef's 'atomicrmw' Instruction section.
; langref: atomicrmw-instruction sha1=9b341f928ffff2d20f080e0b895cd51121b9de9a
;
; LangRef 24.0.0git gives the following example(s):
;
; %old = atomicrmw add ptr %ptr, i32 1 acquire                        ; yields i32

; NOT SUPPORTED by Vellvm: no concurrency / memory ordering
