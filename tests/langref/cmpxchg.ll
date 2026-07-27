; Examples from the LLVM LangRef's 'cmpxchg' Instruction section.
; langref: cmpxchg-instruction sha1=d94a4552e59c57b8d0b46d750f0ffb530d47e9ea
;
; LangRef 24.0.0git gives the following example(s):
;
; entry:
;   %orig = load atomic i32, ptr %ptr unordered, align 4                      ; yields i32
;   br label %loop
;
; loop:
;   %cmp = phi i32 [ %orig, %entry ], [%value_loaded, %loop]
;   %squared = mul i32 %cmp, %cmp
;   %val_success = cmpxchg ptr %ptr, i32 %cmp, i32 %squared acq_rel monotonic ; yields  { i32, i1 }
;   %value_loaded = extractvalue { i32, i1 } %val_success, 0
;   %success = extractvalue { i32, i1 } %val_success, 1
;   br i1 %success, label %done, label %loop
;
; done:
;   ...

; NOT SUPPORTED by Vellvm: no concurrency / memory ordering
