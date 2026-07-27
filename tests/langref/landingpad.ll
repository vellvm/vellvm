; Examples from the LLVM LangRef's 'landingpad' Instruction section.
; langref: landingpad-instruction sha1=9ab42167a0e490cc64a48d1272d911a611a04626
;
; LangRef 24.0.0git gives the following example(s):
;
; ;; A landing pad which can catch an integer.
; %res = landingpad { ptr, i32 }
;          catch ptr @_ZTIi
; ;; A landing pad that is a cleanup.
; %res = landingpad { ptr, i32 }
;          cleanup
; ;; A landing pad which can catch an integer and can only throw a double.
; %res = landingpad { ptr, i32 }
;          catch ptr @_ZTIi
;          filter [1 x ptr] [ptr @_ZTId]

; NOT SUPPORTED by Vellvm: exception handling not modelled
