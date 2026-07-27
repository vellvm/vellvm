; Examples from the LLVM LangRef's 'fpext .. to' Instruction section.
; langref: fpext-to-instruction sha1=44d6b9fc3bcb8cd0ee986fecced84a9f41d5cefd
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = fpext float 3.125 to double         ; yields double:3.125000e+00
; %Y = fpext double %X to fp128            ; yields fp128:0xL00000000000000004000900000000000

define double @fpext_3125() {
  %X = fpext float 3.125 to double
  ret double %X
}

; ASSERT EQ: double 3.125 = call double @fpext_3125()
