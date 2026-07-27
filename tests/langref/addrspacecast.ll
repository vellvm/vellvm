; Examples from the LLVM LangRef's 'addrspacecast .. to' Instruction section.
; langref: addrspacecast-to-instruction sha1=f3ed88d0a65c8874a6624fa99e559056ba415f40
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = addrspacecast ptr %x to ptr addrspace(1)
; %Y = addrspacecast ptr addrspace(1) %y to ptr addrspace(2)
; %Z = addrspacecast <4 x ptr> %z to <4 x ptr addrspace(3)>

; NOT SUPPORTED by Vellvm: single address space only
