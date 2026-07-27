; Examples from the LLVM LangRef's 'invoke' Instruction section.
; langref: invoke-instruction sha1=97476542c9fd5677c9ab973f5f19cb6dcea79606
;
; LangRef 24.0.0git gives the following example(s):
;
; %retval = invoke i32 @Test(i32 15) to label %Continue
;             unwind label %TestCleanup              ; i32:retval set
; %retval = invoke coldcc i32 %Testfnptr(i32 15) to label %Continue
;             unwind label %TestCleanup              ; i32:retval set

; NOT SUPPORTED by Vellvm: exception handling not modelled
