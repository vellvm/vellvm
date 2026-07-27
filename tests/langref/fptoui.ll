; Examples from the LLVM LangRef's 'fptoui .. to' Instruction section.
; langref: fptoui-to-instruction sha1=6c890b80b8339f778354919814485611b9018f71
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = fptoui double 123.0 to i32      ; yields i32:123
; %Y = fptoui float 1.0E+300 to i1     ; yields undefined:1
; %Z = fptoui float 1.04E+17 to i8     ; yields undefined:1

define i32 @fptoui_123() {
  %X = fptoui double 123.0 to i32
  ret i32 %X
}

; ASSERT EQ: i32 123 = call i32 @fptoui_123()
